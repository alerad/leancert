/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.API.Eval

/-!
# Checked backend-native evaluation

These APIs are for clients that need a backend's native result type. They keep
the same checked failure behavior and box semantics as `LeanCert.evalInterval`.
Ordinary clients should prefer the backend-independent public façade.
-/

namespace LeanCert.Backend

open LeanCert
open LeanCert.Core
open LeanCert.Engine
open LeanCert.Engine.Affine

namespace Rational

/-- Evaluate with the checked rational backend and retain its native interval. -/
def eval (e : Expr) (box : List IntervalRat) : EvalResult IntervalRat :=
  evalIntervalChecked e (intervalEnvOfList box)

/-- Successful native rational evaluation encloses every point of the box. -/
theorem eval_correct {e : Expr} {box : List IntervalRat} {result : IntervalRat}
    (hsuccess : eval e box = .ok result) {rho : Nat → ℝ}
    (hrho : BoxEnvMem rho box) : Expr.eval rho e ∈ result := by
  exact evalIntervalChecked_correct e (intervalEnvOfList box) result hsuccess rho hrho

end Rational

namespace Dyadic

/-- Evaluate with the checked dyadic backend and retain its native interval. -/
def eval (e : Expr) (box : List IntervalRat)
    (precision : PrecisionOptions := {}) : EvalResult IntervalDyadic :=
  if precision.dyadicExponent > 0 then
    .error (.invalidConfiguration
      "dyadicExponent must be nonpositive for certified outward rounding")
  else
    let cfg : DyadicConfig := {
      precision := precision.dyadicExponent
      taylorDepth := precision.taylorDepth
    }
    evalIntervalDyadicChecked e
      (toDyadicEnv (intervalEnvOfList box) precision.dyadicExponent) cfg

/-- Successful native dyadic evaluation encloses every point of the box. -/
theorem eval_correct {e : Expr} {box : List IntervalRat}
    {precision : PrecisionOptions} {result : IntervalDyadic}
    (hsuccess : eval e box precision = .ok result) {rho : Nat → ℝ}
    (hrho : BoxEnvMem rho box) : Expr.eval rho e ∈ result := by
  have hprec : precision.dyadicExponent ≤ 0 := by
    by_contra h
    have hpos : precision.dyadicExponent > 0 := lt_of_not_ge h
    simp [eval, hpos] at hsuccess
  let cfg : DyadicConfig := {
    precision := precision.dyadicExponent
    taylorDepth := precision.taylorDepth
  }
  let rhoDyadic := toDyadicEnv (intervalEnvOfList box) precision.dyadicExponent
  have hrhoDyadic : envMemDyadic rho rhoDyadic := by
    intro i
    exact IntervalDyadic.mem_ofIntervalRat (hrho i) precision.dyadicExponent hprec
  apply evalIntervalDyadicChecked_correct e rho rhoDyadic hrhoDyadic cfg hprec result
  simpa [eval, cfg, rhoDyadic, show ¬precision.dyadicExponent > 0 from not_lt.mpr hprec]
    using hsuccess

end Dyadic

namespace Affine

/-- Evaluate with the checked affine backend and retain its native form. -/
def eval (e : Expr) (box : List IntervalRat)
    (precision : PrecisionOptions := {}) : EvalResult AffineForm :=
  let cfg : AffineConfig := {
    taylorDepth := precision.taylorDepth
    maxNoiseSymbols := precision.maxNoiseSymbols
  }
  evalIntervalAffineChecked e (toAffineEnv box) cfg

/-- Successful native affine evaluation encloses every point of the box after
conversion to an ordinary rational interval. -/
theorem eval_correct {e : Expr} {box : List IntervalRat}
    {precision : PrecisionOptions} {result : AffineForm}
    (hsuccess : eval e box precision = .ok result) {rho : Nat → ℝ}
    (hrho : BoxEnvMem rho box) : Expr.eval rho e ∈ result.toInterval := by
  obtain ⟨eps, hvalid, henv⟩ := exists_noise_toAffineEnv box rho
    (fun i hi => hrho.get i hi) (fun i hi => hrho.eq_zero i hi)
  let cfg : AffineConfig := {
    taylorDepth := precision.taylorDepth
    maxNoiseSymbols := precision.maxNoiseSymbols
  }
  have hnative := evalIntervalAffineChecked_correct e rho (toAffineEnv box) eps
    hvalid henv cfg result (by simpa [eval, cfg] using hsuccess)
  exact AffineForm.mem_toInterval_weak hvalid hnative

end Affine

end LeanCert.Backend
