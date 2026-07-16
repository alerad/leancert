/-
Copyright (c) 2025 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Core.Expr
import LeanCert.Engine.Affine.Transcendental
import LeanCert.Engine.IntervalEval

/-!
# Affine Arithmetic Expression Evaluator

This module provides expression evaluation using Affine Arithmetic (AA).
Affine arithmetic tracks correlations between variables, solving the
"dependency problem" that causes interval arithmetic to over-approximate.

## Main definitions

* `AffineConfig` - Configuration for affine evaluation
* `AffineEnv` - Variable environment mapping indices to affine forms
* `LeanCert.Internal.Affine.evalUnchecked` - Main evaluator: Expr → AffineForm
* `evalIntervalAffine?` - Strict evaluator rejecting unsupported/domain-invalid cases

## Performance

For expressions with repeated variables:
- Interval: `x - x` on [-1, 1] gives [-2, 2]
- Affine: `x - x` on [-1, 1] gives [0, 0] (exact!)

Affine arithmetic gives 50-90% tighter bounds for many real-world expressions,
especially in neural network verification where the same inputs flow through
multiple paths.

## Limitations

Some transcendental functions (sin, cos, atan) fall back to interval
arithmetic because affine approximations aren't yet implemented.
-/

namespace LeanCert.Engine

open LeanCert.Core Affine

/-! ### Configuration -/

/-- Configuration for Affine evaluation.

* `taylorDepth` - Number of Taylor terms for transcendental functions
* `maxNoiseSymbols` - Maximum noise symbols before consolidation (0 = unlimited)
-/
structure AffineConfig where
  /-- Number of Taylor series terms for transcendental functions -/
  taylorDepth : Nat := 10
  /-- Max noise symbols before consolidation (0 = no limit) -/
  maxNoiseSymbols : Nat := 0
  deriving Repr, DecidableEq

instance : Inhabited AffineConfig := ⟨{}⟩

/-! ### Variable Environment -/

/-- Variable assignment as Affine forms -/
abbrev AffineEnv := Nat → AffineForm

/-- Create an affine environment from rational intervals.

Each variable gets a unique noise symbol to track correlations. -/
def toAffineEnv (intervals : List IntervalRat) : AffineEnv :=
  let n := intervals.length
  fun i =>
    let I := intervals.getD i (IntervalRat.singleton 0)
    AffineForm.ofInterval I i n

/-! ### Main Evaluator -/

end LeanCert.Engine

namespace LeanCert.Internal.Affine

open LeanCert.Core LeanCert.Engine LeanCert.Engine.Affine

/-- Evaluate expression using Affine Arithmetic.

This function recursively evaluates an expression, using:
- Exact affine operations for linear functions (add, sub, neg, scale)
- Controlled approximations for nonlinear functions (mul, sq)
- Interval fallbacks for unsupported transcendentals (sin, cos, atan)

The result is an AffineForm that can be converted to an interval via
`toInterval`, typically giving tighter bounds than pure interval arithmetic. -/
def evalUnchecked (e : Expr) (ρ : AffineEnv) (cfg : AffineConfig := {}) : AffineForm :=
  match e with
  | Expr.const q => AffineForm.const q
  | Expr.var idx => ρ idx
  | Expr.add e₁ e₂ =>
      AffineForm.add (LeanCert.Internal.Affine.evalUnchecked e₁ ρ cfg) (LeanCert.Internal.Affine.evalUnchecked e₂ ρ cfg)
  | Expr.mul e₁ e₂ =>
      AffineForm.mul (LeanCert.Internal.Affine.evalUnchecked e₁ ρ cfg) (LeanCert.Internal.Affine.evalUnchecked e₂ ρ cfg)
  | Expr.neg e =>
      AffineForm.neg (LeanCert.Internal.Affine.evalUnchecked e ρ cfg)
  | Expr.inv e =>
      AffineForm.inv (LeanCert.Internal.Affine.evalUnchecked e ρ cfg)
  | Expr.exp e =>
      AffineForm.exp (LeanCert.Internal.Affine.evalUnchecked e ρ cfg) cfg.taylorDepth
  | Expr.sinh e =>
      AffineForm.sinh (LeanCert.Internal.Affine.evalUnchecked e ρ cfg) cfg.taylorDepth
  | Expr.cosh e =>
      AffineForm.cosh (LeanCert.Internal.Affine.evalUnchecked e ρ cfg) cfg.taylorDepth
  | Expr.tanh e =>
      AffineForm.tanh (LeanCert.Internal.Affine.evalUnchecked e ρ cfg)
  | Expr.sqrt e =>
      AffineForm.sqrt (LeanCert.Internal.Affine.evalUnchecked e ρ cfg)
  -- Fallback to interval for unsupported transcendentals
  | Expr.sin e =>
      let af := LeanCert.Internal.Affine.evalUnchecked e ρ cfg
      let I := af.toInterval
      let result := IntervalRat.sinComputable I cfg.taylorDepth
      let mid := (result.lo + result.hi) / 2
      let rad := (result.hi - result.lo) / 2
      { c0 := mid, coeffs := [], r := |rad|, r_nonneg := abs_nonneg _ }
  | Expr.cos e =>
      let af := LeanCert.Internal.Affine.evalUnchecked e ρ cfg
      let I := af.toInterval
      let result := IntervalRat.cosComputable I cfg.taylorDepth
      let mid := (result.lo + result.hi) / 2
      let rad := (result.hi - result.lo) / 2
      { c0 := mid, coeffs := [], r := |rad|, r_nonneg := abs_nonneg _ }
  | Expr.log e =>
      let af := LeanCert.Internal.Affine.evalUnchecked e ρ cfg
      let I := af.toInterval
      if h : 0 < I.lo then
        let result := IntervalRat.logComputable I cfg.taylorDepth
        let mid := (result.lo + result.hi) / 2
        let rad := (result.hi - result.lo) / 2
        { c0 := mid, coeffs := [], r := |rad|, r_nonneg := abs_nonneg _ }
      else
        -- Fallback for non-positive inputs
        { c0 := 0, coeffs := [], r := 10^30, r_nonneg := by norm_num }
  | Expr.atan e =>
      -- Global bound [-π/2, π/2] ≈ [-2, 2]
      let neg2 := (-2 : ℚ)
      let pos2 := (2 : ℚ)
      let mid := (neg2 + pos2) / 2
      let rad := (pos2 - neg2) / 2
      { c0 := mid, coeffs := [], r := rad, r_nonneg := by norm_num }
  | Expr.arsinh e =>
      AffineForm.ofIntervalFallback
        (arsinhInterval (LeanCert.Internal.Affine.evalUnchecked e ρ cfg).toInterval)
  | Expr.atanh e =>
      let a := LeanCert.Internal.Affine.evalUnchecked e ρ cfg
      let I := a.toInterval
      if -1 < I.lo ∧ I.hi < 1 then
        AffineForm.ofIntervalFallback (IntervalRat.atanhComputable I cfg.taylorDepth)
      else
        -- Legacy total API cannot express domain failure. Checked callers use
        -- `evalIntervalAffineChecked`, which rejects this case.
        default
  | Expr.sinc e =>
      -- sinc(x) = sin(x)/x, bounded in [-1, 1]
      { c0 := 0, coeffs := [], r := 1, r_nonneg := by norm_num }
  | Expr.erf e =>
      -- erf bounded in [-1, 1]
      { c0 := 0, coeffs := [], r := 1, r_nonneg := by norm_num }
  | Expr.namedConst c =>
      let I := c.interval
      let mid := (I.lo + I.hi) / 2
      let rad := (I.hi - I.lo) / 2
      { c0 := mid, coeffs := [], r := |rad|, r_nonneg := abs_nonneg _ }

end LeanCert.Internal.Affine

namespace LeanCert.Engine

open LeanCert.Core LeanCert.Engine.Affine

/-- Strict affine evaluator.

This variant returns `none` for operations that the legacy evaluator handles by
returning `default` or a huge fallback interval. All expression constructors are
implemented here; `none` means that a partial operation's domain could not be
proved for the supplied interval.
-/
def evalIntervalAffine? (e : Expr) (ρ : AffineEnv) (cfg : AffineConfig := {}) : Option AffineForm :=
  match e with
  | Expr.const q => some (AffineForm.const q)
  | Expr.var idx => some (ρ idx)
  | Expr.add e₁ e₂ =>
      match evalIntervalAffine? e₁ ρ cfg, evalIntervalAffine? e₂ ρ cfg with
      | some a₁, some a₂ => some (AffineForm.add a₁ a₂)
      | _, _ => none
  | Expr.mul e₁ e₂ =>
      match evalIntervalAffine? e₁ ρ cfg, evalIntervalAffine? e₂ ρ cfg with
      | some a₁, some a₂ => some (AffineForm.mul a₁ a₂)
      | _, _ => none
  | Expr.neg e =>
      match evalIntervalAffine? e ρ cfg with
      | some a => some (AffineForm.neg a)
      | none => none
  | Expr.inv e =>
      match evalIntervalAffine? e ρ cfg with
      | some a =>
          if a.toInterval.lo > 0 ∨ a.toInterval.hi < 0 then
            some (AffineForm.ofIntervalFallback (invInterval a.toInterval))
          else
            none
      | none => none
  | Expr.exp e =>
      match evalIntervalAffine? e ρ cfg with
      | some a => some (AffineForm.exp a cfg.taylorDepth)
      | none => none
  | Expr.sinh e =>
      match evalIntervalAffine? e ρ cfg with
      | some a => some (AffineForm.sinh a cfg.taylorDepth)
      | none => none
  | Expr.cosh e =>
      match evalIntervalAffine? e ρ cfg with
      | some a => some (AffineForm.cosh a cfg.taylorDepth)
      | none => none
  | Expr.tanh e =>
      match evalIntervalAffine? e ρ cfg with
      | some a => some (AffineForm.tanh a)
      | none => none
  | Expr.sqrt e =>
      match evalIntervalAffine? e ρ cfg with
      | some a => some (AffineForm.sqrt a)
      | none => none
  | Expr.sin e =>
      match evalIntervalAffine? e ρ cfg with
      | some a =>
          let I := a.toInterval
          let result := IntervalRat.sinComputable I cfg.taylorDepth
          let mid := (result.lo + result.hi) / 2
          let rad := (result.hi - result.lo) / 2
          some { c0 := mid, coeffs := [], r := |rad|, r_nonneg := abs_nonneg _ }
      | none => none
  | Expr.cos e =>
      match evalIntervalAffine? e ρ cfg with
      | some a =>
          let I := a.toInterval
          let result := IntervalRat.cosComputable I cfg.taylorDepth
          let mid := (result.lo + result.hi) / 2
          let rad := (result.hi - result.lo) / 2
          some { c0 := mid, coeffs := [], r := |rad|, r_nonneg := abs_nonneg _ }
      | none => none
  | Expr.log e =>
      match evalIntervalAffine? e ρ cfg with
      | some a =>
          let I := a.toInterval
          if h : 0 < I.lo then
            let result := IntervalRat.logComputable I cfg.taylorDepth
            let mid := (result.lo + result.hi) / 2
            let rad := (result.hi - result.lo) / 2
            some { c0 := mid, coeffs := [], r := |rad|, r_nonneg := abs_nonneg _ }
          else
            none
      | none => none
  | Expr.atan e =>
      match evalIntervalAffine? e ρ cfg with
      | some _ =>
          let neg2 := (-2 : ℚ)
          let pos2 := (2 : ℚ)
          let mid := (neg2 + pos2) / 2
          let rad := (pos2 - neg2) / 2
          some { c0 := mid, coeffs := [], r := rad, r_nonneg := by norm_num }
      | none => none
  | Expr.arsinh e =>
      match evalIntervalAffine? e ρ cfg with
      | some a =>
          some (AffineForm.ofIntervalFallback (arsinhInterval a.toInterval))
      | none => none
  | Expr.atanh e =>
      match evalIntervalAffine? e ρ cfg with
      | some a =>
          let I := a.toInterval
          if -1 < I.lo ∧ I.hi < 1 then
            some (AffineForm.ofIntervalFallback
              (IntervalRat.atanhComputable I cfg.taylorDepth))
          else
            none
      | none => none
  | Expr.sinc _ => some { c0 := 0, coeffs := [], r := 1, r_nonneg := by norm_num }
  | Expr.erf _ => some { c0 := 0, coeffs := [], r := 1, r_nonneg := by norm_num }
  | Expr.namedConst c =>
      let I := c.interval
      let mid := (I.lo + I.hi) / 2
      let rad := (I.hi - I.lo) / 2
      some { c0 := mid, coeffs := [], r := |rad|, r_nonneg := abs_nonneg _ }

/-- Diagnose the first strict affine evaluation failure. -/
def diagnoseEvalIntervalAffineFailure (e : Expr) (ρ : AffineEnv)
    (cfg : AffineConfig := {}) : EvalError :=
  match e with
  | .add e₁ e₂ | .mul e₁ e₂ =>
      if evalIntervalAffine? e₁ ρ cfg = none then
        .nestedFailure "left operand" (diagnoseEvalIntervalAffineFailure e₁ ρ cfg)
      else
        .nestedFailure "right operand" (diagnoseEvalIntervalAffineFailure e₂ ρ cfg)
  | .neg e | .exp e | .sin e | .cos e | .atan e | .arsinh e | .sinc e |
      .erf e | .sinh e | .cosh e | .tanh e | .sqrt e =>
      .nestedFailure "unary operand" (diagnoseEvalIntervalAffineFailure e ρ cfg)
  | .inv e =>
      match evalIntervalAffine? e ρ cfg with
      | some a => .reciprocalContainsZero a.toInterval
      | none => .nestedFailure "reciprocal operand"
          (diagnoseEvalIntervalAffineFailure e ρ cfg)
  | .log e =>
      match evalIntervalAffine? e ρ cfg with
      | some a => .logNonpositive a.toInterval
      | none => .nestedFailure "logarithm operand"
          (diagnoseEvalIntervalAffineFailure e ρ cfg)
  | .atanh e =>
      match evalIntervalAffine? e ρ cfg with
      | some a => .atanhOutsideUnitBall a.toInterval
      | none => .nestedFailure "atanh operand"
          (diagnoseEvalIntervalAffineFailure e ρ cfg)
  | .const _ | .var _ | .namedConst _ =>
      .unsupportedBackend "internal: total affine expression unexpectedly failed"
termination_by e

/-- Checked affine evaluator with structured domain errors. -/
def evalIntervalAffineChecked (e : Expr) (ρ : AffineEnv)
    (cfg : AffineConfig := {}) : EvalResult AffineForm :=
  match evalIntervalAffine? e ρ cfg with
  | some a => .ok a
  | none => .error (diagnoseEvalIntervalAffineFailure e ρ cfg)

/-- Strictly evaluate and convert to an interval. -/
def evalAffineToInterval? (e : Expr) (ρ : AffineEnv) (cfg : AffineConfig := {}) :
    Option IntervalRat :=
  match evalIntervalAffine? e ρ cfg with
  | some a => some a.toInterval
  | none => none

/-- Check if expression is bounded above -/
def checkUpperBoundAffine (e : Expr) (ρ : AffineEnv) (bound : ℚ) (cfg : AffineConfig := {}) : Bool :=
  let result := LeanCert.Internal.Affine.evalUnchecked e ρ cfg
  result.toInterval.hi ≤ bound

/-- Check if expression is bounded below -/
def checkLowerBoundAffine (e : Expr) (ρ : AffineEnv) (bound : ℚ) (cfg : AffineConfig := {}) : Bool :=
  let result := LeanCert.Internal.Affine.evalUnchecked e ρ cfg
  bound ≤ result.toInterval.lo

/-! ### Correctness Theorem -/

/-- Environment membership: real value is represented by the affine form -/
def envMemAffine (ρ_real : Nat → ℝ) (ρ_affine : AffineEnv) (eps : AffineForm.NoiseAssignment) : Prop :=
  ∀ i, AffineForm.mem_affine (ρ_affine i) eps (ρ_real i)

/-- A successful strict affine evaluation represents the true value.

Unlike the legacy total evaluator, success itself discharges every partial
domain condition. Operations without a dedicated affine linearization use the
proved interval fallback and therefore remain sound while losing correlation. -/
theorem evalIntervalAffine?_correct (e : Expr)
    (ρ_real : Nat → ℝ) (ρ_affine : AffineEnv) (eps : AffineForm.NoiseAssignment)
    (hvalid : AffineForm.validNoise eps)
    (hρ : envMemAffine ρ_real ρ_affine eps) (cfg : AffineConfig := {})
    (result : AffineForm) (hsuccess : evalIntervalAffine? e ρ_affine cfg = some result) :
    AffineForm.mem_affine result eps (Expr.eval ρ_real e) := by
  induction e generalizing result with
  | const q =>
      simp only [evalIntervalAffine?] at hsuccess
      cases hsuccess
      exact AffineForm.mem_const q eps
  | var idx =>
      simp only [evalIntervalAffine?] at hsuccess
      cases hsuccess
      exact hρ idx
  | add e₁ e₂ ih₁ ih₂ =>
      simp only [evalIntervalAffine?] at hsuccess
      cases h₁ : evalIntervalAffine? e₁ ρ_affine cfg with
      | none => simp only [h₁] at hsuccess; contradiction
      | some a₁ =>
        cases h₂ : evalIntervalAffine? e₂ ρ_affine cfg with
        | none => simp only [h₁, h₂] at hsuccess; contradiction
        | some a₂ =>
          simp only [h₁, h₂] at hsuccess
          cases hsuccess
          exact AffineForm.mem_add (ih₁ a₁ h₁) (ih₂ a₂ h₂)
  | mul e₁ e₂ ih₁ ih₂ =>
      simp only [evalIntervalAffine?] at hsuccess
      cases h₁ : evalIntervalAffine? e₁ ρ_affine cfg with
      | none => simp only [h₁] at hsuccess; contradiction
      | some a₁ =>
        cases h₂ : evalIntervalAffine? e₂ ρ_affine cfg with
        | none => simp only [h₁, h₂] at hsuccess; contradiction
        | some a₂ =>
          simp only [h₁, h₂] at hsuccess
          cases hsuccess
          exact AffineForm.mem_mul hvalid (ih₁ a₁ h₁) (ih₂ a₂ h₂)
  | neg e ih =>
      simp only [evalIntervalAffine?] at hsuccess
      cases h : evalIntervalAffine? e ρ_affine cfg with
      | none => simp only [h] at hsuccess; contradiction
      | some a =>
        simp only [h] at hsuccess
        cases hsuccess
        exact AffineForm.mem_neg (ih a h)
  | inv e ih =>
      simp only [evalIntervalAffine?] at hsuccess
      cases h : evalIntervalAffine? e ρ_affine cfg with
      | none => simp only [h] at hsuccess; contradiction
      | some a =>
        simp only [h] at hsuccess
        split at hsuccess
        · rename_i hnonzero
          cases hsuccess
          have hv := AffineForm.mem_toInterval_weak hvalid (ih a h)
          exact AffineForm.mem_ofIntervalFallback
            (mem_invInterval_nonzero hv hnonzero)
        · contradiction
  | exp e ih =>
      simp only [evalIntervalAffine?] at hsuccess
      cases h : evalIntervalAffine? e ρ_affine cfg with
      | none => simp only [h] at hsuccess; contradiction
      | some a =>
        simp only [h] at hsuccess
        cases hsuccess
        exact AffineForm.mem_exp hvalid (ih a h) cfg.taylorDepth
  | sin e ih =>
      simp only [evalIntervalAffine?] at hsuccess
      cases h : evalIntervalAffine? e ρ_affine cfg with
      | none => simp only [h] at hsuccess; contradiction
      | some a =>
        simp only [h] at hsuccess
        cases hsuccess
        have hv := AffineForm.mem_toInterval_weak hvalid (ih a h)
        exact AffineForm.mem_affine_of_interval
          (IntervalRat.mem_sinComputable hv cfg.taylorDepth)
  | cos e ih =>
      simp only [evalIntervalAffine?] at hsuccess
      cases h : evalIntervalAffine? e ρ_affine cfg with
      | none => simp only [h] at hsuccess; contradiction
      | some a =>
        simp only [h] at hsuccess
        cases hsuccess
        have hv := AffineForm.mem_toInterval_weak hvalid (ih a h)
        exact AffineForm.mem_affine_of_interval
          (IntervalRat.mem_cosComputable hv cfg.taylorDepth)
  | log e ih =>
      simp only [evalIntervalAffine?] at hsuccess
      cases h : evalIntervalAffine? e ρ_affine cfg with
      | none => simp only [h] at hsuccess; contradiction
      | some a =>
        simp only [h] at hsuccess
        split at hsuccess
        · rename_i hpos
          cases hsuccess
          have hv := AffineForm.mem_toInterval_weak hvalid (ih a h)
          exact AffineForm.mem_affine_of_interval
            (IntervalRat.mem_logComputable hv hpos cfg.taylorDepth)
        · contradiction
  | atan e ih =>
      simp only [evalIntervalAffine?] at hsuccess
      cases h : evalIntervalAffine? e ρ_affine cfg with
      | none => simp only [h] at hsuccess; contradiction
      | some a =>
        simp only [h] at hsuccess
        cases hsuccess
        have hv := AffineForm.mem_toInterval_weak hvalid (ih a h)
        simpa [atanInterval] using
          (AffineForm.mem_affine_of_interval (eps := eps) (mem_atanInterval hv))
  | arsinh e ih =>
      simp only [evalIntervalAffine?] at hsuccess
      cases h : evalIntervalAffine? e ρ_affine cfg with
      | none => simp only [h] at hsuccess; contradiction
      | some a =>
        simp only [h] at hsuccess
        cases hsuccess
        have hv := AffineForm.mem_toInterval_weak hvalid (ih a h)
        exact AffineForm.mem_ofIntervalFallback (mem_arsinhInterval hv)
  | atanh e ih =>
      simp only [evalIntervalAffine?] at hsuccess
      cases h : evalIntervalAffine? e ρ_affine cfg with
      | none => simp only [h] at hsuccess; contradiction
      | some a =>
        simp only [h] at hsuccess
        split at hsuccess
        · rename_i hunit
          cases hsuccess
          have hv := AffineForm.mem_toInterval_weak hvalid (ih a h)
          exact AffineForm.mem_ofIntervalFallback
            (IntervalRat.mem_atanhComputable hv hunit.1 hunit.2 cfg.taylorDepth)
        · contradiction
  | sinc e ih =>
      simp only [evalIntervalAffine?] at hsuccess
      cases hsuccess
      show AffineForm.mem_affine
        { c0 := 0, coeffs := [], r := 1, r_nonneg := _ } eps _
      unfold AffineForm.mem_affine AffineForm.evalLinear AffineForm.linearSum
      simp only [List.zipWith_nil_left, List.sum_nil, Rat.cast_zero, zero_add, Rat.cast_one]
      use Real.sinc (Expr.eval ρ_real e)
      exact ⟨(by simpa [abs_le] using Real.sinc_mem_Icc (Expr.eval ρ_real e)), rfl⟩
  | erf e ih =>
      simp only [evalIntervalAffine?] at hsuccess
      cases hsuccess
      show AffineForm.mem_affine
        { c0 := 0, coeffs := [], r := 1, r_nonneg := _ } eps _
      unfold AffineForm.mem_affine AffineForm.evalLinear AffineForm.linearSum
      simp only [List.zipWith_nil_left, List.sum_nil, Rat.cast_zero, zero_add, Rat.cast_one]
      use Real.erf (Expr.eval ρ_real e)
      exact ⟨(by simpa [abs_le] using Real.erf_mem_Icc (Expr.eval ρ_real e)), rfl⟩
  | sinh e ih =>
      simp only [evalIntervalAffine?] at hsuccess
      cases h : evalIntervalAffine? e ρ_affine cfg with
      | none => simp only [h] at hsuccess; contradiction
      | some a =>
        simp only [h] at hsuccess
        cases hsuccess
        exact AffineForm.mem_sinh hvalid (ih a h) cfg.taylorDepth
  | cosh e ih =>
      simp only [evalIntervalAffine?] at hsuccess
      cases h : evalIntervalAffine? e ρ_affine cfg with
      | none => simp only [h] at hsuccess; contradiction
      | some a =>
        simp only [h] at hsuccess
        cases hsuccess
        exact AffineForm.mem_cosh hvalid (ih a h) cfg.taylorDepth
  | tanh e ih =>
      simp only [evalIntervalAffine?] at hsuccess
      cases h : evalIntervalAffine? e ρ_affine cfg with
      | none => simp only [h] at hsuccess; contradiction
      | some a =>
        simp only [h] at hsuccess
        cases hsuccess
        exact AffineForm.mem_tanh hvalid (ih a h)
  | sqrt e ih =>
      simp only [evalIntervalAffine?] at hsuccess
      cases h : evalIntervalAffine? e ρ_affine cfg with
      | none => simp only [h] at hsuccess; contradiction
      | some a =>
        simp only [h] at hsuccess
        cases hsuccess
        exact AffineForm.mem_sqrt' hvalid (ih a h)
  | namedConst c =>
      simp only [evalIntervalAffine?] at hsuccess
      cases hsuccess
      exact AffineForm.mem_affine_of_interval c.mem_interval

/-- Successful checked affine evaluation is sound for every expression. -/
theorem evalIntervalAffineChecked_correct (e : Expr)
    (ρ_real : Nat → ℝ) (ρ_affine : AffineEnv) (eps : AffineForm.NoiseAssignment)
    (hvalid : AffineForm.validNoise eps)
    (hρ : envMemAffine ρ_real ρ_affine eps) (cfg : AffineConfig := {})
    (result : AffineForm) (hsuccess : evalIntervalAffineChecked e ρ_affine cfg = .ok result) :
    AffineForm.mem_affine result eps (Expr.eval ρ_real e) := by
  cases heval : evalIntervalAffine? e ρ_affine cfg with
  | none =>
    rw [evalIntervalAffineChecked, heval] at hsuccess
    contradiction
  | some a =>
    rw [evalIntervalAffineChecked, heval] at hsuccess
    injection hsuccess with ha
    subst result
    exact evalIntervalAffine?_correct e ρ_real ρ_affine eps hvalid hρ cfg a heval

/-- Domain validity for Affine evaluation.
    This is defined directly in terms of LeanCert.Internal.Affine.evalUnchecked to ensure compatibility.
    For log, we require the argument's toInterval to have positive lower bound. -/
def evalDomainValidAffine (e : Expr) (ρ : AffineEnv) (cfg : AffineConfig := {}) : Prop :=
  match e with
  | Expr.const _ => True
  | Expr.var _ => True
  | Expr.add e₁ e₂ => evalDomainValidAffine e₁ ρ cfg ∧ evalDomainValidAffine e₂ ρ cfg
  | Expr.mul e₁ e₂ => evalDomainValidAffine e₁ ρ cfg ∧ evalDomainValidAffine e₂ ρ cfg
  | Expr.neg e => evalDomainValidAffine e ρ cfg
  | Expr.inv e => evalDomainValidAffine e ρ cfg
  | Expr.exp e => evalDomainValidAffine e ρ cfg
  | Expr.sin e => evalDomainValidAffine e ρ cfg
  | Expr.cos e => evalDomainValidAffine e ρ cfg
  | Expr.log e => evalDomainValidAffine e ρ cfg ∧ (LeanCert.Internal.Affine.evalUnchecked e ρ cfg).toInterval.lo > 0
  | Expr.atan e => evalDomainValidAffine e ρ cfg
  | Expr.arsinh e => evalDomainValidAffine e ρ cfg
  | Expr.atanh e => evalDomainValidAffine e ρ cfg
  | Expr.sinc e => evalDomainValidAffine e ρ cfg
  | Expr.erf e => evalDomainValidAffine e ρ cfg
  | Expr.sinh e => evalDomainValidAffine e ρ cfg
  | Expr.cosh e => evalDomainValidAffine e ρ cfg
  | Expr.tanh e => evalDomainValidAffine e ρ cfg
  | Expr.sqrt e => evalDomainValidAffine e ρ cfg
  | Expr.namedConst _ => True

/-- Domain validity is trivially true for ADSupported expressions (which exclude log). -/
theorem evalDomainValidAffine_of_ExprSupported {e : Expr} (hsupp : ADSupported e)
    (ρ : AffineEnv) (cfg : AffineConfig := {}) : evalDomainValidAffine e ρ cfg := by
  induction hsupp with
  | const _ => trivial
  | var _ => trivial
  | add _ _ ih1 ih2 => exact ⟨ih1, ih2⟩
  | mul _ _ ih1 ih2 => exact ⟨ih1, ih2⟩
  | neg _ ih => exact ih
  | sin _ ih => exact ih
  | cos _ ih => exact ih
  | exp _ ih => exact ih

/-- Correctness theorem for Affine interval evaluation.

If all input variables are represented by their affine forms (via noise assignment eps),
then the real evaluation of the expression is represented by the affine result.

This proves soundness: the affine form always contains the true value.

Note: Requires valid noise assignment and domain validity for log.
Some transcendental cases (sin, cos, pi) use interval fallback and have
separate soundness via interval bounds. -/
theorem evalIntervalAffine_correct (e : Expr) (hsupp : ExprSupportedCore e)
    (ρ_real : Nat → ℝ) (ρ_affine : AffineEnv) (eps : AffineForm.NoiseAssignment)
    (hvalid : AffineForm.validNoise eps)
    (hρ : envMemAffine ρ_real ρ_affine eps) (cfg : AffineConfig := {})
    (hdom : evalDomainValidAffine e ρ_affine cfg) :
    AffineForm.mem_affine (LeanCert.Internal.Affine.evalUnchecked e ρ_affine cfg) eps (Expr.eval ρ_real e) := by
  induction hsupp with
  | const q =>
    simp only [Expr.eval_const, LeanCert.Internal.Affine.evalUnchecked]
    exact AffineForm.mem_const q eps
  | var idx =>
    simp only [Expr.eval_var, LeanCert.Internal.Affine.evalUnchecked]
    exact hρ idx
  | add _ _ ih₁ ih₂ =>
    simp only [evalDomainValidAffine] at hdom
    simp only [Expr.eval_add, LeanCert.Internal.Affine.evalUnchecked]
    exact AffineForm.mem_add (ih₁ hdom.1) (ih₂ hdom.2)
  | mul _ _ ih₁ ih₂ =>
    simp only [evalDomainValidAffine] at hdom
    simp only [Expr.eval_mul, LeanCert.Internal.Affine.evalUnchecked]
    exact AffineForm.mem_mul hvalid (ih₁ hdom.1) (ih₂ hdom.2)
  | neg _ ih =>
    simp only [evalDomainValidAffine] at hdom
    simp only [Expr.eval_neg, LeanCert.Internal.Affine.evalUnchecked]
    exact AffineForm.mem_neg (ih hdom)
  | exp _ ih =>
    simp only [evalDomainValidAffine] at hdom
    simp only [Expr.eval_exp, LeanCert.Internal.Affine.evalUnchecked]
    exact AffineForm.mem_exp hvalid (ih hdom) cfg.taylorDepth
  | tanh _ ih =>
    simp only [evalDomainValidAffine] at hdom
    simp only [Expr.eval_tanh, LeanCert.Internal.Affine.evalUnchecked]
    exact AffineForm.mem_tanh hvalid (ih hdom)
  | @erf arg _ ih =>
    simp only [evalDomainValidAffine] at hdom
    -- erf returns trivial affine form { c0 := 0, coeffs := [], r := 1 } representing [-1, 1]
    -- Just need to show Real.erf x ∈ [-1, 1]
    simp only [Expr.eval_erf, LeanCert.Internal.Affine.evalUnchecked]
    -- mem_affine requires: ∃ err, |err| ≤ r ∧ v = evalLinear af eps + err
    -- For { c0 := 0, coeffs := [], r := 1 }, evalLinear is just 0
    -- So we need: ∃ err, |err| ≤ 1 ∧ erf(x) = err
    -- Take err = erf(x), then need |erf(x)| ≤ 1
    show AffineForm.mem_affine { c0 := 0, coeffs := [], r := 1, r_nonneg := _ } eps _
    unfold AffineForm.mem_affine AffineForm.evalLinear AffineForm.linearSum
    simp only [List.zipWith_nil_left, List.sum_nil, Rat.cast_zero, zero_add, Rat.cast_one]
    use Real.erf (Expr.eval ρ_real arg)
    constructor
    · rw [abs_le]
      exact Real.erf_mem_Icc _
    · ring
  | sqrt _ ih =>
    simp only [evalDomainValidAffine] at hdom
    simp only [Expr.eval_sqrt, LeanCert.Internal.Affine.evalUnchecked]
    exact AffineForm.mem_sqrt' hvalid (ih hdom)
  | @sin arg _ ih =>
    simp only [evalDomainValidAffine] at hdom
    -- Interval fallback soundness
    set af := LeanCert.Internal.Affine.evalUnchecked arg ρ_affine cfg
    have hv_in_I : Expr.eval ρ_real arg ∈ af.toInterval :=
      AffineForm.mem_toInterval_weak hvalid (ih hdom)
    have hsin_in :=
      IntervalRat.mem_sinComputable hv_in_I cfg.taylorDepth
    simpa [Expr.eval_sin, LeanCert.Internal.Affine.evalUnchecked, af] using
      (AffineForm.mem_affine_of_interval (eps := eps) hsin_in)
  | @cos arg _ ih =>
    simp only [evalDomainValidAffine] at hdom
    set af := LeanCert.Internal.Affine.evalUnchecked arg ρ_affine cfg
    have hv_in_I : Expr.eval ρ_real arg ∈ af.toInterval :=
      AffineForm.mem_toInterval_weak hvalid (ih hdom)
    have hcos_in :=
      IntervalRat.mem_cosComputable hv_in_I cfg.taylorDepth
    simpa [Expr.eval_cos, LeanCert.Internal.Affine.evalUnchecked, af] using
      (AffineForm.mem_affine_of_interval (eps := eps) hcos_in)
  | sinh _ ih =>
    simp only [evalDomainValidAffine] at hdom
    simp only [Expr.eval_sinh, LeanCert.Internal.Affine.evalUnchecked]
    exact AffineForm.mem_sinh hvalid (ih hdom) cfg.taylorDepth
  | cosh _ ih =>
    simp only [evalDomainValidAffine] at hdom
    simp only [Expr.eval_cosh, LeanCert.Internal.Affine.evalUnchecked]
    exact AffineForm.mem_cosh hvalid (ih hdom) cfg.taylorDepth
  | @log arg _ ih =>
    simp only [evalDomainValidAffine] at hdom
    -- Interval fallback soundness for log
    have hmem_arg := ih hdom.1
    have hv_in_I : Expr.eval ρ_real arg ∈ (LeanCert.Internal.Affine.evalUnchecked arg ρ_affine cfg).toInterval :=
      AffineForm.mem_toInterval_weak hvalid hmem_arg
    -- hdom.2 gives us the positivity condition
    have hpos : (LeanCert.Internal.Affine.evalUnchecked arg ρ_affine cfg).toInterval.lo > 0 := hdom.2
    simp only [Expr.eval_log, LeanCert.Internal.Affine.evalUnchecked, hpos]
    have hlog_in := IntervalRat.mem_logComputable hv_in_I hpos cfg.taylorDepth
    exact AffineForm.mem_affine_of_interval (eps := eps) hlog_in
  | namedConst c =>
    simp only [Expr.eval_namedConst, LeanCert.Internal.Affine.evalUnchecked]
    simpa using (AffineForm.mem_affine_of_interval (eps := eps) c.mem_interval)

/-- Corollary: The interval produced by toInterval contains the true value.

This is the key result for optimization: if we compute an affine form and convert
to an interval, the interval is guaranteed to contain the true value. -/
theorem evalIntervalAffine_toInterval_correct (e : Expr) (hsupp : ExprSupportedCore e)
    (ρ_real : Nat → ℝ) (ρ_affine : AffineEnv) (eps : AffineForm.NoiseAssignment)
    (hvalid : AffineForm.validNoise eps)
    (hρ : envMemAffine ρ_real ρ_affine eps)
    (cfg : AffineConfig := {})
    (hlen : eps.length = (LeanCert.Internal.Affine.evalUnchecked e ρ_affine cfg).coeffs.length)
    (hdom : evalDomainValidAffine e ρ_affine cfg) :
    Expr.eval ρ_real e ∈ (LeanCert.Internal.Affine.evalUnchecked e ρ_affine cfg).toInterval := by
  have hmem := evalIntervalAffine_correct e hsupp ρ_real ρ_affine eps hvalid hρ cfg hdom
  exact AffineForm.mem_toInterval hvalid hlen hmem

end LeanCert.Engine
