/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.API.Eval
import LeanCert.Validity.Dyadic

/-!
# Public checked bound certificates

This module is the proof-facing companion to `LeanCert.API.Eval`.
The box checkers retain the enclosure and selected backend returned by
`evalInterval`, together with the Boolean comparison result. This gives
programmatic clients one-pass evaluation and structured domain failures.

The one-dimensional `checkUpperBound`, `checkLowerBound`, and `checkBounds`
functions remain explicitly Dyadic-backed Boolean certificates so reflective
tactics can close `check... = true` using their configured kernel/native
verification route. Domain and precision validity are included in those
certificates, so their Golden Theorems require no separate support or domain
premise.
-/

namespace LeanCert.API.Bounds

open LeanCert Core

/-- A retained one-pass bound-check result. The enclosure and selected backend
are exactly those used to compute `verified`; clients never need to rerun the
evaluator to report them. -/
structure BoundCheckOutcome where
  interval : IntervalRat
  backend : ConcreteBackend
  verified : Bool
  deriving Repr, DecidableEq

/-- Check an upper bound over a box using the public checked evaluator. -/
def checkUpperBoundBox (e : Expr) (box : List IntervalRat) (bound : ℚ)
    (options : EvalOptions := {}) : EvalResult BoundCheckOutcome :=
  match evalInterval e box options with
  | .error err => .error err
  | .ok outcome => .ok {
      interval := outcome.interval
      backend := outcome.backend
      verified := decide (outcome.interval.hi ≤ bound)
    }

/-- Check a lower bound over a box using the public checked evaluator. -/
def checkLowerBoundBox (e : Expr) (box : List IntervalRat) (bound : ℚ)
    (options : EvalOptions := {}) : EvalResult BoundCheckOutcome :=
  match evalInterval e box options with
  | .error err => .error err
  | .ok outcome => .ok {
      interval := outcome.interval
      backend := outcome.backend
      verified := decide (bound ≤ outcome.interval.lo)
    }

/-- A successful box upper-bound check proves the requested semantic bound. -/
theorem verifyUpperBoundBox {e : Expr} {box : List IntervalRat} {bound : ℚ}
    {options : EvalOptions} {outcome : BoundCheckOutcome}
    (hcheck : checkUpperBoundBox e box bound options = .ok outcome)
    (hverified : outcome.verified = true) :
    ∀ rho, BoxEnvMem rho box → Expr.eval rho e ≤ bound := by
  simp only [checkUpperBoundBox] at hcheck
  split at hcheck
  · contradiction
  · next evalOutcome heval =>
      cases hcheck
      simp only at hverified
      have hle : evalOutcome.interval.hi ≤ bound := by
        exact of_decide_eq_true hverified
      intro rho hrho
      have hmem := evalInterval_correct heval hrho
      exact le_trans hmem.2 (by exact_mod_cast hle)

/-- A successful box lower-bound check proves the requested semantic bound. -/
theorem verifyLowerBoundBox {e : Expr} {box : List IntervalRat} {bound : ℚ}
    {options : EvalOptions} {outcome : BoundCheckOutcome}
    (hcheck : checkLowerBoundBox e box bound options = .ok outcome)
    (hverified : outcome.verified = true) :
    ∀ rho, BoxEnvMem rho box → bound ≤ Expr.eval rho e := by
  simp only [checkLowerBoundBox] at hcheck
  split at hcheck
  · contradiction
  · next evalOutcome heval =>
      cases hcheck
      simp only at hverified
      have hle : bound ≤ evalOutcome.interval.lo := by
        exact of_decide_eq_true hverified
      intro rho hrho
      have hmem := evalInterval_correct heval hrho
      exact le_trans (by exact_mod_cast hle) hmem.1

/-- Concrete backend used by the first public Boolean bound checker. -/
def backend : ConcreteBackend := .dyadic

/-- Check a non-strict upper bound with a checked Dyadic evaluator. -/
def checkUpperBound (e : Expr) (interval : IntervalRat) (bound : ℚ)
    (precision : PrecisionOptions := {}) : Bool :=
  decide (precision.dyadicExponent ≤ 0) &&
    Validity.Dyadic.checkUpperBoundDyadicChecked e interval.lo interval.hi interval.le
      bound precision.dyadicExponent precision.taylorDepth

/-- Check a non-strict lower bound with a checked Dyadic evaluator. -/
def checkLowerBound (e : Expr) (interval : IntervalRat) (bound : ℚ)
    (precision : PrecisionOptions := {}) : Bool :=
  decide (precision.dyadicExponent ≤ 0) &&
    Validity.Dyadic.checkLowerBoundDyadicChecked e interval.lo interval.hi interval.le
      bound precision.dyadicExponent precision.taylorDepth

/-- Check simultaneous lower and upper bounds. -/
def checkBounds (e : Expr) (interval : IntervalRat) (lower upper : ℚ)
    (precision : PrecisionOptions := {}) : Bool :=
  checkLowerBound e interval lower precision &&
    checkUpperBound e interval upper precision

/-- A successful public upper-bound certificate proves the semantic bound. -/
theorem verifyUpperBound {e : Expr} {interval : IntervalRat} {bound : ℚ}
    {precision : PrecisionOptions}
    (hcheck : checkUpperBound e interval bound precision = true) :
    ∀ x ∈ interval, Expr.eval (fun _ => x) e ≤ bound := by
  simp only [checkUpperBound, Bool.and_eq_true, decide_eq_true_eq] at hcheck
  intro x hx
  apply Validity.Dyadic.verify_upper_bound_dyadic_checked
    e interval.lo interval.hi interval.le bound
      precision.dyadicExponent precision.taylorDepth hcheck.1 hcheck.2
  rwa [← IntervalRat.mem_iff_mem_Icc]

/-- A successful public lower-bound certificate proves the semantic bound. -/
theorem verifyLowerBound {e : Expr} {interval : IntervalRat} {bound : ℚ}
    {precision : PrecisionOptions}
    (hcheck : checkLowerBound e interval bound precision = true) :
    ∀ x ∈ interval, bound ≤ Expr.eval (fun _ => x) e := by
  simp only [checkLowerBound, Bool.and_eq_true, decide_eq_true_eq] at hcheck
  intro x hx
  apply Validity.Dyadic.verify_lower_bound_dyadic_checked
    e interval.lo interval.hi interval.le bound
      precision.dyadicExponent precision.taylorDepth hcheck.1 hcheck.2
  rwa [← IntervalRat.mem_iff_mem_Icc]

/-- A successful two-sided certificate proves both semantic bounds. -/
theorem verifyBounds {e : Expr} {interval : IntervalRat} {lower upper : ℚ}
    {precision : PrecisionOptions}
    (hcheck : checkBounds e interval lower upper precision = true) :
    ∀ x ∈ interval,
      lower ≤ Expr.eval (fun _ => x) e ∧ Expr.eval (fun _ => x) e ≤ upper := by
  simp only [checkBounds, Bool.and_eq_true] at hcheck
  intro x hx
  exact
    ⟨verifyLowerBound hcheck.1 x hx,
      verifyUpperBound hcheck.2 x hx⟩

end LeanCert.API.Bounds
