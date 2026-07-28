/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.API.Eval
import LeanCert.Validity.Dyadic

/-!
# Public checked Boolean bound certificates

This module is the proof-facing companion to `LeanCert.API.Eval`.
`evalInterval` returns structured `EvalResult` data for programmatic callers;
the checkers here return `Bool` so reflective tactics can close
`check... = true` using their configured kernel/native verification route.

The first stable implementation is explicitly Dyadic-backed. Domain validity
and precision validity are included in each Boolean certificate, so the Golden
Theorems require no separate expression-support or domain premise.
-/

namespace LeanCert.API.Bounds

open LeanCert Core

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
