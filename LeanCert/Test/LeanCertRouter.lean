/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Tactic

/-!
# Semantic Router Tests

Natural mathematical statements are proved through the public `leancert`
front door, importing only the stable tactic umbrella.
-/

open LeanCert
open MeasureTheory

private def checkerExpr : LeanCert.Core.Expr := .var 0
private def checkerInterval : LeanCert.Core.IntervalRat := ⟨0, 1, by norm_num⟩

/--
info: LeanCert recognized: closed certificate check

Selected strategy:
  closed Boolean certificate verification

Certificate verification:
  requested native → used native

Suggested proof:
  by
    leancert
-/
#guard_msgs in
example : LeanCert.Validity.checkUpperBound checkerExpr checkerInterval 1 {} = true := by
  leancert?

#guard_msgs in
example : (3 : ℝ) / 2 < 2 := by
  leancert (budget := 1)

/--
info: LeanCert recognized: closed numerical comparison

Selected strategy:
  exact normalization

Certificate verification:
  not required by this proof strategy

Suggested proof:
  by
    leancert

Advanced control:
  by
    norm_num
-/
#guard_msgs in
example : (1 : ℝ) < 2 := by
  leancert?

/--
info: LeanCert recognized: closed numerical comparison

Selected strategy:
  direct point enclosure (Taylor depth 10)
  Taylor depth: 10
  precision: -80

Numerical computation:
  Dyadic interval evaluation

Certificate verification:
  requested native → used native
Checker: LeanCert.Validity.checkStrictUpperBoundDyadicChecked
Verifier: LeanCert.Validity.verify_strict_upper_bound_dyadic_checked

Suggested proof:
  by
    leancert

Advanced control:
  by
    interval_auto 10
-/
#guard_msgs in
example : Real.log 2 < 7 / 10 := by
  leancert?

/--
info: LeanCert recognized: univariate interval bound

Selected strategy:
  direct interval enclosure (Taylor depth 10)
  Taylor depth: 10

Numerical computation:
  Rational interval evaluation

Certificate verification:
  requested native; actual route not observed by the legacy adapter

Suggested proof:
  by
    leancert

Advanced control:
  by
    certify_bound 10
-/
#guard_msgs in
example : ∀ x ∈ Set.Icc (0 : ℝ) 1,
    Real.exp x * Real.cos x ≤ 3 := by
  leancert?

example : ∀ x ∈ Set.Icc (0 : ℝ) 1, x ^ 2 ≤ 1 := by
  leancert

example : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
    x + y ≤ (2 : ℚ) := by
  leancert

example : ∃ x ∈ Set.Icc (1 : ℝ) 2, x ^ 2 = 2 := by
  leancert

example : ∃! x, x ∈ Set.Icc (1 : ℝ) 2 ∧ 2 = x ^ 2 := by
  leancert

example : ∀ x ∈ Set.Icc (0 : ℝ) 1, x ^ 2 + 1 ≠ 0 := by
  leancert

example : ∃ m : ℚ, ∀ x ∈ Set.Icc (0 : ℝ) 1, x ^ 2 ≥ m := by
  leancert

example : ∃ M : ℚ, ∀ x ∈ Set.Icc (0 : ℝ) 1, x ^ 2 ≤ M := by
  leancert

example : ∃ m : ℚ, ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
    x * x + y * y ≥ m := by
  leancert

example : ∃ M : ℚ, ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
    x + y ≤ M := by
  leancert

example : ∃ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1, x ≤ y := by
  leancert

example : ∃ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
    2 * y + 1 ≤ 2 * x + 1 := by
  leancert

example : ∑ _k ∈ Finset.Icc 1 10, (1 : ℝ) ≤ 11 := by
  leancert

-- The direct enclosure is too wide; the third isolated strategy uses subdivision.
/--
info: LeanCert recognized: univariate interval bound

Selected strategy:
  recursive interval subdivision
  Taylor depth 10; maximum recursive depth 8
  deepest recursive depth used: 5
  certified leaves: 14

Numerical computation:
  Rational interval evaluation

Certificate verification:
  requested kernel → used kernel (14 checks)
Checker: LeanCert.Validity.checkUpperBound
Verifier: LeanCert.Validity.verify_upper_bound_Icc_core

Suggested proof:
  by
    leancert (subdivisions := 8) (trust := kernel)

Advanced control:
  by
    interval_bound_subdiv 10 8 (trust := kernel)
-/
#guard_msgs in
example : ∀ x ∈ Set.Icc (0 : ℝ) 1, x * (1 - x) ≤ (27 / 100 : ℚ) := by
  leancert? (subdivisions := 8) (trust := kernel)

example : ∀ x ∈ Set.Icc (0 : ℝ) 1, (-27 / 100 : ℚ) ≤ x * x - x := by
  leancert (subdivisions := 8)

example : ∀ x ∈ Set.Icc (0 : ℝ) 1, x * (1 - x) < (27 / 100 : ℚ) := by
  leancert (subdivisions := 8)

example : ∀ x ∈ Set.Icc (0 : ℝ) 1, (-27 / 100 : ℚ) < x * x - x := by
  leancert (subdivisions := 8)

-- Failed portfolios restore the original goal and its local context.
example (h : ∀ x ∈ Set.Icc (-1 : ℝ) 1, x ^ 2 ≤ 0) :
    ∀ x ∈ Set.Icc (-1 : ℝ) 1, x ^ 2 ≤ 0 := by
  fail_if_success leancert (budget := 2)
  exact h

/--
error: LeanCert recognized a conjunction, but child 2 of 2 failed: closed numerical comparison

LeanCert recognized: closed numerical comparison

Attempts:
  1. exact normalization
     solver left 1 proof obligation(s):
False
  2. direct point enclosure (Taylor depth 10)
     The backend could not construct a complete certificate with the current settings.
  3. direct point enclosure (Taylor depth 20)
     The backend could not construct a complete certificate with the current settings.

Budget: spent 3 of 6

Next steps:
• Check whether the requested statement is true.
• Increase `(taylorDepth := ...)`, `(subdivisions := ...)`, or `(maxIterations := ...)` when the corresponding attempt was inconclusive.
• Use `interval_refute` to search for a certified counterexample.
-/
#guard_msgs in
example : ((1 : ℝ) < 2) ∧ ((2 : ℝ) < 1) := by
  leancert?

-- Question mode proves the goal and reports the winning dedicated tactic.
example : ∀ x ∈ Set.Icc (0 : ℝ) 1, Real.sin x ≤ 1 := by
  leancert?

/-! ## Suggested-proof and compatibility syntax

These are deliberately literal rather than generated-string tests.  Every
primary or dedicated shape that the router may recommend must continue to
elaborate verbatim.
-/

-- Primary recipe, including non-default parameters and requested trust.
example : (3 : ℝ) / 2 < 2 := by
  leancert

example : ∀ x ∈ Set.Icc (0 : ℝ) 1, x * (1 - x) ≤ (27 / 100 : ℚ) := by
  leancert (subdivisions := 8) (taylorDepth := 10) (maxIterations := 64)

example : Real.log 2 < 7 / 10 := by
  leancert (trust := kernel)

-- Dedicated recipes retained for advanced use and legacy compatibility.
example : ∀ x ∈ Set.Icc (0 : ℝ) 1, Real.exp x ≤ 3 := by
  certify_bound

example : ∀ x ∈ Set.Icc (0 : ℝ) 1, Real.exp x ≤ 3 := by
  certify_bound 20

example : ∀ x ∈ Set.Icc (0 : ℝ) 1, x * (1 - x) ≤ (27 / 100 : ℚ) := by
  interval_bound_subdiv 10 8 (trust := kernel)

example : ∃ x ∈ Set.Icc (1 : ℝ) 2, x ^ 2 = 2 := by
  interval_roots (trust := auto)

example : ∃! x, x ∈ Set.Icc (1 : ℝ) 2 ∧ x ^ 2 = 2 := by
  interval_unique_root (trust := kernel)

example : ∑ _k ∈ Finset.Icc 1 10, (1 : ℝ) ≤ 11 := by
  finsum_bound (trust := native)

example : (∫ x in (0 : ℝ)..1, x ^ 2) = 1 / 3 := by
  integral_exact
