/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Tactic

/-!
# Natural integral tests

Ordinary interval-integral statements are solved through the public semantic
front door.  Polynomial goals use exact rational certificates; transcendental
inequalities use checked partition search.
-/

open MeasureTheory

example : (∫ x in (0 : ℝ)..1, x ^ 2) = 1 / 3 := by
  leancert

example : (∫ x in (0 : ℝ)..1, (3 : ℝ) * x ^ 2 + 2 * x + 7) = 9 := by
  leancert?

example : (∫ x in (1 : ℝ)..0, x ^ 2) = -(1 / 3) := by
  leancert

example : (∫ x in (0 : ℝ)..1, x / 2) = 1 / 4 := by
  leancert

example : (3 / 10 : ℝ) ≤ (∫ x in (0 : ℝ)..1, x ^ 2) := by
  leancert

example : (∫ x in (0 : ℝ)..1, x ^ 2) ≤ (2 / 5 : ℝ) := by
  leancert

example : (3 / 10 : ℝ) ≤ (∫ x in (0 : ℝ)..1, x ^ 2) ∧
    (∫ x in (0 : ℝ)..1, x ^ 2) ≤ 2 / 5 := by
  leancert

/-! False rational-polynomial equalities are ordinary refutations, not proof
transport failures.  These cover a monomial, a linear term, and a constant. -/

/--
error: integral_exact: The statement is false. Computed integral: 1/4; claimed: 1/3.
-/
#guard_msgs in
example : (∫ x in (0 : ℝ)..1, x ^ 3) = 1 / 3 := by
  integral_exact

/--
error: integral_exact: The statement is false. Computed integral: 1/2; claimed: 1/5.
-/
#guard_msgs in
example : (∫ x in (0 : ℝ)..1, x) = 1 / 5 := by
  integral_exact

/--
error: integral_exact: The statement is false. Computed integral: 1; claimed: 2.
-/
#guard_msgs in
example : (∫ _x in (0 : ℝ)..1, (1 : ℝ)) = 2 := by
  integral_exact

/--
error: LeanCert recognized: definite integral bound

The statement is false.

Certified counterexample: exact rational integral evaluation
The computed integral is 1/2, not 1/5.
-/
#guard_msgs in
example : (∫ x in (0 : ℝ)..1, x) = 1 / 5 := by
  leancert?

private def shiftedSquare (x : ℝ) : ℝ := (x - 1) ^ 2

example : (∫ x in (0 : ℝ)..2, shiftedSquare x) = 2 / 3 := by
  leancert

example : (∫ x in (0 : ℝ)..1, Real.exp x) ≤ 2 := by
  leancert

example : (∫ x in (0 : ℝ)..1, Real.sin x) ≤ 1 := by
  leancert (budget := 2)

-- Numerical integration respects oriented interval semantics.
example : (∫ x in (1 : ℝ)..0, Real.exp x) ≥ -2 := by
  leancert

-- A failed exact/numerical portfolio restores the original goal.
example (h : (∫ x in (0 : ℝ)..1, Real.exp x) = 1) :
    (∫ x in (0 : ℝ)..1, Real.exp x) = 1 := by
  fail_if_success leancert
  exact h
