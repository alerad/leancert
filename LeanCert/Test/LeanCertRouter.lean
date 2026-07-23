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

private def checkerExpr : LeanCert.Core.Expr := .var 0
private def checkerInterval : LeanCert.Core.IntervalRat := ⟨0, 1, by norm_num⟩

example : LeanCert.Validity.checkUpperBound checkerExpr checkerInterval 1 {} = true := by
  leancert?

example : (3 : ℝ) / 2 < 2 := by
  leancert (budget := 1)

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
example : ∀ x ∈ Set.Icc (0 : ℝ) 1, x * (1 - x) ≤ (27 / 100 : ℚ) := by
  leancert? (subdivisions := 8)

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

-- Question mode proves the goal and reports the winning dedicated tactic.
example : ∀ x ∈ Set.Icc (0 : ℝ) 1, Real.sin x ≤ 1 := by
  leancert?
