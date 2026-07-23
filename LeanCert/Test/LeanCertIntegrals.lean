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

private def shiftedSquare (x : ℝ) : ℝ := (x - 1) ^ 2

example : (∫ x in (0 : ℝ)..2, shiftedSquare x) = 2 / 3 := by
  leancert

example : (∫ x in (0 : ℝ)..1, Real.exp x) ≤ 2 := by
  leancert

example : (∫ x in (0 : ℝ)..1, Real.sin x) ≤ 1 := by
  leancert (budget := 2)

-- A failed exact/numerical portfolio restores the original goal.
example (h : (∫ x in (0 : ℝ)..1, Real.exp x) = 1) :
    (∫ x in (0 : ℝ)..1, Real.exp x) = 1 := by
  fail_if_success leancert
  exact h
