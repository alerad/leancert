/-
Copyright (c) 2024 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Tactic

/-!
# LeanCert Showcase

Five ordinary mathematical statements covering the main public proof shapes.
Every theorem deliberately uses the semantic `leancert` front door where that
front door applies.

The mirrored guide records the selected strategy, trust boundary, and measured
runtime for each theorem.
-/

namespace LeanCert.Examples.Showcase

/-- A closed transcendental inequality. -/
theorem log_two_lt_seven_tenths : Real.log 2 < 7 / 10 := by
  leancert

private example : Real.log 2 < 7 / 10 := by
  interval_auto 10

/-- One certificate proves the nonlinear bound for every point of `[0, 1]`. -/
theorem exp_mul_cos_bound :
    ∀ x ∈ Set.Icc (0 : ℝ) 1, Real.exp x * Real.cos x ≤ 3 := by
  leancert

private example :
    ∀ x ∈ Set.Icc (0 : ℝ) 1, Real.exp x * Real.cos x ≤ 3 := by
  certify_bound 10

/-- Semantic routing recognizes a two-dimensional box. -/
theorem two_variable_box_bound :
    ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
      x + y ≤ (2 : ℚ) := by
  leancert

private example :
    ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
      x + y ≤ (2 : ℚ) := by
  multivariate_bound

/-- Interval sign and Newton certificates establish the unique square root. -/
theorem sqrt_two_unique :
    ∃! x, x ∈ Set.Icc (1 : ℝ) 2 ∧ x ^ 2 - 2 = 0 := by
  leancert

private example :
    ∃! x, x ∈ Set.Icc (1 : ℝ) 2 ∧ x ^ 2 - 2 = 0 := by
  interval_unique_root

/-- Rational-polynomial integration is checked exactly. -/
theorem square_integral :
    (∫ x in (0 : ℝ)..1, x ^ 2) = 1 / 3 := by
  leancert

private example :
    (∫ x in (0 : ℝ)..1, x ^ 2) = 1 / 3 := by
  integral_exact

end LeanCert.Examples.Showcase
