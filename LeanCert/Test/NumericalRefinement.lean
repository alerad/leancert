/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert
import LeanCert.API.Bounds

/-! # Coordinated numerical-refinement regressions -/

namespace LeanCert.Test.NumericalRefinement

open LeanCert LeanCert.Core LeanCert.API.Bounds LeanCert.Tactic

private def unit : IntervalRat := ⟨0, 1, by norm_num⟩
private def exponential : Expr := .exp (.var 0)
private def veryTightUpper : ℚ :=
  2718281828459045235360287472 / 1000000000000000000000000000

example : (NumericalRefinementPolicy.adaptive 10 4).stages = [
    ⟨0, -53, 10, 0⟩,
    ⟨1, -85, 20, 2⟩,
    ⟨2, -117, 30, 4⟩
  ] := by native_decide

example : (NumericalRefinementPolicy.fixedTaylor 20 6).stages = [
    ⟨0, -53, 20, 0⟩,
    ⟨1, -85, 20, 3⟩,
    ⟨2, -117, 20, 6⟩
  ] := by native_decide

-- The historical fixed `-80` precision cannot certify this bound even with
-- enough Taylor terms; coordinated refinement reaches a successful stage.
example : LeanCert.API.Bounds.checkUpperBound exponential unit veryTightUpper
    { dyadicExponent := -80, taylorDepth := 30 } = false := by native_decide

example : LeanCert.API.Bounds.checkUpperBound exponential unit veryTightUpper
    { dyadicExponent := -117, taylorDepth := 30 } = true := by native_decide

example : ∀ x ∈ Set.Icc (0 : ℝ) 1,
    Real.exp x ≤
      (2718281828459045235360287472 /
        1000000000000000000000000000 : ℚ) := by
  certify_bound

example : ∀ x ∈ Set.Icc (0 : ℝ) 1,
    Real.exp x ≤
      (2718281828459045235360287472 /
        1000000000000000000000000000 : ℚ) := by
  leancert

-- The unified dedicated entry point shares the same schedule rather than
-- nesting its historical Taylor loop around the precision loop.
example : ∀ x ∈ Set.Icc (0 : ℝ) 1,
    Real.exp x ≤
      (2718281828459045235360287472 /
        1000000000000000000000000000 : ℚ) := by
  interval_auto

example : Real.exp 1 ≤
    (2718281828459045235360287472 /
      1000000000000000000000000000 : ℚ) := by
  leancert

example : Real.exp 1 ≤
    (2718281828459045235360287472 /
      1000000000000000000000000000 : ℚ) := by
  interval_auto

end LeanCert.Test.NumericalRefinement
