/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Tactic.IntervalAuto

/-!
# Tests for `Real.eulerMascheroniConstant` support in `interval_decide`

Uses Mathlib bounds: 1/2 < γ < 2/3.
-/

-- The motivating example from the issue
example : (0.5 : ℝ) ≤ Real.eulerMascheroniConstant := by interval_decide

-- Upper bound
example : Real.eulerMascheroniConstant ≤ 0.667 := by interval_decide

-- Both directions
example : (0.5 : ℝ) ≤ Real.eulerMascheroniConstant ∧
    Real.eulerMascheroniConstant ≤ 0.667 := by constructor <;> interval_decide

-- In an expression: γ + 1 > 1.5
example : (1.5 : ℝ) ≤ Real.eulerMascheroniConstant + 1 := by interval_decide

-- Combined with π
example : Real.eulerMascheroniConstant ≤ Real.pi := by interval_decide
