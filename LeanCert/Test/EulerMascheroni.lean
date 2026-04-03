/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Tactic.IntervalAuto

/-!
# Tests for `Real.eulerMascheroniConstant` support in `interval_decide`

Uses tight bounds: 0.5722 ≤ γ ≤ 0.5823, derived from
`eulerMascheroniSeq 100 < γ < eulerMascheroniSeq' 100`
combined with LeanCert's computable log intervals.
-/

-- The motivating example from the issue
example : (0.5 : ℝ) ≤ Real.eulerMascheroniConstant := by interval_decide

-- Tighter lower bound (impossible with Mathlib's 1/2 alone)
example : (0.572 : ℝ) ≤ Real.eulerMascheroniConstant := by interval_decide

-- Tighter upper bound (impossible with Mathlib's 2/3 alone)
example : Real.eulerMascheroniConstant ≤ 0.583 := by interval_decide
