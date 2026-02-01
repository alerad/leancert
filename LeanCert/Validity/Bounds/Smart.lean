/-
Copyright (c) 2024 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Validity.Bounds.Core
import LeanCert.Engine.AD

/-!
# Smart Bounds with Monotonicity

This module provides monotonicity-aware bounds that use derivative information
to get tighter bounds at interval endpoints. If the function is monotonic on
the interval, we can evaluate at the appropriate endpoint to get an exact
bound, avoiding Taylor series remainder widening.

## Main definitions

### Boolean Checkers
* `checkLowerBoundSmart` - Lower bound check using monotonicity
* `checkUpperBoundSmart` - Upper bound check using monotonicity

### Monotonicity Helpers
* `increasing_min_at_left_core` - For increasing functions, minimum is at left endpoint
* `decreasing_min_at_right_core` - For decreasing functions, minimum is at right endpoint
* `increasing_max_at_right_core` - For increasing functions, maximum is at right endpoint
* `decreasing_max_at_left_core` - For decreasing functions, maximum is at left endpoint

### Golden Theorems
* `verify_lower_bound_smart` - Smart lower bound verification
* `verify_upper_bound_smart` - Smart upper bound verification
-/

namespace LeanCert.Validity

open LeanCert.Core
open LeanCert.Engine

/-! ### Smart Bounds with Monotonicity

These checkers use derivative information to get tighter bounds at interval endpoints.
If the function is monotonic on the interval, we can evaluate at the appropriate
endpoint to get an exact bound, avoiding Taylor series remainder widening.
-/

/-- Smart lower bound check using monotonicity.
    1. Tries standard interval check first (fastest).
    2. If fails, computes derivative interval.
    3. If derivative > 0 (increasing), checks if f(I.lo) ≥ c.
    4. If derivative < 0 (decreasing), checks if f(I.hi) ≥ c. -/
def checkLowerBoundSmart (e : Expr) (I : IntervalRat) (c : ℚ) (cfg : EvalConfig) : Bool :=
  -- 1. Try standard check first (fastest)
  if checkLowerBound e I c cfg then true
  else
    -- 2. Compute derivative bounds
    let dI := derivIntervalCore e I cfg
    if 0 < dI.lo then
      -- Strictly increasing: minimum is at lo
      -- Evaluate at singleton lo (with domain validity check)
      checkDomainValid1 e (IntervalRat.singleton I.lo) cfg &&
        c ≤ (evalIntervalCore1 e (IntervalRat.singleton I.lo) cfg).lo
    else if dI.hi < 0 then
      -- Strictly decreasing: minimum is at hi (with domain validity check)
      checkDomainValid1 e (IntervalRat.singleton I.hi) cfg &&
        c ≤ (evalIntervalCore1 e (IntervalRat.singleton I.hi) cfg).lo
    else
      false

/-- Smart upper bound check using monotonicity.
    1. Tries standard interval check first.
    2. If fails, computes derivative interval.
    3. If derivative > 0 (increasing), checks if f(I.hi) ≤ c.
    4. If derivative < 0 (decreasing), checks if f(I.lo) ≤ c. -/
def checkUpperBoundSmart (e : Expr) (I : IntervalRat) (c : ℚ) (cfg : EvalConfig) : Bool :=
  if checkUpperBound e I c cfg then true
  else
    let dI := derivIntervalCore e I cfg
    if 0 < dI.lo then
      -- Increasing: max at hi (with domain validity check)
      checkDomainValid1 e (IntervalRat.singleton I.hi) cfg &&
        (evalIntervalCore1 e (IntervalRat.singleton I.hi) cfg).hi ≤ c
    else if dI.hi < 0 then
      -- Decreasing: max at lo (with domain validity check)
      checkDomainValid1 e (IntervalRat.singleton I.lo) cfg &&
        (evalIntervalCore1 e (IntervalRat.singleton I.lo) cfg).hi ≤ c
    else
      false

/-! ### Monotonicity Helper Theorems -/

/-- Helper: For increasing functions, the minimum is at the left endpoint -/
theorem increasing_min_at_left_core (e : Expr) (hsupp : ExprSupported e)
    (I : IntervalRat) (cfg : EvalConfig) (hpos : 0 < (derivIntervalCore e I cfg).lo) :
    ∀ x ∈ I, Expr.eval (fun _ => I.lo) e ≤ Expr.eval (fun _ => x) e := by
  intro x hx
  -- Use the MVT: f(x) - f(lo) = f'(ξ) * (x - lo) for some ξ ∈ (lo, x)
  -- Since f' > 0 and x ≥ lo, we have f(x) ≥ f(lo)
  have hdiff := evalFunc1_differentiable e hsupp
  by_cases heq : (I.lo : ℝ) = x
  · rw [heq]
  · -- x > lo since x ∈ I and x ≠ lo
    have hlo_le_x : (I.lo : ℝ) ≤ x := by
      simp only [IntervalRat.mem_def] at hx; exact hx.1
    have hlo_lt_x : (I.lo : ℝ) < x := lt_of_le_of_ne hlo_le_x heq
    -- Apply MVT
    have hmvt := exists_deriv_eq_slope (evalFunc1 e) hlo_lt_x
      (hdiff.continuous.continuousOn) (fun t _ => (hdiff t).differentiableWithinAt)
    obtain ⟨ξ, hξ_mem, hξ_eq⟩ := hmvt
    -- ξ ∈ (lo, x) ⊆ I, so deriv f ξ ∈ derivIntervalCore
    have hξ_in_I : ξ ∈ I := by
      simp only [Set.mem_Ioo] at hξ_mem
      simp only [IntervalRat.mem_def] at hx ⊢
      constructor
      · exact le_of_lt hξ_mem.1
      · exact le_trans (le_of_lt hξ_mem.2) hx.2
    have hderiv := derivIntervalCore_correct e hsupp I ξ hξ_in_I cfg
    -- deriv f ξ > 0
    have hderiv_pos : deriv (evalFunc1 e) ξ > 0 := by
      simp only [IntervalRat.mem_def] at hderiv
      calc deriv (evalFunc1 e) ξ ≥ (derivIntervalCore e I cfg).lo := hderiv.1
        _ > 0 := by exact_mod_cast hpos
    -- slope = deriv f ξ > 0, so f(x) > f(lo)
    have hslope_pos : (evalFunc1 e x - evalFunc1 e I.lo) / (x - I.lo) > 0 := by
      rw [← hξ_eq]; exact hderiv_pos
    have hdiff_pos : x - (I.lo : ℝ) > 0 := sub_pos.mpr hlo_lt_x
    have hnum_pos : evalFunc1 e x - evalFunc1 e I.lo > 0 := by
      have := div_pos_iff.mp hslope_pos
      cases this with
      | inl h => exact h.1
      | inr h => exact absurd hdiff_pos (not_lt.mpr (le_of_lt h.2))
    simp only [evalFunc1] at hnum_pos ⊢
    linarith

/-- Helper: For decreasing functions, the minimum is at the right endpoint -/
theorem decreasing_min_at_right_core (e : Expr) (hsupp : ExprSupported e)
    (I : IntervalRat) (cfg : EvalConfig) (hneg : (derivIntervalCore e I cfg).hi < 0) :
    ∀ x ∈ I, Expr.eval (fun _ => I.hi) e ≤ Expr.eval (fun _ => x) e := by
  intro x hx
  have hdiff := evalFunc1_differentiable e hsupp
  by_cases heq : x = (I.hi : ℝ)
  · rw [heq]
  · have hx_le_hi : x ≤ (I.hi : ℝ) := by
      simp only [IntervalRat.mem_def] at hx; exact hx.2
    have hx_lt_hi : x < (I.hi : ℝ) := lt_of_le_of_ne hx_le_hi heq
    have hmvt := exists_deriv_eq_slope (evalFunc1 e) hx_lt_hi
      (hdiff.continuous.continuousOn) (fun t _ => (hdiff t).differentiableWithinAt)
    obtain ⟨ξ, hξ_mem, hξ_eq⟩ := hmvt
    have hξ_in_I : ξ ∈ I := by
      simp only [Set.mem_Ioo] at hξ_mem
      simp only [IntervalRat.mem_def] at hx ⊢
      constructor
      · exact le_trans hx.1 (le_of_lt hξ_mem.1)
      · exact le_of_lt hξ_mem.2
    have hderiv := derivIntervalCore_correct e hsupp I ξ hξ_in_I cfg
    have hderiv_neg : deriv (evalFunc1 e) ξ < 0 := by
      simp only [IntervalRat.mem_def] at hderiv
      calc deriv (evalFunc1 e) ξ ≤ (derivIntervalCore e I cfg).hi := hderiv.2
        _ < 0 := by exact_mod_cast hneg
    have hslope_neg : (evalFunc1 e I.hi - evalFunc1 e x) / ((I.hi : ℝ) - x) < 0 := by
      rw [← hξ_eq]; exact hderiv_neg
    have hdiff_pos : (I.hi : ℝ) - x > 0 := sub_pos.mpr hx_lt_hi
    have hnum_neg : evalFunc1 e I.hi - evalFunc1 e x < 0 := by
      have := div_neg_iff.mp hslope_neg
      cases this with
      | inl h => exact absurd hdiff_pos (not_lt.mpr (le_of_lt h.2))
      | inr h => exact h.1
    simp only [evalFunc1] at hnum_neg ⊢
    linarith

/-- Smart lower bound verification using monotonicity -/
theorem verify_lower_bound_smart (e : Expr) (hsupp : ExprSupported e)
    (I : IntervalRat) (c : ℚ) (cfg : EvalConfig)
    (h_cert : checkLowerBoundSmart e I c cfg = true) :
    ∀ x ∈ I, c ≤ Expr.eval (fun _ => x) e := by
  unfold checkLowerBoundSmart at h_cert
  -- Split on the Bool conditions
  split at h_cert
  · -- Case 1: Standard check passed
    rename_i h_std
    exact verify_lower_bound e hsupp.toCore I c cfg h_std
  · -- Standard check failed, simplify the let binding and split
    rename_i h_std_neg
    simp only at h_cert  -- eliminate let binding
    split at h_cert
    · -- Case 2: Derivative strictly positive (increasing)
      rename_i h_pos
      intro x hx
      have hlo_mem : (I.lo : ℝ) ∈ IntervalRat.singleton I.lo := IntervalRat.mem_singleton I.lo
      -- Extract domain validity and bound from the combined check
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h_cert
      have hdom := checkDomainValid1_correct e (IntervalRat.singleton I.lo) cfg h_cert.1
      have hbound := h_cert.2
      have heval := evalIntervalCore1_correct e hsupp.toCore I.lo (IntervalRat.singleton I.lo) hlo_mem cfg hdom
      simp only [IntervalRat.mem_def] at heval
      have hmono := increasing_min_at_left_core e hsupp I cfg h_pos x hx
      calc (c : ℝ) ≤ (evalIntervalCore1 e (IntervalRat.singleton I.lo) cfg).lo := by exact_mod_cast hbound
        _ ≤ Expr.eval (fun _ => I.lo) e := heval.1
        _ ≤ Expr.eval (fun _ => x) e := hmono
    · -- Not increasing, split on decreasing condition
      rename_i h_pos_neg
      split at h_cert
      · -- Case 3: Derivative strictly negative (decreasing)
        rename_i h_neg
        intro x hx
        have hhi_mem : (I.hi : ℝ) ∈ IntervalRat.singleton I.hi := IntervalRat.mem_singleton I.hi
        -- Extract domain validity and bound from the combined check
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h_cert
        have hdom := checkDomainValid1_correct e (IntervalRat.singleton I.hi) cfg h_cert.1
        have hbound := h_cert.2
        have heval := evalIntervalCore1_correct e hsupp.toCore I.hi (IntervalRat.singleton I.hi) hhi_mem cfg hdom
        simp only [IntervalRat.mem_def] at heval
        have hmono := decreasing_min_at_right_core e hsupp I cfg h_neg x hx
        calc (c : ℝ) ≤ (evalIntervalCore1 e (IntervalRat.singleton I.hi) cfg).lo := by exact_mod_cast hbound
          _ ≤ Expr.eval (fun _ => I.hi) e := heval.1
          _ ≤ Expr.eval (fun _ => x) e := hmono
      · -- Neither increasing nor decreasing => impossible since h_cert = true
        exact absurd h_cert Bool.false_ne_true

/-- Helper: For increasing functions, the maximum is at the right endpoint -/
theorem increasing_max_at_right_core (e : Expr) (hsupp : ExprSupported e)
    (I : IntervalRat) (cfg : EvalConfig) (hpos : 0 < (derivIntervalCore e I cfg).lo) :
    ∀ x ∈ I, Expr.eval (fun _ => x) e ≤ Expr.eval (fun _ => I.hi) e := by
  intro x hx
  have hdiff := evalFunc1_differentiable e hsupp
  by_cases heq : x = (I.hi : ℝ)
  · rw [heq]
  · have hx_le_hi : x ≤ (I.hi : ℝ) := by
      simp only [IntervalRat.mem_def] at hx; exact hx.2
    have hx_lt_hi : x < (I.hi : ℝ) := lt_of_le_of_ne hx_le_hi heq
    have hmvt := exists_deriv_eq_slope (evalFunc1 e) hx_lt_hi
      (hdiff.continuous.continuousOn) (fun t _ => (hdiff t).differentiableWithinAt)
    obtain ⟨ξ, hξ_mem, hξ_eq⟩ := hmvt
    have hξ_in_I : ξ ∈ I := by
      simp only [Set.mem_Ioo] at hξ_mem
      simp only [IntervalRat.mem_def] at hx ⊢
      constructor
      · exact le_trans hx.1 (le_of_lt hξ_mem.1)
      · exact le_of_lt hξ_mem.2
    have hderiv := derivIntervalCore_correct e hsupp I ξ hξ_in_I cfg
    have hderiv_pos : deriv (evalFunc1 e) ξ > 0 := by
      simp only [IntervalRat.mem_def] at hderiv
      calc deriv (evalFunc1 e) ξ ≥ (derivIntervalCore e I cfg).lo := hderiv.1
        _ > 0 := by exact_mod_cast hpos
    have hslope_pos : (evalFunc1 e I.hi - evalFunc1 e x) / ((I.hi : ℝ) - x) > 0 := by
      rw [← hξ_eq]; exact hderiv_pos
    have hdiff_pos : (I.hi : ℝ) - x > 0 := sub_pos.mpr hx_lt_hi
    have hnum_pos : evalFunc1 e I.hi - evalFunc1 e x > 0 := by
      have := div_pos_iff.mp hslope_pos
      cases this with
      | inl h => exact h.1
      | inr h => exact absurd hdiff_pos (not_lt.mpr (le_of_lt h.2))
    simp only [evalFunc1] at hnum_pos ⊢
    linarith

/-- Helper: For decreasing functions, the maximum is at the left endpoint -/
theorem decreasing_max_at_left_core (e : Expr) (hsupp : ExprSupported e)
    (I : IntervalRat) (cfg : EvalConfig) (hneg : (derivIntervalCore e I cfg).hi < 0) :
    ∀ x ∈ I, Expr.eval (fun _ => x) e ≤ Expr.eval (fun _ => I.lo) e := by
  intro x hx
  have hdiff := evalFunc1_differentiable e hsupp
  by_cases heq : (I.lo : ℝ) = x
  · rw [heq]
  · have hlo_le_x : (I.lo : ℝ) ≤ x := by
      simp only [IntervalRat.mem_def] at hx; exact hx.1
    have hlo_lt_x : (I.lo : ℝ) < x := lt_of_le_of_ne hlo_le_x heq
    have hmvt := exists_deriv_eq_slope (evalFunc1 e) hlo_lt_x
      (hdiff.continuous.continuousOn) (fun t _ => (hdiff t).differentiableWithinAt)
    obtain ⟨ξ, hξ_mem, hξ_eq⟩ := hmvt
    have hξ_in_I : ξ ∈ I := by
      simp only [Set.mem_Ioo] at hξ_mem
      simp only [IntervalRat.mem_def] at hx ⊢
      constructor
      · exact le_of_lt hξ_mem.1
      · exact le_trans (le_of_lt hξ_mem.2) hx.2
    have hderiv := derivIntervalCore_correct e hsupp I ξ hξ_in_I cfg
    have hderiv_neg : deriv (evalFunc1 e) ξ < 0 := by
      simp only [IntervalRat.mem_def] at hderiv
      calc deriv (evalFunc1 e) ξ ≤ (derivIntervalCore e I cfg).hi := hderiv.2
        _ < 0 := by exact_mod_cast hneg
    have hslope_neg : (evalFunc1 e x - evalFunc1 e I.lo) / (x - I.lo) < 0 := by
      rw [← hξ_eq]; exact hderiv_neg
    have hdiff_pos : x - (I.lo : ℝ) > 0 := sub_pos.mpr hlo_lt_x
    have hnum_neg : evalFunc1 e x - evalFunc1 e I.lo < 0 := by
      have := div_neg_iff.mp hslope_neg
      cases this with
      | inl h => exact absurd hdiff_pos (not_lt.mpr (le_of_lt h.2))
      | inr h => exact h.1
    simp only [evalFunc1] at hnum_neg ⊢
    linarith

/-- Smart upper bound verification using monotonicity -/
theorem verify_upper_bound_smart (e : Expr) (hsupp : ExprSupported e)
    (I : IntervalRat) (c : ℚ) (cfg : EvalConfig)
    (h_cert : checkUpperBoundSmart e I c cfg = true) :
    ∀ x ∈ I, Expr.eval (fun _ => x) e ≤ c := by
  unfold checkUpperBoundSmart at h_cert
  -- Split on the Bool conditions
  split at h_cert
  · -- Case 1: Standard check passed
    rename_i h_std
    exact verify_upper_bound e hsupp.toCore I c cfg h_std
  · -- Standard check failed, simplify the let binding and split
    rename_i h_std_neg
    simp only at h_cert  -- eliminate let binding
    split at h_cert
    · -- Case 2: Derivative strictly positive (increasing), max at hi
      rename_i h_pos
      intro x hx
      have hhi_mem : (I.hi : ℝ) ∈ IntervalRat.singleton I.hi := IntervalRat.mem_singleton I.hi
      -- Extract domain validity and bound from the combined check
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h_cert
      have hdom := checkDomainValid1_correct e (IntervalRat.singleton I.hi) cfg h_cert.1
      have hbound := h_cert.2
      have heval := evalIntervalCore1_correct e hsupp.toCore I.hi (IntervalRat.singleton I.hi) hhi_mem cfg hdom
      simp only [IntervalRat.mem_def] at heval
      have hmono := increasing_max_at_right_core e hsupp I cfg h_pos x hx
      calc Expr.eval (fun _ => x) e ≤ Expr.eval (fun _ => I.hi) e := hmono
        _ ≤ (evalIntervalCore1 e (IntervalRat.singleton I.hi) cfg).hi := heval.2
        _ ≤ c := by exact_mod_cast hbound
    · -- Not increasing, split on decreasing condition
      rename_i h_pos_neg
      split at h_cert
      · -- Case 3: Derivative strictly negative (decreasing), max at lo
        rename_i h_neg
        intro x hx
        have hlo_mem : (I.lo : ℝ) ∈ IntervalRat.singleton I.lo := IntervalRat.mem_singleton I.lo
        -- Extract domain validity and bound from the combined check
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h_cert
        have hdom := checkDomainValid1_correct e (IntervalRat.singleton I.lo) cfg h_cert.1
        have hbound := h_cert.2
        have heval := evalIntervalCore1_correct e hsupp.toCore I.lo (IntervalRat.singleton I.lo) hlo_mem cfg hdom
        simp only [IntervalRat.mem_def] at heval
        have hmono := decreasing_max_at_left_core e hsupp I cfg h_neg x hx
        calc Expr.eval (fun _ => x) e ≤ Expr.eval (fun _ => I.lo) e := hmono
          _ ≤ (evalIntervalCore1 e (IntervalRat.singleton I.lo) cfg).hi := heval.2
          _ ≤ c := by exact_mod_cast hbound
      · -- Neither increasing nor decreasing => impossible since h_cert = true
        exact absurd h_cert Bool.false_ne_true

end LeanCert.Validity
