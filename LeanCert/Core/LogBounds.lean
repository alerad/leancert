/-
Copyright (c) 2024 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# Logarithm Bounds

This file provides certified bounds on the natural logarithm, useful for
numerical analysis and the Prime Number Theorem formalization.

## Main results

* `log_lower_taylor` : `t - t²/2 ≤ log(1+t)` for `t ≥ 0`
* `log_ge'` : `(t/t₀) * log(1-t₀) ≤ log(1-t)` for `0 ≤ t ≤ t₀ < 1` (concavity)
* `symmetricLogComb_pos` : The symmetric combination `1/log(1+t) + 1/log(1-t) > 0`
* `symmetricLogComb_le_two` : The symmetric combination is bounded by 2

## References

* Tao's Prime Number Theorem formalization (PNT+)
* Blueprint: Sublemmas 9.1.2-9.1.5
-/

namespace LeanCert.Core

open Real Set

/-! ## Taylor-style lower bound for log(1+t) -/

/-- For t ≥ 0, we have t - t²/2 ≤ log(1+t).
    Proof: Chain `t - t²/2 ≤ 2t/(t+2) ≤ log(1+t)` using `le_log_one_add_of_nonneg`. -/
theorem log_lower_taylor (t : ℝ) (ht : 0 ≤ t) : t - t^2 / 2 ≤ log (1 + t) := by
  have h1pt_pos : 0 < 1 + t := by linarith
  have h_chain : t - t^2 / 2 ≤ 2 * t / (t + 2) := by
    by_cases ht0 : t = 0
    · simp [ht0]
    · have ht_pos : 0 < t := ht.lt_of_ne' ht0
      have ht2_pos : 0 < t + 2 := by linarith
      rw [le_div_iff₀ ht2_pos]
      have h1 : (t - t^2 / 2) * (t + 2) = 2*t - t^3/2 := by ring
      rw [h1]
      have h2 : t^3 / 2 ≥ 0 := by positivity
      linarith
  calc t - t^2 / 2 ≤ 2 * t / (t + 2) := h_chain
    _ ≤ log (1 + t) := le_log_one_add_of_nonneg ht

/-! ## Concavity bound for log(1-t) -/

/-- For 0 ≤ t ≤ t₀ < 1, we have (t/t₀) * log(1-t₀) ≤ log(1-t).
    This follows from concavity of log on (0, ∞). -/
theorem log_ge' (t t₀ : ℝ) (ht : 0 ≤ t) (ht0 : t ≤ t₀) (ht0' : t₀ < 1) :
    (t / t₀) * log (1 - t₀) ≤ log (1 - t) := by
  by_cases ht0_eq : t₀ = 0
  · have ht_eq : t = 0 := le_antisymm (ht0.trans (le_of_eq ht0_eq)) ht
    simp only [ht0_eq, ht_eq]
    simp
  · have ht0_pos : 0 < t₀ := lt_of_le_of_ne (ht.trans ht0) (Ne.symm ht0_eq)
    have h1mt0_pos : 0 < 1 - t₀ := by linarith
    have h1mt_pos : 0 < 1 - t := by linarith [ht0]
    have hconcave := StrictConcaveOn.concaveOn strictConcaveOn_log_Ioi
    set a := t / t₀
    set b := 1 - t / t₀
    have ha_nonneg : 0 ≤ a := div_nonneg ht (le_of_lt ht0_pos)
    have ha_le1 : a ≤ 1 := div_le_one_of_le₀ ht0 (le_of_lt ht0_pos)
    have hb_nonneg : 0 ≤ b := by simp only [b]; linarith
    have hab : a + b = 1 := by simp only [a, b]; ring
    have hx_mem : 1 - t₀ ∈ Set.Ioi (0 : ℝ) := h1mt0_pos
    have hy_mem : (1 : ℝ) ∈ Set.Ioi (0 : ℝ) := Set.mem_Ioi.mpr one_pos
    have hconv : a * (1 - t₀) + b * 1 = 1 - t := by
      simp only [a, b]
      field_simp
      ring
    have hconc := hconcave.2 hx_mem hy_mem ha_nonneg hb_nonneg hab
    simp only [smul_eq_mul] at hconc
    rw [hconv, log_one, mul_zero, add_zero] at hconc
    exact hconc

/-! ## Symmetric combination bounds -/

/-- The symmetric combination g(t) = 1/log(1+t) + 1/log(1-t).
    Despite the apparent singularities, this is well-defined and bounded for t ∈ (0, 1). -/
noncomputable def symmetricLogComb (t : ℝ) : ℝ := 1 / log (1 + t) + 1 / log (1 - t)

/-- g(t) > 0 for 0 < t < 1.
    Key identity: g(t) = log(1-t²) / (log(1+t) · log(1-t)) = (neg)/(neg) > 0. -/
theorem symmetricLogComb_pos (t : ℝ) (ht_pos : 0 < t) (ht_lt : t < 1) :
    0 < symmetricLogComb t := by
  have h1pt_pos : 0 < 1 + t := by linarith
  have h1mt_pos : 0 < 1 - t := by linarith
  have h1mt2_pos : 0 < 1 - t^2 := by nlinarith [sq_nonneg t]
  have h1mt2_lt1 : 1 - t^2 < 1 := by nlinarith [sq_nonneg t]
  have hlog1p_pos : log (1 + t) > 0 := log_pos (by linarith : 1 < 1 + t)
  have hlog1m_neg : log (1 - t) < 0 := log_neg h1mt_pos (by linarith : 1 - t < 1)
  have hlog1mt2_neg : log (1 - t^2) < 0 := log_neg h1mt2_pos h1mt2_lt1
  have hdenom_neg : log (1 + t) * log (1 - t) < 0 := mul_neg_of_pos_of_neg hlog1p_pos hlog1m_neg
  have hlog1p_ne : log (1 + t) ≠ 0 := ne_of_gt hlog1p_pos
  have hlog1m_ne : log (1 - t) ≠ 0 := ne_of_lt hlog1m_neg
  have halt : symmetricLogComb t = log (1 - t^2) / (log (1 + t) * log (1 - t)) := by
    unfold symmetricLogComb
    have h1 : 1 / log (1 + t) + 1 / log (1 - t) =
        (log (1 - t) + log (1 + t)) / (log (1 + t) * log (1 - t)) := by field_simp
    have h2 : log (1 - t) + log (1 + t) = log ((1 - t) * (1 + t)) :=
      (log_mul (ne_of_gt h1mt_pos) (ne_of_gt h1pt_pos)).symm
    have h3 : (1 - t) * (1 + t) = 1 - t^2 := by ring
    simp only [h1, h2, h3]
  rw [halt]
  exact div_pos_of_neg_of_neg hlog1mt2_neg hdenom_neg

/-- g(t) ≤ 2 for 0 < t < 1.
    Proof uses: log(1+t) ≥ t/(1+t), log(1-t) ≥ -t/(1-t)
    Hence: 1/log(1+t) ≤ (1+t)/t, 1/log(1-t) ≤ -(1-t)/t
    Sum: ≤ (1+t)/t - (1-t)/t = 2 -/
theorem symmetricLogComb_le_two (t : ℝ) (ht_pos : 0 < t) (ht_lt : t < 1) :
    symmetricLogComb t ≤ 2 := by
  have h1pt_pos : 0 < 1 + t := by linarith
  have h1mt_pos : 0 < 1 - t := by linarith
  have h1pt_ne : 1 + t ≠ 0 := ne_of_gt h1pt_pos
  have h1mt_ne : 1 - t ≠ 0 := ne_of_gt h1mt_pos
  have ht_ne : t ≠ 0 := ne_of_gt ht_pos
  have h1pt_gt1 : 1 < 1 + t := by linarith
  have h1mt_lt1 : 1 - t < 1 := by linarith
  have hlog1p_pos : 0 < log (1 + t) := log_pos h1pt_gt1
  have hlog1m_neg : log (1 - t) < 0 := log_neg h1mt_pos h1mt_lt1
  -- Bound: log(1+t) ≥ t/(1+t)
  have hlog1p_lb : t / (1 + t) ≤ log (1 + t) := by
    have h := one_sub_inv_le_log_of_pos h1pt_pos
    convert h using 1
    field_simp; ring
  -- Bound: log(1-t) ≥ -t/(1-t)
  have hlog1m_lb : -t / (1 - t) ≤ log (1 - t) := by
    have h := one_sub_inv_le_log_of_pos h1mt_pos
    convert h using 1
    field_simp; ring
  -- Upper bound for 1/log(1+t)
  have hlog1p_inv_ub : 1 / log (1 + t) ≤ (1 + t) / t := by
    rw [one_div, le_div_iff₀ ht_pos, inv_mul_le_iff₀ hlog1p_pos]
    calc t = t / (1 + t) * (1 + t) := by field_simp
      _ ≤ log (1 + t) * (1 + t) := mul_le_mul_of_nonneg_right hlog1p_lb (le_of_lt h1pt_pos)
  -- Upper bound for 1/log(1-t)
  have hlog1m_inv_ub : 1 / log (1 - t) ≤ -(1 - t) / t := by
    have hneg_log : 0 < -log (1 - t) := neg_pos.mpr hlog1m_neg
    have hneg_log_ub : -log (1 - t) ≤ t / (1 - t) := by
      have h : -t / (1 - t) = -(t / (1 - t)) := by ring
      rw [h] at hlog1m_lb
      linarith
    have hinv_lb : (1 - t) / t ≤ 1 / (-log (1 - t)) := by
      rw [div_le_div_iff₀ ht_pos hneg_log]
      calc (1 - t) * -log (1 - t) = -log (1 - t) * (1 - t) := by ring
        _ ≤ t / (1 - t) * (1 - t) := mul_le_mul_of_nonneg_right hneg_log_ub (le_of_lt h1mt_pos)
        _ = t := by field_simp
        _ = 1 * t := by ring
    have hlog1m_ne : log (1 - t) ≠ 0 := ne_of_lt hlog1m_neg
    calc 1 / log (1 - t) = -(1 / -log (1 - t)) := by field_simp [hlog1m_ne]
      _ ≤ -((1 - t) / t) := neg_le_neg hinv_lb
      _ = -(1 - t) / t := by ring
  -- Combine
  unfold symmetricLogComb
  calc 1 / log (1 + t) + 1 / log (1 - t)
      ≤ (1 + t) / t + (-(1 - t) / t) := add_le_add hlog1p_inv_ub hlog1m_inv_ub
    _ = ((1 + t) - (1 - t)) / t := by ring
    _ = 2 * t / t := by ring
    _ = 2 := by field_simp

/-- |g(t)| ≤ 2 for 0 < t < 1. -/
theorem symmetricLogComb_abs_le_two (t : ℝ) (ht_pos : 0 < t) (ht_lt : t < 1) :
    |symmetricLogComb t| ≤ 2 := by
  have hpos := symmetricLogComb_pos t ht_pos ht_lt
  rw [abs_of_pos hpos]
  exact symmetricLogComb_le_two t ht_pos ht_lt

/-! ## Tighter bounds via alternative form

The symmetric combination can be written as:
  g(t) = log(1-t²) / (log(1+t) · log(1-t))

Key properties:
- g(t) → 1 as t → 0⁺ (removable singularity)
- g(t) is continuous and increasing on (0, 1)
- g(1/2) ≈ 1.024

The PNT+ blueprint claims |g(t)| ≤ log(4/3)/(4/3) ≈ 0.216, but this is
clearly incorrect since g(t) → 1. The correct bound should be around 4/3.
-/

/-- g(t) ≤ 4/3 for 0 < t ≤ 1/2.
    This is a tighter bound than 2, useful for integration estimates.

    **Status:** Numerically verified but not formally proven.

    **Why this is hard:**
    The expression g(t) = 1/log(1+t) + 1/log(1-t) suffers from the "dependency problem"
    in interval arithmetic: the variable t appears multiple times, causing naive interval
    bounds to be very loose. Even with LeanCert's branch-and-bound optimizer, verification
    fails on intervals like [0.1, 0.5] due to overestimation.

    **Numerical verification:** sup{g(t) : t ∈ (0, 1/2]} ≈ 1.024 < 4/3

    **Possible proof approaches:**
    1. Use the limit g(t) → 1 as t → 0⁺ (proven) for small t, then verify the bound on
       [δ, 1/2] using a very fine partition (hundreds of intervals)
    2. Calculus: show g' > 0, so g is increasing, then evaluate g(1/2) < 4/3
    3. Use the alternative form g(t) = log(1-t²)/(log(1+t)·log(1-t)) with Taylor models

    **For applications:** Use `symmetricLogComb_le_two` (proven) as a fallback. -/
theorem symmetricLogComb_le_four_thirds (t : ℝ) (ht_pos : 0 < t) (ht_le : t ≤ 1/2) :
    symmetricLogComb t ≤ 4/3 := by
  -- Numerically verified but formally unproven due to interval arithmetic limitations.
  -- The weaker bound symmetricLogComb_le_two (≤ 2) is proven and sufficient for most uses.
  sorry

/-- The symmetric combination approaches 1 as t → 0.
    More precisely: |g(t) - 1| → 0 as t → 0⁺.

    This is proven in LeanCert.Engine.TaylorModel.Log1p as
    `symmetricLogCombination_tendsto_one`. The definitions are definitionally equal:
    `symmetricLogComb = LeanCert.Engine.TaylorModel.symmetricLogCombination`

    Due to import constraints (LogBounds is in Core, Log1p is in Engine/TaylorModel),
    we cannot directly reference the proof here. See PNT_LogBounds.lean for the
    re-export that connects these results. -/
theorem symmetricLogComb_tendsto_one :
    Filter.Tendsto symmetricLogComb (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
  -- Proof: See LeanCert.Engine.TaylorModel.symmetricLogCombination_tendsto_one
  -- The two definitions are definitionally equal.
  -- Cannot import here due to module structure, but the proof is complete in Log1p.lean
  sorry

end LeanCert.Core
