/-
Copyright (c) 2024 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Complex.ExponentialBounds

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

* Prime Number Theorem formalization (PNT+)
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

/-- Alternative form: g(t) = log(1-t²) / (log(1+t) · log(1-t)) for t ∈ (0, 1). -/
theorem symmetricLogComb_alt (t : ℝ) (ht_pos : 0 < t) (ht_lt : t < 1) :
    symmetricLogComb t = log (1 - t^2) / (log (1 + t) * log (1 - t)) := by
  have h1pt_pos : 0 < 1 + t := by linarith
  have h1mt_pos : 0 < 1 - t := by linarith
  have hlog1p_ne : log (1 + t) ≠ 0 := ne_of_gt (log_pos (by linarith : 1 < 1 + t))
  have hlog1m_ne : log (1 - t) ≠ 0 := ne_of_lt (log_neg h1mt_pos (by linarith : 1 - t < 1))
  unfold symmetricLogComb
  have h1 : 1 / log (1 + t) + 1 / log (1 - t) =
      (log (1 - t) + log (1 + t)) / (log (1 + t) * log (1 - t)) := by field_simp
  have h2 : log (1 - t) + log (1 + t) = log ((1 - t) * (1 + t)) :=
    (log_mul (ne_of_gt h1mt_pos) (ne_of_gt h1pt_pos)).symm
  have h3 : (1 - t) * (1 + t) = 1 - t^2 := by ring
  simp only [h1, h2, h3]

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

/-! ## Numerical bounds on log values -/

/-- log(3/2) ≥ 2/5. From le_log_one_add_of_nonneg with t = 1/2. -/
theorem log_three_half_ge : 2/5 ≤ log (3/2) := by
  have h := le_log_one_add_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2)
  have heq : (1:ℝ) + 1/2 = 3/2 := by norm_num
  rw [heq] at h
  convert h using 1
  norm_num

/-- log(3/2) > 2/5. Strict version. -/
theorem log_three_half_gt : 2/5 < log (3/2) := by
  calc (2:ℝ)/5 = 2 * (1/2) / ((1/2) + 2) := by norm_num
    _ < log (1 + 1/2) := lt_log_one_add_of_pos (by norm_num : (0:ℝ) < 1/2)
    _ = log (3/2) := by norm_num

/-- g(1/2) = 1/log(3/2) - 1/log(2). Explicit computation. -/
theorem symmetricLogComb_half : symmetricLogComb (1/2) = 1 / log (3/2) - 1 / log 2 := by
  unfold symmetricLogComb
  have hlog32_ne : log (3/2) ≠ 0 := ne_of_gt (log_pos (by norm_num : (1:ℝ) < 3/2))
  have hlog2_ne : log 2 ≠ 0 := ne_of_gt (log_pos one_lt_two)
  have h1 : log (1 - (1:ℝ)/2) = log (1/2) := by ring_nf
  have h2 : log (1/2 : ℝ) = -log 2 := by rw [log_div one_ne_zero two_ne_zero, log_one, zero_sub]
  have h3 : (1:ℝ) + 1/2 = 3/2 := by ring
  rw [h3, h1, h2]
  field_simp
  ring

/-- g(1/2) < 4/3. Numerical verification using bounds on log 2 and log(3/2). -/
theorem symmetricLogComb_half_lt_four_thirds : symmetricLogComb (1/2) < 4/3 := by
  rw [symmetricLogComb_half]
  -- We have: log(3/2) > 2/5 = 0.4, log(2) > 0.6931471803
  -- So: 1/log(3/2) < 2.5, 1/log(2) < 1.4428
  -- Thus: 1/log(3/2) - 1/log(2) < 2.5 - 1/0.6931471808 ≈ 1.057 < 4/3
  have hlog32_pos : 0 < log (3/2) := log_pos (by norm_num : (1:ℝ) < 3/2)
  have hlog2_pos : 0 < log 2 := log_pos one_lt_two
  have hlog32_lb : 2/5 < log (3/2) := log_three_half_gt
  have hlog2_lb : (0.6931471803 : ℝ) < log 2 := Real.log_two_gt_d9
  -- 1/log(3/2) < 5/2
  have h1 : 1 / log (3/2) < 5/2 := by
    rw [div_lt_iff₀ hlog32_pos]
    have : (2:ℝ)/5 * (5/2) = 1 := by norm_num
    linarith [mul_lt_mul_of_pos_right hlog32_lb (by norm_num : (0:ℝ) < 5/2)]
  -- 1/log(2) > 1/0.6931471808
  have hlog2_ub : log 2 < 0.6931471808 := Real.log_two_lt_d9
  have h2 : 1 / log 2 > 1/0.6931471808 := by
    exact one_div_lt_one_div_of_lt hlog2_pos hlog2_ub
  -- Combine
  calc 1 / log (3/2) - 1 / log 2
      < 5/2 - 1/0.6931471808 := by linarith
    _ < 4/3 := by norm_num

/-- g(t) ≤ 4/3 for 0 < t ≤ 1/2.
    Proof is direct from explicit log inequalities. -/
theorem symmetricLogComb_le_four_thirds (t : ℝ) (ht_pos : 0 < t) (ht_le : t ≤ 1/2) :
    symmetricLogComb t ≤ 4/3 := by
  have ht_lt : t < 1 := by linarith
  have h1pt_pos : 0 < 1 + t := by linarith
  have h1mt_pos : 0 < 1 - t := by linarith
  have h1mt2_pos : 0 < 1 - t^2 := by nlinarith [sq_nonneg t]
  have hlog1p_pos : 0 < log (1 + t) := log_pos (by linarith : (1 : ℝ) < 1 + t)
  have hlog1m_neg : log (1 - t) < 0 := log_neg h1mt_pos (by linarith : 1 - t < (1 : ℝ))
  have hden_neg : log (1 + t) * log (1 - t) < 0 := mul_neg_of_pos_of_neg hlog1p_pos hlog1m_neg

  -- Lower bound for log(1+t).
  have hlog1p_lb : 2 * t / (t + 2) ≤ log (1 + t) := le_log_one_add_of_nonneg (le_of_lt ht_pos)

  -- Upper bound for log(1-t): log(1-t) ≤ -2t/(2-t).
  have hlog1m_ub : log (1 - t) ≤ -(2 * t / (2 - t)) := by
    have hfrac_nonneg : 0 ≤ t / (1 - t) := div_nonneg (le_of_lt ht_pos) (le_of_lt h1mt_pos)
    have h := le_log_one_add_of_nonneg hfrac_nonneg
    have h1mt_ne : 1 - t ≠ 0 := ne_of_gt h1mt_pos
    have hleft : 2 * (t / (1 - t)) / (t / (1 - t) + 2) = 2 * t / (2 - t) := by
      have h2mt_ne : 2 - t ≠ 0 := by linarith
      field_simp [h1mt_ne, h2mt_ne]
      ring
    have hright : log (1 + t / (1 - t)) = -log (1 - t) := by
      calc
        log (1 + t / (1 - t)) = log ((1 - t + t) / (1 - t)) := by
          congr
          field_simp [h1mt_ne]
        _ = log ((1 : ℝ) / (1 - t)) := by ring
        _ = log ((1 - t)⁻¹) := by field_simp [h1mt_ne]
        _ = -log (1 - t) := by simpa using log_inv h1mt_ne
    rw [hleft, hright] at h
    linarith

  -- Product bound.
  have hprod_ub : log (1 + t) * log (1 - t) ≤ (2 * t / (t + 2)) * (-(2 * t / (2 - t))) := by
    have hlog1p_nonneg : 0 ≤ log (1 + t) := le_of_lt hlog1p_pos
    have hneg_nonpos : -(2 * t / (2 - t)) ≤ 0 := by
      have : 0 ≤ 2 * t / (2 - t) := by
        refine div_nonneg ?_ ?_
        · positivity
        · linarith
      linarith
    have h1 : log (1 + t) * log (1 - t) ≤ log (1 + t) * (-(2 * t / (2 - t))) :=
      mul_le_mul_of_nonneg_left hlog1m_ub hlog1p_nonneg
    have h2 : log (1 + t) * (-(2 * t / (2 - t))) ≤ (2 * t / (t + 2)) * (-(2 * t / (2 - t))) :=
      mul_le_mul_of_nonpos_right hlog1p_lb hneg_nonpos
    exact le_trans h1 h2

  -- Numerator lower bound: log(1-u) ≥ -u/(1-u), with u = t².
  have hnum_lb : -(t^2) / (1 - t^2) ≤ log (1 - t^2) := by
    have h := one_sub_inv_le_log_of_pos h1mt2_pos
    have hrew : -(t^2) / (1 - t^2) = (1 : ℝ) - 1 / (1 - t^2) := by
      field_simp [ne_of_gt h1mt2_pos]
      ring_nf
    calc
      -(t^2) / (1 - t^2) = (1 : ℝ) - 1 / (1 - t^2) := hrew
      _ ≤ log (1 - t^2) := by simpa [one_div] using h

  rw [symmetricLogComb_alt t ht_pos ht_lt]
  have hmain : (4 / 3 : ℝ) * (log (1 + t) * log (1 - t)) ≤ log (1 - t^2) := by
    have hstep1 : (4 / 3 : ℝ) * (log (1 + t) * log (1 - t))
        ≤ (4 / 3 : ℝ) * ((2 * t / (t + 2)) * (-(2 * t / (2 - t)))) :=
      mul_le_mul_of_nonneg_left hprod_ub (by positivity)
    have hstep2 : (4 / 3 : ℝ) * ((2 * t / (t + 2)) * (-(2 * t / (2 - t)))
        ) ≤ -(t^2) / (1 - t^2) := by
      have h2mt_ne : 2 - t ≠ 0 := by linarith
      have htp2_ne : t + 2 ≠ 0 := by linarith
      have hrew : (4 / 3 : ℝ) * ((2 * t / (t + 2)) * (-(2 * t / (2 - t))))
          = -(16 * t^2) / (3 * ((t + 2) * (2 - t))) := by
        field_simp [h2mt_ne, htp2_ne]
        ring
      rw [hrew]
      have hcoef : 1 / (1 - t^2) ≤ 16 / (3 * ((t + 2) * (2 - t))) := by
        have hA : 0 < 3 * ((t + 2) * (2 - t)) := by nlinarith
        have hAB : 3 * ((t + 2) * (2 - t)) ≤ 16 * (1 - t^2) := by nlinarith [ht_le]
        have hrecip : 1 / (16 * (1 - t^2)) ≤ 1 / (3 * ((t + 2) * (2 - t))) :=
          one_div_le_one_div_of_le hA hAB
        have hmul := mul_le_mul_of_nonneg_left hrecip (by norm_num : (0 : ℝ) ≤ 16)
        have h1mt2_ne : (1 - t^2) ≠ 0 := by nlinarith
        have hleft : 16 * (1 / (16 * (1 - t^2))) = 1 / (1 - t^2) := by
          field_simp [h1mt2_ne]
        have hright : 16 * (1 / (3 * ((t + 2) * (2 - t)))) = 16 / (3 * ((t + 2) * (2 - t))) := by
          ring
        calc
          1 / (1 - t^2) = 16 * (1 / (16 * (1 - t^2))) := by symm; exact hleft
          _ ≤ 16 * (1 / (3 * ((t + 2) * (2 - t)))) := hmul
          _ = 16 / (3 * ((t + 2) * (2 - t))) := hright
      have ht2_nonneg : 0 ≤ t^2 := sq_nonneg t
      have hmul : t^2 / (1 - t^2) ≤ (16 * t^2) / (3 * ((t + 2) * (2 - t))) := by
        have hmul' := mul_le_mul_of_nonneg_left hcoef ht2_nonneg
        simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hmul'
      have hneg : -(16 * t^2 / (3 * ((t + 2) * (2 - t)))) ≤ -(t^2 / (1 - t^2)) := neg_le_neg hmul
      simpa [neg_div] using hneg
    exact le_trans hstep1 (le_trans hstep2 hnum_lb)
  exact (div_le_iff_of_neg hden_neg).2 hmain

/-! ## Limit theorems for the symmetric combination -/

/-- Helper: log(1+t)/t → 1 as t → 0⁺.
    This follows from log'(1) = 1. -/
theorem tendsto_log_one_add_div_self :
    Filter.Tendsto (fun t => log (1 + t) / t) (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
  have hderiv : HasDerivAt log 1 1 := by
    have h := hasDerivAt_log (one_ne_zero)
    simp only [inv_one] at h
    exact h
  have htendsto := hderiv.tendsto_slope_zero_right
  simp only [log_one, sub_zero, smul_eq_mul, inv_mul_eq_div] at htendsto
  exact htendsto

/-- Helper: log(1-t)/t → -1 as t → 0⁺. -/
theorem tendsto_log_one_sub_div_self :
    Filter.Tendsto (fun t => log (1 - t) / t) (nhdsWithin 0 (Set.Ioi 0)) (nhds (-1)) := by
  have hderiv : HasDerivAt (fun x : ℝ => log (1 - x)) (-1) 0 := by
    have hlog : HasDerivAt log 1 1 := by simpa using hasDerivAt_log (one_ne_zero)
    have hneg : HasDerivAt (fun x : ℝ => 1 - x) (-1) 0 := by
      simpa using (hasDerivAt_const (0 : ℝ) (1 : ℝ)).sub (hasDerivAt_id 0)
    have hlog' : HasDerivAt log 1 (1 - 0) := by simp only [sub_zero]; exact hlog
    simpa using hlog'.comp 0 hneg
  have htendsto := hderiv.tendsto_slope_zero_right
  simp only [sub_zero, log_one, smul_eq_mul, inv_mul_eq_div] at htendsto
  convert htendsto using 2 with t
  ring

/-- Helper: log(1-t²)/t² → -1 as t → 0⁺. -/
theorem tendsto_log_one_sub_sq_div_sq :
    Filter.Tendsto (fun t => log (1 - t^2) / t^2) (nhdsWithin 0 (Set.Ioi 0)) (nhds (-1)) := by
  have h := tendsto_log_one_sub_div_self
  have hsq : Filter.Tendsto (fun t : ℝ => t^2) (nhdsWithin 0 (Set.Ioi 0)) (nhdsWithin 0 (Set.Ioi 0)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have h0 : Filter.Tendsto (fun t : ℝ => t) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) :=
        (continuous_id.tendsto 0).mono_left nhdsWithin_le_nhds
      simp only [sq]
      have hmul := h0.mul h0
      simp only [mul_zero] at hmul
      exact hmul
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact sq_pos_of_pos (Set.mem_Ioi.mp ht)
  exact h.comp hsq

/-- The symmetric combination approaches 1 as t → 0⁺.
    More precisely: g(t) → 1 as t → 0⁺.

    **Proof:** Rewrite g(t) using the alternative form:
      g(t) = log(1-t²)/(log(1+t)·log(1-t))
           = [log(1-t²)/t²] / [(log(1+t)/t) · (log(1-t)/t)]
    As t → 0⁺:
      - log(1-t²)/t² → -1
      - log(1+t)/t → 1
      - log(1-t)/t → -1
    So g(t) → (-1) / (1 · (-1)) = 1. -/
theorem symmetricLogComb_tendsto_one :
    Filter.Tendsto symmetricLogComb (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
  -- Use the alternative form for t ∈ (0, 1)
  have heventually : ∀ᶠ t in nhdsWithin 0 (Set.Ioi 0), symmetricLogComb t =
      log (1 - t^2) / (log (1 + t) * log (1 - t)) := by
    rw [Filter.eventually_iff_exists_mem]
    use Set.Ioo 0 1
    constructor
    · rw [mem_nhdsWithin]
      use Set.Iio 1
      refine ⟨isOpen_Iio, ?_, ?_⟩
      · norm_num
      · intro x ⟨hx1, hx2⟩
        exact ⟨hx2, hx1⟩
    · intro t ht
      exact symmetricLogComb_alt t ht.1 ht.2
  apply Filter.Tendsto.congr' (Filter.EventuallyEq.symm heventually)
  -- Rewrite as ratio: [log(1-t²)/t²] / [(log(1+t)/t) · (log(1-t)/t)]
  have hrewrite : ∀ᶠ t in nhdsWithin 0 (Set.Ioi 0),
      log (1 - t^2) / (log (1 + t) * log (1 - t)) =
      (log (1 - t^2) / t^2) / ((log (1 + t) / t) * (log (1 - t) / t)) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht_ne : t ≠ 0 := ne_of_gt ht
    field_simp
  apply Filter.Tendsto.congr' (Filter.EventuallyEq.symm hrewrite)
  -- Apply the limits
  have h1 := tendsto_log_one_sub_sq_div_sq  -- log(1-t²)/t² → -1
  have h2 := tendsto_log_one_add_div_self   -- log(1+t)/t → 1
  have h3 := tendsto_log_one_sub_div_self   -- log(1-t)/t → -1
  -- The product (log(1+t)/t) * (log(1-t)/t) → 1 * (-1) = -1
  have hprod : Filter.Tendsto (fun t => (log (1 + t) / t) * (log (1 - t) / t))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (-1)) := by
    have := h2.mul h3
    simp only [one_mul] at this
    exact this
  -- The ratio (-1) / (-1) = 1
  have hdiv : Filter.Tendsto (fun t => (log (1 - t^2) / t^2) /
      ((log (1 + t) / t) * (log (1 - t) / t)))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
    have hne : (-1 : ℝ) ≠ 0 := by norm_num
    have := h1.div hprod hne
    simp only [neg_div_neg_eq] at this
    convert this using 1
    norm_num
  exact hdiv

end LeanCert.Core
