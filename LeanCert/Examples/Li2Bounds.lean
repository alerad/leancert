/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Engine.TaylorModel.Log1p
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Li(2) Bounds - Lightweight Interface

This file provides the lightweight interface for li(2) bounds. It contains:
- Definitions of g(t) and li(2)
- Analytic lemmas (g_tendsto_one, g_bounded, g_pos, g_le_two, etc.)
- Statements of the certified bounds (proven in Li2Verified.lean)

## Purpose

This module is designed to be fast to compile (~seconds) and is what downstream
projects like PNT+ should import. The heavy numerical verification that proves
the bounds is in Li2Verified.lean, which takes ~20 minutes but is only needed
for LeanCert's CI, not for users of the bounds.

## Main Results

* `g` - The symmetric log combination g(t) = 1/log(1+t) + 1/log(1-t)
* `li2` - Definition of li(2) as ∫₀¹ g(t) dt
* `g_tendsto_one` - g(t) → 1 as t → 0⁺ (removable singularity)
* `g_bounded` - |g(t)| ≤ 2 for t ∈ (0, 1/2)
* `g_pos`, `g_le_two` - Positivity and upper bound on (0, 1)
* `li2_lower` - Lower bound: 1.039 ≤ li(2)
* `li2_upper` - Upper bound: li(2) ≤ 1.06

## Verification Status

The bounds `li2_lower` and `li2_upper` are marked with `sorry` in this file.
They are fully verified via interval arithmetic in `Li2Verified.lean`.
This separation allows downstream projects to use the bounds without
incurring the ~20 minute compilation cost of numerical verification.
-/

open MeasureTheory LeanCert.Engine.TaylorModel
open scoped ENNReal

namespace Li2

/-! ### Core Definitions -/

/-- The symmetric log combination g(t) = 1/log(1+t) + 1/log(1-t).
    This is the integrand for computing li(2). -/
noncomputable def g (t : ℝ) : ℝ := symmetricLogCombination t

/-- li(2) defined as the integral of the symmetric combination on [0, 1].
    This is equivalent to the principal value integral ∫₀² dt/log(t). -/
noncomputable def li2 : ℝ := ∫ t in (0:ℝ)..1, g t

/-! ### Basic Properties -/

/-- The integrand g(t) equals 1/log(1+t) + 1/log(1-t) -/
theorem g_eq (t : ℝ) : g t = 1 / Real.log (1 + t) + 1 / Real.log (1 - t) := rfl

/-- g(t) has an alternative form: log(1-t²)/(log(1+t)·log(1-t)) -/
theorem g_alt (t : ℝ) (ht_pos : 0 < t) (ht_lt : t < 1) :
    g t = Real.log (1 - t^2) / (Real.log (1 + t) * Real.log (1 - t)) :=
  symmetricLogCombination_alt t ht_pos ht_lt

/-- g(t) → 1 as t → 0⁺ (the removable singularity) -/
theorem g_tendsto_one :
    Filter.Tendsto g (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) :=
  symmetricLogCombination_tendsto_one

/-- |g(t)| ≤ 2 for t ∈ (0, 1/2] -/
theorem g_bounded (t : ℝ) (ht_pos : 0 < t) (ht_le : t < 1/2) :
    |g t| ≤ 2 :=
  symmetricLogCombination_bounded t ht_pos ht_le

/-! ### Positivity and Global Upper Bound -/

/-- g(t) > 0 for t ∈ (0, 1). -/
theorem g_pos (t : ℝ) (ht_pos : 0 < t) (ht_lt : t < 1) : 0 < g t := by
  have h1mt2_pos : 0 < 1 - t^2 := by nlinarith [sq_nonneg t]
  have h1mt2_lt1 : 1 - t^2 < 1 := by nlinarith [sq_nonneg t, ht_lt]
  have hlog1mt2_neg : Real.log (1 - t^2) < 0 := Real.log_neg h1mt2_pos h1mt2_lt1
  have h1pt_gt1 : 1 < 1 + t := by linarith
  have h1mt_pos : 0 < 1 - t := by linarith
  have h1mt_lt1 : 1 - t < 1 := by linarith
  have hlog1p_pos : 0 < Real.log (1 + t) := Real.log_pos h1pt_gt1
  have hlog1m_neg : Real.log (1 - t) < 0 := Real.log_neg h1mt_pos h1mt_lt1
  have hdenom_neg : Real.log (1 + t) * Real.log (1 - t) < 0 :=
    mul_neg_of_pos_of_neg hlog1p_pos hlog1m_neg
  have hpos :
      0 < Real.log (1 - t^2) / (Real.log (1 + t) * Real.log (1 - t)) :=
    div_pos_of_neg_of_neg hlog1mt2_neg hdenom_neg
  simpa [g_alt t ht_pos ht_lt] using hpos

/-- g(t) ≤ 2 for t ∈ (0, 1). -/
theorem g_le_two (t : ℝ) (ht_pos : 0 < t) (ht_lt : t < 1) : g t ≤ 2 := by
  have h1pt_pos : 0 < 1 + t := by linarith
  have h1mt_pos : 0 < 1 - t := by linarith
  have h1pt_gt1 : 1 < 1 + t := by linarith
  have h1mt_lt1 : 1 - t < 1 := by linarith
  have hlog1p_pos : 0 < Real.log (1 + t) := Real.log_pos h1pt_gt1
  have hlog1m_neg : Real.log (1 - t) < 0 := Real.log_neg h1mt_pos h1mt_lt1
  have hlog1p_lb : t / (1 + t) ≤ Real.log (1 + t) := by
    have h := Real.one_sub_inv_le_log_of_pos h1pt_pos
    have h' : 1 - 1 / (1 + t) ≤ Real.log (1 + t) := by
      simpa [one_div] using h
    have h1 : t / (1 + t) = 1 - 1 / (1 + t) := by field_simp; ring
    calc t / (1 + t) = 1 - 1 / (1 + t) := h1
      _ ≤ Real.log (1 + t) := h'
  have hlog1m_ub : Real.log (1 - t) ≥ -t / (1 - t) := by
    have h := Real.one_sub_inv_le_log_of_pos h1mt_pos
    have h' : 1 - 1 / (1 - t) ≤ Real.log (1 - t) := by
      simpa [one_div] using h
    have h1 : -t / (1 - t) = 1 - 1 / (1 - t) := by field_simp; ring
    calc -t / (1 - t) = 1 - 1 / (1 - t) := h1
      _ ≤ Real.log (1 - t) := h'
  have hlog1p_inv_ub : 1 / Real.log (1 + t) ≤ (1 + t) / t := by
    rw [one_div, le_div_iff₀ ht_pos, inv_mul_le_iff₀ hlog1p_pos]
    have h1 : t = t / (1 + t) * (1 + t) := by field_simp
    calc t = t / (1 + t) * (1 + t) := h1
      _ ≤ Real.log (1 + t) * (1 + t) := by
        apply mul_le_mul_of_nonneg_right hlog1p_lb (le_of_lt h1pt_pos)
  have hlog1m_inv_ub : 1 / Real.log (1 - t) ≤ -(1 - t) / t := by
    have hneg_log : -Real.log (1 - t) > 0 := neg_pos.mpr hlog1m_neg
    have hneg_log_ub : -Real.log (1 - t) ≤ t / (1 - t) := by
      have h := hlog1m_ub
      have hdiv_neg : -t / (1 - t) = -(t / (1 - t)) := by ring
      rw [hdiv_neg] at h
      linarith
    have hinv_lb : (1 - t) / t ≤ 1 / (-Real.log (1 - t)) := by
      rw [div_le_div_iff₀ ht_pos hneg_log]
      calc (1 - t) * -Real.log (1 - t) = -Real.log (1 - t) * (1 - t) := by ring
        _ ≤ t / (1 - t) * (1 - t) := by
          apply mul_le_mul_of_nonneg_right hneg_log_ub (le_of_lt h1mt_pos)
        _ = t := by field_simp
        _ = 1 * t := by ring
    have hlog1m_ne : Real.log (1 - t) ≠ 0 := ne_of_lt hlog1m_neg
    calc 1 / Real.log (1 - t) = -(1 / -Real.log (1 - t)) := by field_simp [hlog1m_ne]
      _ ≤ -((1 - t) / t) := neg_le_neg hinv_lb
      _ = -(1 - t) / t := by ring
  calc
    g t = 1 / Real.log (1 + t) + 1 / Real.log (1 - t) := by rfl
    _ ≤ (1 + t) / t + (-(1 - t) / t) := add_le_add hlog1p_inv_ub hlog1m_inv_ub
    _ = ((1 + t) - (1 - t)) / t := by ring
    _ = 2 * t / t := by ring
    _ = 2 := by field_simp

/-! ### Integrability -/

/-- g is integrable on [0, 1]. -/
theorem g_intervalIntegrable_full : IntervalIntegrable g volume (0:ℝ) 1 := by
  have hmeas : Measurable g := by
    have hlog1p : Measurable fun t : ℝ => Real.log (1 + t) :=
      Real.measurable_log.comp (measurable_const.add measurable_id)
    have hlog1m : Measurable fun t : ℝ => Real.log (1 - t) :=
      Real.measurable_log.comp (measurable_const.sub measurable_id)
    have hlog1p_inv : Measurable fun t : ℝ => (Real.log (1 + t))⁻¹ := hlog1p.inv
    have hlog1m_inv : Measurable fun t : ℝ => (Real.log (1 - t))⁻¹ := hlog1m.inv
    unfold g
    unfold symmetricLogCombination
    simpa [one_div] using hlog1p_inv.add hlog1m_inv
  have hInt_Ioo : IntegrableOn g (Set.Ioo (0:ℝ) 1) volume := by
    apply Measure.integrableOn_of_bounded
    · exact measure_Ioo_lt_top.ne
    · exact hmeas.aestronglyMeasurable
    · refine (ae_restrict_iff' measurableSet_Ioo).2 ?_
      exact ae_of_all _ (fun t ht =>
        by
          have hpos := g_pos t ht.1 ht.2
          have hle := g_le_two t ht.1 ht.2
          have habs : |g t| = g t := abs_of_pos hpos
          simpa [Real.norm_eq_abs, habs] using hle)
  have hab : (0:ℝ) ≤ 1 := by norm_num
  exact (intervalIntegrable_iff_integrableOn_Ioo_of_le (μ:=volume) (f:=g) hab).2 hInt_Ioo

/-- g is integrable on any closed subinterval of (0, 1). -/
theorem g_intervalIntegrable (a b : ℝ) (ha_pos : 0 < a) (hb_lt : b < 1) (hab : a ≤ b) :
    IntervalIntegrable g volume a b := by
  have hmeas : Measurable g := by
    have hlog1p : Measurable fun t : ℝ => Real.log (1 + t) :=
      Real.measurable_log.comp (measurable_const.add measurable_id)
    have hlog1m : Measurable fun t : ℝ => Real.log (1 - t) :=
      Real.measurable_log.comp (measurable_const.sub measurable_id)
    have hlog1p_inv : Measurable fun t : ℝ => (Real.log (1 + t))⁻¹ := hlog1p.inv
    have hlog1m_inv : Measurable fun t : ℝ => (Real.log (1 - t))⁻¹ := hlog1m.inv
    unfold g symmetricLogCombination
    simpa [one_div] using hlog1p_inv.add hlog1m_inv
  have hInt_Ioo : IntegrableOn g (Set.Ioo a b) volume := by
    apply Measure.integrableOn_of_bounded
    · exact measure_Ioo_lt_top.ne
    · exact hmeas.aestronglyMeasurable
    · refine (ae_restrict_iff' measurableSet_Ioo).2 ?_
      exact ae_of_all _ (fun t ht => by
        have ht_pos : 0 < t := lt_of_lt_of_le ha_pos (le_of_lt ht.1)
        have ht_lt1 : t < 1 := lt_of_lt_of_le ht.2 (le_of_lt hb_lt)
        have hpos := g_pos t ht_pos ht_lt1
        have hle := g_le_two t ht_pos ht_lt1
        have habs : |g t| = g t := abs_of_pos hpos
        simpa [Real.norm_eq_abs, habs] using hle)
  exact (intervalIntegrable_iff_integrableOn_Ioo_of_le hab).2 hInt_Ioo

/-! ### Crude Bounds (Analytic) -/

/-- Crude upper bound: li(2) ≤ 2.
    This follows from g(t) ≤ 2 on (0, 1). -/
theorem li2_upper_crude : li2 ≤ 2 := by
  have hInt := g_intervalIntegrable_full
  have hInt_const : IntervalIntegrable (fun _ : ℝ => (2:ℝ)) volume (0:ℝ) 1 :=
    intervalIntegrable_const
  have hab : (0:ℝ) ≤ 1 := by norm_num
  have hmono : ∀ t ∈ Set.Ioo (0:ℝ) 1, g t ≤ (2:ℝ) := by
    intro t ht
    exact g_le_two t ht.1 ht.2
  have hle :=
    intervalIntegral.integral_mono_on_of_le_Ioo (μ:=volume) (a:=0) (b:=1)
      (f:=g) (g:=fun _ : ℝ => (2:ℝ)) (hab:=hab) (hf:=hInt) (hg:=hInt_const) hmono
  have hconst : (∫ t in (0:ℝ)..1, (2:ℝ)) = 2 := by
    simp [intervalIntegral.integral_const]
  simpa [li2, hconst] using hle

/-- li(2) > 0. -/
theorem li2_pos : 0 < li2 := by
  have hInt := g_intervalIntegrable_full
  have hpos : ∀ t ∈ Set.Ioo (0:ℝ) 1, 0 < g t := by
    intro t ht
    exact g_pos t ht.1 ht.2
  have hlt : (0:ℝ) < 1 := by norm_num
  have h :=
    intervalIntegral.intervalIntegral_pos_of_pos_on (f:=g) (a:=0) (b:=1) hInt hpos hlt
  simpa [li2] using h

/-! ### Certified Bounds

The following bounds are proven via interval arithmetic in Li2Verified.lean.
They are stated here with `sorry` to allow downstream projects to use them
without incurring the ~20 minute compilation cost of numerical verification.

The actual verification uses:
- Partition of [0, 1] into 7 subintervals
- Taylor model integration with 3000 partitions on [1/1000, 999/1000]
- Analytic bounds on tail intervals near 0 and 1

Sum of verified lower bounds: 1.03951 > 1.039
Sum of verified upper bounds: 1.0524 < 1.06
-/

/-- Certified lower bound: li(2) ≥ 1.039.
    Proven via interval arithmetic in Li2Verified.lean. -/
theorem li2_lower : (1039:ℚ)/1000 ≤ li2 := by
  sorry

/-- Certified upper bound: li(2) ≤ 1.06.
    Proven via interval arithmetic in Li2Verified.lean. -/
theorem li2_upper : li2 ≤ (106:ℚ)/100 := by
  sorry

/-- Combined bounds: li(2) ∈ [1.039, 1.06]. -/
theorem li2_bounds : (1039:ℚ)/1000 ≤ li2 ∧ li2 ≤ (106:ℚ)/100 :=
  ⟨li2_lower, li2_upper⟩

/-- li(2) is approximately 1.045 (the Ramanujan-Soldner constant).
    Our bounds show: |li(2) - 1.045| ≤ 0.015 -/
theorem li2_approx_1045 : |li2 - (1045:ℚ)/1000| ≤ (15:ℚ)/1000 := by
  have ⟨hlo, hhi⟩ := li2_bounds
  rw [abs_le]
  constructor
  · linarith
  · linarith

end Li2
