/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Analysis.ContourShift
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-! Holomorphic constructors and a bridge to actual integrable vertical lines. -/
namespace LeanCert.Analysis.ContourShift
open Complex MeasureTheory Filter Set
open scoped Topology

/-- Zero-residue rectangle constructor, with either horizontal orientation. -/
def RectangleShiftCert.ofHolomorphicStrip (F : ℂ → ℂ) (σ₀ σ₁ T : ℝ)
    (hF : ∀ z : ℂ, z.re ∈ uIcc σ₀ σ₁ → DifferentiableAt ℂ F z) :
    RectangleShiftCert F σ₀ σ₁ T where
  poles := ∅
  residue := fun _ => 0
  rectangle_identity := by
    have hc : ContinuousOn F (uIcc σ₀ σ₁ ×ℂ uIcc (-T) T) := by
      intro z hz
      exact (hF z hz.1).continuousAt.continuousWithinAt
    have hd : DifferentiableOn ℂ F
        (Ioo (min σ₀ σ₁) (max σ₀ σ₁) ×ℂ Ioo (min (-T) T) (max (-T) T)) := by
      intro z hz
      exact (hF z ⟨hz.1.1.le, hz.1.2.le⟩).differentiableWithinAt
    have h := rectBoundary_eq_zero_of_continuousOn_of_differentiableOn F
      ((σ₀ : ℂ)-(T : ℂ)*I) ((σ₁ : ℂ)+(T : ℂ)*I)
      (by simpa using hc) (by simpa using hd)
    simp only [rectBoundary, bottomIntegral, topIntegral, leftIntegral, rightIntegral,
      sub_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero, sub_zero,
      add_re, add_zero, sub_im, mul_im, mul_one, zero_sub, add_im] at h
    simp only [verticalIntegral, topHorizontalIntegral, bottomHorizontalIntegral,
      Finset.sum_empty, mul_zero, add_zero, intervalIntegral.integral_mul_const]
    rw [intervalIntegral.integral_symm σ₀ σ₁]
    simp only [zero_add, ofReal_neg, ← neg_mul, sub_eq_add_neg] at h ⊢
    linear_combination -h

/-- A uniform decaying strip bound controls both horizontal sides. -/
def horizontalBoundOfStrip (F : ℂ → ℂ) (σ₀ σ₁ : ℝ) (T : ℕ → ℝ)
    (b : ℕ → ℝ) (hb : ∀ n, 0 ≤ b n) (hlim : Tendsto b atTop (𝓝 0))
    (hbound : ∀ n x, x ∈ uIcc σ₀ σ₁ →
      ‖F ((x : ℂ)+(T n : ℂ)*I)‖ ≤ b n ∧
      ‖F ((x : ℂ)-(T n : ℂ)*I)‖ ≤ b n) :
    HorizontalBoundCert F σ₀ σ₁ T where
  bound n := b n * |σ₁-σ₀|
  bound_nonneg n := mul_nonneg (hb n) (abs_nonneg _)
  bound_tendsto_zero := by simpa using hlim.mul_const |σ₁-σ₀|
  top_norm_le n := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro x hx
    exact (hbound n x (uIoc_subset_uIcc hx)).1
  bottom_norm_le n := by
    unfold bottomHorizontalIntegral
    rw [intervalIntegral.integral_symm σ₀ σ₁, norm_neg]
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro x hx
    exact (hbound n x (uIoc_subset_uIcc hx)).2

/-- The certificate's limits are actual Lebesgue integrals when the two
vertical parameterizations are integrable. -/
theorem integral_vertical_eq_of_holomorphic_of_vanish
    (F : ℂ → ℂ) (σ₀ σ₁ : ℝ)
    (hF : ∀ z : ℂ, z.re ∈ uIcc σ₀ σ₁ → DifferentiableAt ℂ F z)
    (h₀ : Integrable (fun y : ℝ => F ((σ₀ : ℂ)+(y : ℂ)*I)))
    (h₁ : Integrable (fun y : ℝ => F ((σ₁ : ℂ)+(y : ℂ)*I)))
    (hvan : HorizontalVanishCert F σ₀ σ₁ (fun n => (n : ℝ)+1)) :
    (∫ y : ℝ, F ((σ₀ : ℂ)+(y : ℂ)*I)) =
      ∫ y : ℝ, F ((σ₁ : ℂ)+(y : ℂ)*I) := by
  have ht : Tendsto (fun n : ℕ => (n : ℝ)+1) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  have hl (σ : ℝ) (hi : Integrable (fun y : ℝ => F ((σ : ℂ)+(y : ℂ)*I))) :
      Tendsto (fun n : ℕ => verticalIntegral F σ ((n : ℝ)+1)) atTop
        (𝓝 ((∫ y : ℝ, F ((σ : ℂ)+(y : ℂ)*I))*I)) := by
    simpa only [verticalIntegral, integral_mul_const, Function.comp_apply] using
      intervalIntegral_tendsto_integral (hi.mul_const I) (tendsto_neg_atTop_atBot.comp ht) ht
  let C : ContourShiftCert F σ₀ σ₁ := {
    T := fun n => (n : ℝ)+1
    hT_pos := fun n => by positivity
    hT_tendsto := ht
    poles := ∅
    residue := fun _ => 0
    rectCert := fun n => RectangleShiftCert.ofHolomorphicStrip F σ₀ σ₁ ((n : ℝ)+1) hF
    same_poles := fun _ => rfl
    same_residue := fun _ _ => rfl
    left_limit := ⟨_, hl σ₀ h₀⟩
    right_limit := ⟨_, hl σ₁ h₁⟩
    horizontal := hvan }
  obtain ⟨L₀, L₁, hL₀, hL₁, he⟩ := C.shift_identity
  have e₀ := tendsto_nhds_unique hL₀ (hl σ₀ h₀)
  have e₁ := tendsto_nhds_unique hL₁ (hl σ₁ h₁)
  simp only [e₀, e₁, ContourShiftCert.residueSum, C, Finset.sum_empty,
    mul_zero, add_zero] at he
  exact mul_right_cancel₀ I_ne_zero he

end LeanCert.Analysis.ContourShift
