/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Analysis.DBN.DobnerGammaBounds
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv

/-! Coarse reciprocal Gamma bounds from reflection and recurrence.
These control division by a small normalization, not saddle-point errors. -/
namespace LeanCert.Analysis.DBN
open Complex Set

private theorem norm_sin_le_exp_abs_im (z : ℂ) :
    ‖Complex.sin z‖ ≤ Real.exp |z.im| := by
  have hp : Real.exp (z * I).re ≤ Real.exp |z.im| := by
    apply Real.exp_le_exp.mpr
    simpa using neg_le_abs z.im
  have hm : Real.exp (-(z * I)).re ≤ Real.exp |z.im| := by
    apply Real.exp_le_exp.mpr
    simpa using le_abs_self z.im
  unfold Complex.sin
  simp only [norm_div, norm_mul, norm_I, Complex.norm_ofNat, mul_one]
  have h := norm_sub_le (Complex.exp (-(z * I))) (Complex.exp (z * I))
  simp only [Complex.norm_exp] at h
  simp only [neg_mul] at *
  nlinarith

private theorem Gamma_ne_zero_of_im_ne_zero {s : ℂ} (hs : s.im ≠ 0) :
    Complex.Gamma s ≠ 0 := by
  apply Complex.Gamma_ne_zero
  intro n hn
  apply hs
  simp [hn]

/-- Reflection gives exponential control without a sectorial Stirling theorem. -/
theorem norm_inv_Gamma_le_reflection {s : ℂ} (hre : s.re < 1) (him : s.im ≠ 0) :
    ‖(Complex.Gamma s)⁻¹‖ ≤
      Real.Gamma (1-s.re) * Real.exp (Real.pi*|s.im|) / Real.pi := by
  have hG := Gamma_ne_zero_of_im_ne_zero him
  have hG' := Complex.Gamma_ne_zero_of_re_pos (s := 1-s) (by simpa using sub_pos.mpr hre)
  have hr := Complex.Gamma_mul_Gamma_one_sub s
  have hsin : Complex.sin (Real.pi*s) ≠ 0 := by
    intro h
    rw [h, div_zero] at hr
    exact (mul_ne_zero hG hG') hr
  have he : (Complex.Gamma s)⁻¹ =
      Complex.Gamma (1-s)*Complex.sin (Real.pi*s)/Real.pi := by
    have hr' := (eq_div_iff hsin).mp hr
    apply (eq_div_iff (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)).mpr
    apply mul_left_cancel₀ hG
    calc
      Complex.Gamma s * ((Complex.Gamma s)⁻¹ * Real.pi) = Real.pi := by
        rw [← mul_assoc, mul_inv_cancel₀ hG, one_mul]
      _ = Complex.Gamma s * (Complex.Gamma (1-s)*Complex.sin (Real.pi*s)) := by
        linear_combination -hr'
  rw [he, norm_div, norm_mul, Complex.norm_of_nonneg Real.pi_pos.le]
  apply div_le_div_of_nonneg_right _ Real.pi_pos.le
  apply mul_le_mul
  · simpa using norm_Gamma_le_real_Gamma (s := 1-s) (by simpa using sub_pos.mpr hre)
  · simpa [abs_mul, abs_of_pos Real.pi_pos] using norm_sin_le_exp_abs_im (Real.pi*s)
  · exact norm_nonneg _
  · exact (Real.Gamma_pos_of_pos (sub_pos.mpr hre)).le

/-- Moving Gamma's argument right cannot increase its reciprocal norm when
its imaginary part has magnitude at least one. -/
theorem norm_inv_Gamma_add_nat_le (s : ℂ) (n : ℕ) (hs : 1 ≤ |s.im|) :
    ‖(Complex.Gamma (s+n))⁻¹‖ ≤ ‖(Complex.Gamma s)⁻¹‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hn : 1 ≤ ‖s+n‖ := by
      have := Complex.abs_im_le_norm (s+n)
      simp only [add_im, natCast_im, add_zero] at this
      exact hs.trans this
    have hz : s+(n : ℂ) ≠ 0 := by
      intro h
      norm_num [h] at hn
    rw [Nat.cast_succ, ← add_assoc, Complex.Gamma_add_one _ hz, mul_inv, norm_mul]
    calc
      ‖(s+(n : ℂ))⁻¹‖ * ‖(Complex.Gamma (s+n))⁻¹‖ ≤
          1 * ‖(Complex.Gamma (s+n))⁻¹‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        rw [norm_inv]
        exact inv_le_one_of_one_le₀ hn
      _ ≤ _ := by simpa using ih

/-- A uniform exponential reciprocal bound on every fixed vertical strip.
No complex Stirling asymptotic is needed for this coarse estimate. -/
theorem norm_inv_Gamma_le_exp_on_strip (M : ℝ) (_hM : 0 ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, |s.re| ≤ M → 1 ≤ |s.im| →
      ‖(Complex.Gamma s)⁻¹‖ ≤ C * Real.exp (Real.pi*|s.im|) := by
  obtain ⟨N, hN⟩ := exists_nat_gt M
  have hc : ContinuousOn Real.Gamma (Icc 1 (1+2*(N : ℝ))) :=
    Real.differentiableOn_Gamma_Ioi.continuousOn.mono (by
      intro x hx
      exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hx.1)
  obtain ⟨B, hB⟩ := isCompact_Icc.bddAbove_image hc
  refine ⟨(|B|+1)/Real.pi, by positivity, ?_⟩
  intro s hre him
  have hx := abs_le.mp hre
  have hz : (s-(N : ℂ)).re < 1 := by simp; linarith
  have hi : (s-(N : ℂ)).im ≠ 0 := by
    simp only [sub_im, natCast_im, sub_zero]
    intro h
    norm_num [h] at him
  have hb : Real.Gamma (1-(s-(N : ℂ)).re) ≤ |B|+1 := by
    have hmem : 1-(s-(N : ℂ)).re ∈ Icc 1 (1+2*(N : ℝ)) := by
      simp only [mem_Icc, sub_re, natCast_re]
      constructor <;> linarith
    have := hB (mem_image_of_mem Real.Gamma hmem)
    linarith [le_abs_self B]
  calc
    ‖(Complex.Gamma s)⁻¹‖ ≤ ‖(Complex.Gamma (s-(N : ℂ)))⁻¹‖ := by
      simpa using norm_inv_Gamma_add_nat_le (s-(N : ℂ)) N (by simpa using him)
    _ ≤ Real.Gamma (1-(s-(N : ℂ)).re) *
        Real.exp (Real.pi*|(s-(N : ℂ)).im|) / Real.pi :=
      norm_inv_Gamma_le_reflection hz hi
    _ ≤ (|B|+1) * Real.exp (Real.pi*|s.im|) / Real.pi := by
      simp only [sub_im, natCast_im, sub_zero]
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hb (Real.exp_pos _).le) Real.pi_pos.le
    _ = _ := by ring

/-- The logarithmic chart's Gaussian correction has bounded reciprocal norm.
The bound is uniform in the argument, including its height. -/
theorem norm_inv_dobnerGamma_le (a : ℝ) (ha : 0 < a) (s : ℂ) :
    ‖(dobnerGamma a s)⁻¹‖ ≤
      ‖(xiGamma s)⁻¹‖ * Real.exp (a*Real.pi^2/4) := by
  let l := Complex.log (s/(2*Real.pi))
  have he : (s-dobnerMap a s)^2/(4*(a : ℂ)) = (a : ℂ)/4*l^2 := by
    dsimp [dobnerMap, l]
    field_simp [Complex.ofReal_ne_zero.mpr ha.ne']
    ring
  have hb : l.im^2 ≤ Real.pi^2 := by
    have h := Complex.abs_arg_le_pi (s/(2*Real.pi))
    have hl : l.im = Complex.arg (s/(2*Real.pi)) := Complex.log_im _
    rw [← hl] at h
    nlinarith [sq_abs l.im, abs_nonneg l.im, Real.pi_pos]
  have hr : -((a : ℂ)/4*l^2).re ≤ a*Real.pi^2/4 := by
    simp only [mul_re, div_ofNat_re, div_ofNat_im, ofReal_re, ofReal_im,
      zero_div, zero_mul, sub_zero, pow_two]
    nlinarith [mul_nonneg ha.le (sq_nonneg l.re), mul_le_mul_of_nonneg_left hb ha.le]
  simp only [dobnerGamma, mul_inv, norm_mul, he, norm_inv, Complex.norm_exp,
    ← Real.exp_neg]
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hr) (inv_nonneg.mpr (norm_nonneg _))

/-- Reciprocal control of the polynomial and pi factors in the xi completion. -/
theorem norm_inv_xiGamma_le {s : ℂ} (hs : 1 ≤ |s.im|) :
    ‖(xiGamma s)⁻¹‖ ≤
      2 * Real.pi^(s.re/2) * ‖(Complex.Gamma (s/2))⁻¹‖ := by
  have h0 : 1 ≤ ‖s‖ := hs.trans (Complex.abs_im_le_norm s)
  have h1 : 1 ≤ ‖s-1‖ := by
    have h := Complex.abs_im_le_norm (s-1)
    simp only [sub_im, one_im, sub_zero] at h
    exact hs.trans h
  have hp : ‖((Real.pi : ℂ)^(-s/2))⁻¹‖ = Real.pi^(s.re/2) := by
    rw [norm_inv, Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
    simp only [div_ofNat_re, neg_re]
    rw [neg_div, Real.rpow_neg Real.pi_pos.le, inv_inv]
  have hz : ‖s⁻¹‖ ≤ 1 := by rw [norm_inv]; exact inv_le_one_of_one_le₀ h0
  have hz' : ‖(s-1)⁻¹‖ ≤ 1 := by rw [norm_inv]; exact inv_le_one_of_one_le₀ h1
  have hprod : ‖s⁻¹‖ * ‖(s-1)⁻¹‖ ≤ 1 := by
    nlinarith [norm_nonneg s⁻¹, norm_nonneg (s-1)⁻¹]
  rw [xiGamma, Gammaℝ_def, inv_div, div_eq_mul_inv]
  simp only [mul_inv, norm_mul, Complex.norm_ofNat, hp]
  nlinarith [mul_le_mul_of_nonneg_right hprod
    (mul_nonneg (Real.rpow_nonneg Real.pi_pos.le (s.re/2)) (norm_nonneg (Complex.Gamma (s/2))⁻¹))]

/-- The actual Dobner normalization has at most exponential reciprocal growth
on each fixed strip. This discharges the normalization loss in a future
large-index Gaussian-tail estimate; it is not the approximation theorem. -/
theorem norm_inv_dobnerGamma_le_exp_on_strip (a : ℝ) (ha : 0 < a)
    (M : ℝ) (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, |s.re| ≤ M → 2 ≤ s.im →
      ‖(dobnerGamma a s)⁻¹‖ ≤ C * Real.exp (Real.pi*s.im/2) := by
  obtain ⟨B, hB, hb⟩ := norm_inv_Gamma_le_exp_on_strip (M/2) (by positivity)
  refine ⟨2 * Real.pi^(M/2) * B * Real.exp (a*Real.pi^2/4), by positivity, ?_⟩
  intro s hre him
  have him' : 1 ≤ |s.im| := by rw [abs_of_nonneg (by linarith)]; linarith
  have hg : ‖(Complex.Gamma (s/2))⁻¹‖ ≤ B * Real.exp (Real.pi*s.im/2) := by
    have h := hb (s/2) (by simpa [abs_div] using (div_le_div_of_nonneg_right hre (by norm_num : (0 : ℝ) ≤ 2)))
      (by simp [abs_div, abs_of_nonneg (by linarith : 0 ≤ s.im)]; linarith)
    simpa [abs_div, abs_of_nonneg (by linarith : 0 ≤ s.im), mul_div_assoc] using h
  have hp : Real.pi^(s.re/2) ≤ Real.pi^(M/2) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith [Real.pi_gt_three])
      (div_le_div_of_nonneg_right ((le_abs_self s.re).trans hre) (by norm_num))
  calc
    ‖(dobnerGamma a s)⁻¹‖ ≤ ‖(xiGamma s)⁻¹‖ * Real.exp (a*Real.pi^2/4) :=
      norm_inv_dobnerGamma_le a ha s
    _ ≤ (2 * Real.pi^(s.re/2) * ‖(Complex.Gamma (s/2))⁻¹‖) *
        Real.exp (a*Real.pi^2/4) :=
      mul_le_mul_of_nonneg_right (norm_inv_xiGamma_le him') (Real.exp_pos _).le
    _ ≤ (2 * Real.pi^(M/2) * (B * Real.exp (Real.pi*s.im/2))) *
        Real.exp (a*Real.pi^2/4) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      exact mul_le_mul (mul_le_mul_of_nonneg_left hp (by norm_num)) hg
        (norm_nonneg _) (by positivity)
    _ = _ := by ring

end LeanCert.Analysis.DBN
