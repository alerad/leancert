/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Analysis.DBN.DobnerDirichlet
import LeanCert.Analysis.DBN.DobnerGammaReciprocal
import LeanCert.Analysis.ContourShift.Decay
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Actual Gaussian-Gamma contour shifts in the pole-free right half-plane.
These exact shifts do not assert the saddle-point approximation. -/
namespace LeanCert.Analysis.DBN
open Complex MeasureTheory Set Filter
open scoped Topology

/-- The integrand of each DBN Dirichlet contour coefficient; `L=log n`. -/
noncomputable def saddleIntegrand (b : ℝ) (w : ℂ) (L : ℝ) (z : ℂ) : ℂ :=
  Complex.exp ((w-z)^2/(b : ℂ)) * xiGamma z * Complex.exp (-z*(L : ℂ))

/-- On the right half-plane the Gamma prefactor is holomorphic even on the
real axis. This is separate from its upper-half-plane holomorphy. -/
theorem differentiableAt_xiGamma_of_re_pos {z : ℂ} (hz : 0 < z.re) :
    DifferentiableAt ℂ xiGamma z := by
  have hg : DifferentiableAt ℂ Gammaℝ z := by
    have h := (differentiable_Gammaℝ_inv z).inv
      (inv_ne_zero (Gammaℝ_ne_zero_of_re_pos hz))
    change DifferentiableAt ℂ (fun w => ((Gammaℝ w)⁻¹)⁻¹) z at h
    simpa only [inv_inv] using h
  unfold xiGamma
  fun_prop

theorem differentiableAt_saddleIntegrand (b : ℝ) (w : ℂ) (L : ℝ)
    {z : ℂ} (hz : 0 < z.re) : DifferentiableAt ℂ (saddleIntegrand b w L) z := by
  have := differentiableAt_xiGamma_of_re_pos hz
  unfold saddleIntegrand
  fun_prop

private theorem norm_xiGamma_le_strip_poly {z : ℂ} (hz : 0 < z.re) :
    ‖xiGamma z‖ ≤ (|z.re|+1)^2*(1+z.im^2)*
      (Real.pi^(-z.re/2)*Real.Gamma (z.re/2)) := by
  have hg := norm_Gamma_le_real_Gamma (s := z/2) (by simp; linarith)
  have hp : ‖(Real.pi : ℂ)^(-z/2)‖ = Real.pi^(-z.re/2) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
    simp
  have hn := norm_le_abs_re_add_abs_im z
  have hn' : ‖z-1‖ ≤ ‖z‖+1 := by simpa using norm_sub_le z (1 : ℂ)
  have hpoly : ‖z‖*‖z-1‖ ≤ 2*(|z.re|+1)^2*(1+z.im^2) := by
    have hsq : (‖z‖+1)^2 ≤ 2*(|z.re|+1)^2 + 2*z.im^2 := by
      nlinarith [sq_nonneg (|z.re|+1-|z.im|), sq_abs z.im, norm_nonneg z,
        abs_nonneg z.re, abs_nonneg z.im]
    have hh : 1 ≤ (|z.re|+1)^2 := by nlinarith [abs_nonneg z.re]
    nlinarith [norm_nonneg z, norm_nonneg (z-1),
      mul_nonneg (sub_nonneg.mpr hh) (sq_nonneg z.im)]
  have hg' : ‖Gammaℝ z‖ ≤ Real.pi^(-z.re/2)*Real.Gamma (z.re/2) := by
    rw [Gammaℝ_def, norm_mul, hp]
    exact mul_le_mul_of_nonneg_left (by simpa using hg) (by positivity)
  rw [xiGamma, norm_div, norm_mul, norm_mul]
  norm_num only [Complex.norm_ofNat]
  have h := mul_le_mul hpoly hg' (norm_nonneg _) (by positivity)
  nlinarith

private theorem saddle_exp_norm_bound (b : ℝ) (hb : 0 < b) (w z : ℂ) (L : ℝ) :
    ‖Complex.exp ((w-z)^2/(b : ℂ))‖ * ‖Complex.exp (-z*(L : ℂ))‖ ≤
      Real.exp ((w.re-z.re)^2/b+w.im^2/b-z.re*L) * Real.exp (-z.im^2/(2*b)) := by
  rw [Complex.norm_exp, Complex.norm_exp, ← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  simp only [div_ofReal_re, pow_two, mul_re, sub_re, sub_im, neg_re, ofReal_re,
    neg_im, ofReal_im, mul_zero, sub_zero]
  have h := mul_nonneg (sq_nonneg (z.im-2*w.im)) (inv_nonneg.mpr hb.le)
  field_simp
  nlinarith

private noncomputable def saddleStripCoeff (b : ℝ) (w : ℂ) (L x : ℝ) : ℝ :=
  (|x|+1)^2*(Real.pi^(-x/2)*Real.Gamma (x/2))*
    Real.exp ((w.re-x)^2/b+w.im^2/b-x*L)

private theorem norm_saddleIntegrand_le (b : ℝ) (hb : 0 < b) (w : ℂ) (L : ℝ)
    {z : ℂ} (hz : 0 < z.re) :
    ‖saddleIntegrand b w L z‖ ≤
      saddleStripCoeff b w L z.re * (1+z.im^2) * Real.exp (-z.im^2/(2*b)) := by
  have h := mul_le_mul (norm_xiGamma_le_strip_poly hz)
    (saddle_exp_norm_bound b hb w z L)
    (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (by positivity)
  calc
    ‖saddleIntegrand b w L z‖ = ‖xiGamma z‖ *
        (‖Complex.exp ((w-z)^2/(b : ℂ))‖ * ‖Complex.exp (-z*(L : ℂ))‖) := by
      simp only [saddleIntegrand, norm_mul]
      ring
    _ ≤ _ := h
    _ = saddleStripCoeff b w L z.re * (1+z.im^2) * Real.exp (-z.im^2/(2*b)) := by
      unfold saddleStripCoeff
      ring

/-- A fixed-strip Gaussian majorant for the actual contour integrand.
Constants may depend on the strip, heat parameter, center, and Dirichlet index. -/
theorem saddleIntegrand_strip_bound (b : ℝ) (hb : 0 < b) (w : ℂ) (L p q : ℝ)
    (hp : 0 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, z.re ∈ Icc p q →
      ‖saddleIntegrand b w L z‖ ≤ C*(1+z.im^2)*Real.exp (-z.im^2/(2*b)) := by
  have hc : ContinuousOn (saddleStripCoeff b w L) (Icc p q) := by
    intro x hx
    have hx' : 0 < x/2 := by linarith [hx.1]
    have hg : ContinuousAt Real.Gamma (x/2) :=
      (Real.differentiableAt_Gamma (fun n => by
        have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        intro h
        linarith)).continuousAt
    have hg' : ContinuousAt (fun u : ℝ => Real.Gamma (u/2)) x :=
      hg.comp (f := fun u : ℝ => u/2) (by fun_prop)
    have hr : ContinuousAt (fun u : ℝ => Real.pi^(-u/2)) x :=
      (Real.continuousAt_const_rpow Real.pi_ne_zero).comp
        (f := fun u : ℝ => -u/2) (by fun_prop)
    apply ContinuousAt.continuousWithinAt
    unfold saddleStripCoeff
    fun_prop
  obtain ⟨B, hB⟩ := isCompact_Icc.bddAbove_image hc
  refine ⟨|B|+1, by positivity, ?_⟩
  intro z hz
  apply (norm_saddleIntegrand_le b hb w L (lt_of_lt_of_le hp hz.1)).trans
  have h : saddleStripCoeff b w L z.re ≤ |B|+1 := by
    have := hB (mem_image_of_mem (saddleStripCoeff b w L) hz)
    linarith [le_abs_self B]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right h (by positivity)) (Real.exp_pos _).le

/-- Absolute convergence on every positive vertical line, not only Re(z)=2. -/
theorem saddleIntegrand_vertical_integrable (b : ℝ) (hb : 0 < b) (w : ℂ) (L σ : ℝ)
    (hσ : 0 < σ) :
    Integrable (fun y : ℝ => saddleIntegrand b w L ((σ : ℂ)+(y : ℂ)*I)) := by
  obtain ⟨C, hC, hc⟩ := saddleIntegrand_strip_bound b hb w L σ σ hσ
  have hg : Integrable (fun y : ℝ => Real.exp (-y^2/(2*b))) := by
    simpa only [neg_mul, one_div_mul_eq_div, neg_div] using
      integrable_exp_neg_mul_sq (b := 1/(2*b)) (by positivity)
  have hg2 : Integrable (fun y : ℝ => y^2*Real.exp (-y^2/(2*b))) := by
    simpa only [Real.rpow_two, neg_mul, one_div_mul_eq_div, neg_div] using
      integrable_rpow_mul_exp_neg_mul_sq (b := 1/(2*b)) (s := 2) (by positivity) (by norm_num)
  have hm : Integrable (fun y : ℝ => C*(1+y^2)*Real.exp (-y^2/(2*b))) := by
    convert (hg.add hg2).const_mul C using 1
    funext y
    simp only [Pi.add_apply]
    ring
  have hcont : Continuous (fun y : ℝ => saddleIntegrand b w L ((σ : ℂ)+(y : ℂ)*I)) := by
    apply continuous_iff_continuousAt.mpr
    intro y
    exact (differentiableAt_saddleIntegrand b w L (by simpa using hσ)).continuousAt.comp
      (f := fun t : ℝ => (σ : ℂ)+(t : ℂ)*I) (by fun_prop)
  apply hm.mono' hcont.aestronglyMeasurable
  exact Eventually.of_forall (fun y => by simpa using hc ((σ : ℂ)+(y : ℂ)*I) (by simp))

private theorem saddleDecay_tendsto (b : ℝ) (hb : 0 < b) :
    Tendsto (fun y : ℝ => (1+y^2)*Real.exp (-y^2/(2*b))) atTop (𝓝 0) := by
  have hs : Tendsto (fun y : ℝ => y^2) atTop atTop := tendsto_pow_atTop (by norm_num)
  have h0 := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 (1/(2*b)) (by positivity)).comp hs
  have h1 := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 (1/(2*b)) (by positivity)).comp hs
  have h := h0.add h1
  simpa only [Function.comp_apply, Real.rpow_zero, Real.rpow_one, one_mul,
    neg_mul, one_div_mul_eq_div, neg_div, zero_add, add_mul] using h

/-- An actual zero-residue shift of each DBN Gaussian-Gamma contour term
between arbitrary positive vertical lines. Horizontal decay and improper
limits are proved, then passed through LeanCert's contour certificates. -/
theorem saddleIntegrand_contour_shift (b : ℝ) (hb : 0 < b) (w : ℂ) (L σ₀ σ₁ : ℝ)
    (h₀ : 0 < σ₀) (h₁ : 0 < σ₁) :
    (∫ y : ℝ, saddleIntegrand b w L ((σ₀ : ℂ)+(y : ℂ)*I)) =
      ∫ y : ℝ, saddleIntegrand b w L ((σ₁ : ℂ)+(y : ℂ)*I) := by
  obtain ⟨C, hC, hc⟩ := saddleIntegrand_strip_bound b hb w L (min σ₀ σ₁) (max σ₀ σ₁)
    (lt_min h₀ h₁)
  have ht : Tendsto (fun n : ℕ => (n : ℝ)+1) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  let B := ContourShift.horizontalBoundOfStrip (saddleIntegrand b w L) σ₀ σ₁
    (fun n => (n : ℝ)+1)
    (fun n => C*(1+((n : ℝ)+1)^2)*Real.exp (-((n : ℝ)+1)^2/(2*b)))
    (fun n => by positivity)
    (by simpa only [mul_assoc, Function.comp_apply, mul_zero] using ((saddleDecay_tendsto b hb).comp ht).const_mul C)
    (by
      intro n x hx
      change x ∈ Icc (min σ₀ σ₁) (max σ₀ σ₁) at hx
      constructor
      · simpa only [add_im, sub_im, ofReal_im, mul_im, ofReal_re, I_im, I_re, mul_one,
          mul_zero, add_zero, zero_add, zero_sub, neg_sq] using hc ((x : ℂ)+((n : ℝ)+1 : ℝ)*I) (by simpa only [add_re, sub_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero, zero_mul, sub_zero, add_zero] using hx)
      · simpa only [add_im, sub_im, ofReal_im, mul_im, ofReal_re, I_im, I_re, mul_one,
          mul_zero, add_zero, zero_add, zero_sub, neg_sq] using hc ((x : ℂ)-((n : ℝ)+1 : ℝ)*I) (by simpa only [add_re, sub_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero, zero_mul, sub_zero, add_zero] using hx))
  apply ContourShift.integral_vertical_eq_of_holomorphic_of_vanish
    (saddleIntegrand b w L) σ₀ σ₁
  · intro z hz
    exact differentiableAt_saddleIntegrand b w L ((lt_min h₀ h₁).trans_le hz.1)
  · exact saddleIntegrand_vertical_integrable b hb w L σ₀ h₀
  · exact saddleIntegrand_vertical_integrable b hb w L σ₁ h₁
  · exact B.toVanishCert

/-- The existing normalized coefficient on an arbitrary positive vertical line.
This ties the contour shift to the already-proved exact heat-function series. -/
theorem normalizedContourTerm_eq_shifted_integral {a : ℝ} (ha : 0 < a)
    (s : ℂ) (k : ℕ) (σ : ℝ) (hσ : 0 < σ) :
    normalizedContourTerm a s k =
      (∫ y : ℝ, saddleIntegrand (4*a) (dobnerMap a s) (Real.log ((k : ℝ)+1))
        ((σ : ℂ)+(y : ℂ)*I)) /
      ((2*Real.sqrt a : ℝ)*(Real.sqrt Real.pi : ℂ)*dobnerGamma a s) := by
  have hc : 0 < 2*Real.sqrt a := by positivity
  have hsq : (Real.sqrt a : ℂ)^2 = (a : ℂ) := by exact_mod_cast Real.sq_sqrt ha.le
  have hk (x : ℝ) : gaussianShift (dobnerContourCenter a s) x =
      Complex.exp ((dobnerMap a s-(2+(2*Real.sqrt a*x : ℝ)*I))^2/(4*a : ℝ)) := by
    unfold gaussianShift dobnerContourCenter
    congr 1
    push_cast
    rw [← hsq]
    field_simp [show (Real.sqrt a : ℂ) ≠ 0 by exact_mod_cast (Real.sqrt_pos.mpr ha).ne']
    ring_nf
    simp only [I_sq, I_pow_three, I_pow_four]
    ring
  have he : dobnerContourTerm (dobnerContourCenter a s) (2*Real.sqrt a) k =
      ∫ x : ℝ, saddleIntegrand (4*a) (dobnerMap a s) (Real.log ((k : ℝ)+1))
        (2+((2*Real.sqrt a)*x : ℝ)*I) := by
    apply integral_congr_ae
    filter_upwards [] with x
    simp only [gammaContourWeight, saddleIntegrand, plainDirichletTerm, hk]
  have hscale := Measure.integral_comp_mul_left
    (fun y : ℝ => saddleIntegrand (4*a) (dobnerMap a s) (Real.log ((k : ℝ)+1))
      (2+(y : ℂ)*I)) (2*Real.sqrt a)
  rw [normalizedContourTerm, he, hscale, abs_of_pos (inv_pos.mpr hc)]
  have hshift :
      (∫ y : ℝ, saddleIntegrand (4*a) (dobnerMap a s) (Real.log ((k : ℝ)+1)) (2+(y : ℂ)*I)) =
      ∫ y : ℝ, saddleIntegrand (4*a) (dobnerMap a s) (Real.log ((k : ℝ)+1)) ((σ : ℂ)+(y : ℂ)*I) := by
    simpa using saddleIntegrand_contour_shift (4*a) (by positivity) (dobnerMap a s)
      (Real.log ((k : ℝ)+1)) 2 σ (by norm_num) hσ
  rw [hshift]
  simp only [Complex.real_smul, div_eq_mul_inv, mul_inv]
  push_cast
  ring

/-- A pole-free contour through (or to the right of) the leading real saddle.
Unlike shifting a full line to Re(s), this is safe even if Re(s) is negative. -/
theorem normalizedContourTerm_eq_saddle_line {a : ℝ} (ha : 0 < a) (s : ℂ) (k : ℕ) :
    normalizedContourTerm a s k =
      (∫ y : ℝ, saddleIntegrand (4*a) (dobnerMap a s) (Real.log ((k : ℝ)+1))
        ((max 2 (s.re+2*a*Real.log ((k : ℝ)+1)) : ℝ)+(y : ℂ)*I)) /
      ((2*Real.sqrt a : ℝ)*(Real.sqrt Real.pi : ℂ)*dobnerGamma a s) :=
  normalizedContourTerm_eq_shifted_integral ha s k _ (lt_of_lt_of_le (by norm_num) (le_max_left _ _))

/-- Exact saddle cancellation in the actual normalized integrand.
Only the Gamma ratio in parentheses needs a relative asymptotic estimate;
this identity does not assert that it tends to one. -/
theorem saddleIntegrand_normalized_factorization {a : ℝ} (ha : 0 < a)
    (s u : ℂ) (L : ℝ) :
    saddleIntegrand (4*a) (dobnerMap a s) L (s+u) / dobnerGamma a s =
      (xiGamma (s+u)/xiGamma s * Complex.exp (-Complex.log (s/(2*Real.pi))*u/2)) *
      Complex.exp (-(s*(L : ℂ))+u^2/(4*(a : ℂ))-u*(L : ℂ)) := by
  have he : (dobnerMap a s-(s+u))^2/(4*(a : ℂ)) -
      (s-dobnerMap a s)^2/(4*(a : ℂ)) - (s+u)*(L : ℂ) =
      -Complex.log (s/(2*Real.pi))*u/2 +
      (-(s*(L : ℂ))+u^2/(4*(a : ℂ))-u*(L : ℂ)) := by
    unfold dobnerMap
    field_simp [Complex.ofReal_ne_zero.mpr ha.ne']
    ring
  calc
    saddleIntegrand (4*a) (dobnerMap a s) L (s+u) / dobnerGamma a s =
        (xiGamma (s+u)/xiGamma s) * Complex.exp
          ((dobnerMap a s-(s+u))^2/(4*(a : ℂ)) -
            (s-dobnerMap a s)^2/(4*(a : ℂ)) - (s+u)*(L : ℂ)) := by
      simp only [saddleIntegrand, dobnerGamma, ofReal_mul, ofReal_ofNat,
        div_eq_mul_inv, mul_inv, Complex.exp_sub, Complex.exp_neg, neg_mul]
      ring
    _ = _ := by rw [he, Complex.exp_add]; ring

end LeanCert.Analysis.DBN
