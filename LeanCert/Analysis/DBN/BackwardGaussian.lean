import LeanCert.Analysis.DBN.KernelRegularity
import LeanCert.Analysis.DBN.HeatSymmetry
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Recovering the kernel from backward heat times

A change of variables and dominated convergence give a Gaussian approximate
identity. This concerns the actual integral, with no assumptions on its zeros.
-/
namespace LeanCert.Analysis.DBN
open MeasureTheory Set Filter Complex
open scoped Topology

noncomputable def gaussianAverage (c x : ℝ) : ℝ :=
  ∫ v : ℝ, Real.exp (-v^2) * evenPhi (x+v/c)

theorem evenPhi_bounded (u : ℝ) : ‖evenPhi u‖ ≤ 44*Real.exp 1 := by
  apply (evenPhi_bound u).trans
  have h : Real.exp (-u^2) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg u])
  nlinarith [Real.exp_pos 1]

theorem gaussianAverage_tendsto (x : ℝ) :
    Tendsto (fun n : ℕ => gaussianAverage (n+1) x) atTop
      (𝓝 (Real.sqrt Real.pi * evenPhi x)) := by
  have hi : Integrable (fun v : ℝ => (44*Real.exp 1)*Real.exp (-v^2)) := by
    simpa using (integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1)).const_mul
      (44*Real.exp 1)
  have hm (n : ℕ) : AEStronglyMeasurable (fun v : ℝ =>
      Real.exp (-v^2) * evenPhi (x+v/(n+1))) :=
    (show Continuous (fun v : ℝ => Real.exp (-v^2)*evenPhi (x+v/(n+1))) by
      apply Continuous.mul (by fun_prop)
      exact continuous_evenPhi.comp (by fun_prop)).aestronglyMeasurable
  have hb (n : ℕ) : ∀ᵐ v : ℝ, ‖Real.exp (-v^2)*evenPhi (x+v/(n+1))‖ ≤
      (44*Real.exp 1)*Real.exp (-v^2) := by
    apply Eventually.of_forall
    intro v
    rw [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left
      (evenPhi_bounded (x+v/(n+1))) (Real.exp_pos (-v^2)).le
  have hl : ∀ᵐ v : ℝ, Tendsto (fun n : ℕ =>
      Real.exp (-v^2)*evenPhi (x+v/(n+1))) atTop
      (𝓝 (Real.exp (-v^2)*evenPhi x)) := by
    apply Eventually.of_forall
    intro v
    have hinv : Tendsto (fun n : ℕ => ((n : ℝ)+1)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop)
    have harg : Tendsto (fun n : ℕ => x+v/(n+1)) atTop (𝓝 x) := by
      simpa [div_eq_mul_inv] using tendsto_const_nhds.add (tendsto_const_nhds.mul hinv)
    exact tendsto_const_nhds.mul ((continuous_evenPhi.tendsto x).comp harg)
  have h := tendsto_integral_of_dominated_convergence
    (fun v : ℝ => (44*Real.exp 1)*Real.exp (-v^2)) hm hi hb hl
  have hg : (∫ v : ℝ, Real.exp (-v^2)) = Real.sqrt Real.pi := by
    simpa using integral_gaussian (1 : ℝ)
  simpa only [gaussianAverage, integral_mul_const, hg] using h

private theorem gaussian_integrable (c x : ℝ) :
    Integrable (fun u : ℝ => Real.exp (-(c*(u-x))^2)*evenPhi u) := by
  apply integrable_evenPhi.mono'
    ((show Continuous (fun u : ℝ => Real.exp (-(c*(u-x))^2)*evenPhi u) by
      exact (by fun_prop : Continuous (fun u : ℝ => Real.exp (-(c*(u-x))^2))).mul
        continuous_evenPhi).aestronglyMeasurable)
  apply Eventually.of_forall
  intro u
  rw [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  simpa only [Real.norm_eq_abs, abs_of_pos (evenPhi_pos u), one_mul] using mul_le_mul_of_nonneg_right
    (Real.exp_le_one_iff.mpr (show -(c*(u-x))^2 ≤ 0 by nlinarith [sq_nonneg (c*(u-x))])) (norm_nonneg (evenPhi u))

theorem gaussianAverage_eq_convolution {c : ℝ} (hc : 0 < c) (x : ℝ) :
    gaussianAverage c x =
      c * ∫ u : ℝ, Real.exp (-(c*(u-x))^2)*evenPhi u := by
  let f : ℝ → ℝ := fun u => Real.exp (-(c*(u-x))^2)*evenPhi u
  have h := Measure.integral_comp_inv_mul_left (fun v => f (x+v)) c
  have hshift := integral_add_left_eq_self (μ := volume) f x
  rw [hshift, abs_of_pos hc, smul_eq_mul] at h
  convert h using 1
  unfold gaussianAverage
  apply integral_congr_ae
  apply Eventually.of_forall
  intro v
  dsimp [f]
  congr 2 <;> field_simp <;> ring

theorem H_imaginary_re (t y : ℝ) :
    (H t ((y : ℂ)*I)).re =
      ∫ u in Ioi (0 : ℝ), Real.exp (t*u^2)*Phi u*Real.cosh (y*u) := by
  have hr := integral_re (heatIntegrand_integrable t ((y : ℂ)*I))
  change (∫ u in Ioi (0 : ℝ), (heatIntegrand t ((y : ℂ)*I) u).re) =
    (H t ((y : ℂ)*I)).re at hr
  rw [← hr]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro u _
  have he : ((y : ℂ)*I)*(u : ℂ) = ((y*u : ℝ) : ℂ)*I := by push_cast; ring
  simp only [heatIntegrand, he, Complex.cos_mul_I, ← Complex.ofReal_cosh,
    ← Complex.ofReal_mul, Complex.ofReal_re]

theorem H_imaginary_im (t y : ℝ) : (H t ((y : ℂ)*I)).im = 0 := by
  have h := H_conj t ((y : ℂ)*I)
  have he : starRingEnd ℂ ((y : ℂ)*I) = -((y : ℂ)*I) := by simp
  rw [he, H_even] at h
  have hh := congrArg Complex.im h
  simp only [Complex.conj_im] at hh
  linarith

theorem gaussianAverage_eq_H {c : ℝ} (hc : 0 < c) (x : ℝ) :
    gaussianAverage c x =
      (2*c) * Real.exp (-c^2*x^2) * (H (-c^2) ((2*c^2*x : ℝ)*I)).re := by
  rw [gaussianAverage_eq_convolution hc]
  let f : ℝ → ℝ := fun u => Real.exp (-(c*(u-x))^2)*evenPhi u
  have hf : Integrable f := gaussian_integrable c x
  have hsplit : (∫ u, f u) = ∫ u in Ioi (0 : ℝ), f u + f (-u) := by
    rw [integral_add hf.integrableOn hf.comp_neg.integrableOn,
      integral_comp_neg_Ioi]
    simpa using (integral_add_compl measurableSet_Ioi hf).symm
  change c * (∫ u, f u) = _
  rw [hsplit, H_imaginary_re]
  have he (u : ℝ) (hu : u ∈ Ioi (0 : ℝ)) :
      f u + f (-u) = 2*Real.exp (-c^2*x^2) *
        (Real.exp (-c^2*u^2)*Phi u*Real.cosh ((2*c^2*x)*u)) := by
    have h1 : -(c*(u-x))^2 = -c^2*x^2 + (-c^2*u^2 + (2*c^2*x)*u) := by ring
    have h2 : -(c*(-u-x))^2 = -c^2*x^2 + (-c^2*u^2 - (2*c^2*x)*u) := by ring
    simp only [f, evenPhi, abs_neg, abs_of_pos (show 0 < u from hu), h1, h2,
      Real.exp_add, Real.exp_sub, Real.cosh_eq]
    rw [Real.exp_neg]
    field_simp
  rw [setIntegral_congr_fun measurableSet_Ioi he, integral_const_mul]
  ring

end LeanCert.Analysis.DBN
