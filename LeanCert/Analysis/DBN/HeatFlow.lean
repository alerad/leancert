import LeanCert.Analysis.DBN.HeatKernel
import LeanCert.Analysis.ComplexGrowth
import LeanCert.Analysis.IntegralTail
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-! The actual heat-flow integral: measurability, absolute integrability, and
effective Gaussian tails. These results do not assert the xi identity. -/
namespace LeanCert.Analysis.DBN
open MeasureTheory Set

noncomputable def heatIntegrand (t : ℝ) (z : ℂ) (u : ℝ) : ℂ :=
  ((Real.exp (t*u^2) * Phi u : ℝ) : ℂ) * Complex.cos (z * (u : ℂ))

noncomputable def H (t : ℝ) (z : ℂ) : ℂ := ∫ u in Ioi (0 : ℝ), heatIntegrand t z u

/-- A deliberately conservative constant, suitable for convergence and tails,
not for the sharp DBN nonvanishing error budget. -/
noncomputable def heatMajorant (t : ℝ) (z : ℂ) : ℝ :=
  44 * Real.exp (t^2 + (|z.im| +1)^2 + 1)

theorem heatMajorant_pos (t : ℝ) (z : ℂ) : 0 < heatMajorant t z := by
  unfold heatMajorant
  positivity

private theorem exponent_bound (t : ℝ) (z : ℂ) {u : ℝ} (hu : 0 ≤ u) :
    t*u^2 + u - kernelScale u + |z.im| *u ≤ t^2 + (|z.im| +1)^2 + 1 - u^2 := by
  have h4 := Real.pow_div_factorial_le_exp (4*u) (by positivity) 4
  norm_num at h4
  have hs := kernelScale_ge_exp (u := u)
  nlinarith [sq_nonneg (t-u^2), sq_nonneg (|z.im| +1-u), sq_nonneg (u^2-1),
    sq_nonneg t, sq_nonneg (|z.im| +1), sq_nonneg (u^2)]

/-- The scalar amplitude bound also controls sine and phase-shifted cosine
kernels, so differentiated integrands can reuse the same majorant. -/
theorem heat_weight_bound (t : ℝ) (z : ℂ) {u : ℝ} (hu : 0 ≤ u) :
    Real.exp (t*u^2)*‖Phi u‖*Real.exp (|z.im| * u) ≤
      heatMajorant t z * Real.exp (-u^2) := by
  have h := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (Phi_bound_nonneg hu) (Real.exp_pos (t*u^2)).le)
    (Real.exp_pos (|z.im| * u)).le
  apply h.trans
  have he : Real.exp (t*u^2)*(44*Real.exp (u-kernelScale u))*Real.exp (|z.im| *u) =
      44*Real.exp (t*u^2+u-kernelScale u+|z.im| *u) := by
    rw [show t*u^2+u-kernelScale u+|z.im| *u = t*u^2+(u-kernelScale u)+|z.im| *u by ring,
      Real.exp_add, Real.exp_add]
    ring
  rw [he]
  have h' := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (exponent_bound t z hu))
    (show (0 : ℝ) ≤ 44 by norm_num)
  simpa [heatMajorant, Real.exp_sub, Real.exp_neg, div_eq_mul_inv, mul_assoc] using h'

/-- Gaussian domination of the actual heat integrand for every real time and
complex argument, including t=0 and the endpoint u=0. -/
theorem heatIntegrand_bound (t : ℝ) (z : ℂ) {u : ℝ} (hu : 0 ≤ u) :
    ‖heatIntegrand t z u‖ ≤ heatMajorant t z * Real.exp (-u^2) := by
  have hc : ‖Complex.cos (z*(u : ℂ))‖ ≤ Real.exp (|z.im| *u) := by
    simpa [Complex.mul_im, abs_mul, abs_of_nonneg hu] using norm_cos_le_exp_abs_im (z*(u : ℂ))
  have h := mul_le_mul_of_nonneg_left hc
    (show 0 ≤ Real.exp (t*u^2)*‖Phi u‖ by positivity)
  have hn : ‖heatIntegrand t z u‖ = Real.exp (t*u^2)*‖Phi u‖*‖Complex.cos (z*(u : ℂ))‖ := by
    simp only [heatIntegrand, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
  rw [← hn] at h
  exact h.trans (heat_weight_bound t z hu)

/-- A common integrable Gaussian majorant on bounded time/imaginary-part boxes.
There is no restriction on the real part of z. -/
theorem heatIntegrand_bound_box (T Y : ℝ) {t : ℝ} {z : ℂ} {u : ℝ}
    (ht : |t| ≤ T) (hz : |z.im| ≤ Y) (hu : 0 ≤ u) :
    ‖heatIntegrand t z u‖ ≤
      (44 * Real.exp (T^2+(Y+1)^2+1)) * Real.exp (-u^2) := by
  apply (heatIntegrand_bound t z hu).trans
  apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
  unfold heatMajorant
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Real.exp_le_exp.mpr
  have hT : 0 ≤ T := (abs_nonneg t).trans ht
  have hY : 0 ≤ Y := (abs_nonneg z.im).trans hz
  have hs : t^2 ≤ T^2 := by nlinarith [sq_abs t, mul_nonneg (sub_nonneg.mpr ht) (add_nonneg hT (abs_nonneg t))]
  nlinarith [mul_nonneg (sub_nonneg.mpr hz) (show 0 ≤ Y+|z.im|+2 by positivity)]

theorem measurable_heatIntegrand (t : ℝ) (z : ℂ) : Measurable (heatIntegrand t z) := by
  unfold heatIntegrand
  have hp := measurable_Phi
  fun_prop

/-- Absolute integrability of H's defining integrand on its actual domain. -/
theorem heatIntegrand_integrable (t : ℝ) (z : ℂ) : IntegrableOn (heatIntegrand t z) (Ioi 0) := by
  have hg : IntegrableOn (fun u : ℝ => heatMajorant t z * Real.exp (-u^2)) (Ioi 0) := by
    simpa only [IntegrableOn, neg_mul, one_mul] using
      (integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1)).integrableOn.const_mul (heatMajorant t z)
  apply hg.mono' (measurable_heatIntegrand t z).aestronglyMeasurable
  exact (ae_restrict_iff' measurableSet_Ioi).mpr
    (Filter.Eventually.of_forall (fun u hu => heatIntegrand_bound t z hu.le))

/-- Effective truncation of the actual heat integral at any positive cutoff. -/
theorem H_tail (t : ℝ) (z : ℂ) (b : ℝ) (hb : 0 < b) :
    ‖H t z - ∫ u in (0 : ℝ)..b, heatIntegrand t z u‖ ≤
      heatMajorant t z * Real.exp (-b^2) / b := by
  obtain ⟨hi, ht⟩ := IntegralTail.of_gaussian (heatIntegrand t z) b (heatMajorant t z) 1
    hb (heatMajorant_pos t z).le (by norm_num)
    (measurable_heatIntegrand t z).aestronglyMeasurable
    (fun u hu => by simpa using heatIntegrand_bound t z (hb.trans hu).le)
  have hf := heatIntegrand_integrable t z
  have he := intervalIntegral.integral_interval_add_Ioi hf hi
  unfold H
  rw [← he]
  simpa using ht

end LeanCert.Analysis.DBN
