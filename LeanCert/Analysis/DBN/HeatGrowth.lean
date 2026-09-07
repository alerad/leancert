import LeanCert.Analysis.DBN.HeatRegularity

/-! Subquadratic spatial growth of the actual time-zero heat integral. -/
namespace LeanCert.Analysis.DBN
open MeasureTheory Set Complex

/-- Cubic absorption gives an exponent of order `3/2`, strictly below two. -/
theorem cubic_absorption {u y : ℝ} (hu : 0 ≤ u) (hy : 0 ≤ y) :
    y*u ≤ u^3 + y*Real.sqrt y := by
  by_cases h : u ≤ Real.sqrt y
  · nlinarith [mul_le_mul_of_nonneg_left h hy, pow_nonneg hu 3]
  · have hs := Real.sq_sqrt hy
    have hroot := Real.sqrt_nonneg y
    have hyu : y ≤ u^2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right hyu hu, mul_nonneg hy hroot]

/-- Prototype of the sharper exponent estimate needed by Hadamard.
Unlike the existing quadratic majorant, its parameter dependence is subquadratic. -/
theorem subquadratic_exponent {u y : ℝ} (hu : 0 ≤ u) (hy : 0 ≤ y) :
    y*u - kernelScale u ≤ y*Real.sqrt y + 2 - u^2 := by
  have h := cubic_absorption hu hy
  have he := Real.pow_div_factorial_le_exp (4*u) (by positivity) 4
  norm_num at he
  have hk := kernelScale_ge_exp (u := u)
  have h2 : u^2 ≤ u^4+1 := by nlinarith [sq_nonneg (u^2-1)]
  have h3 : u^3 ≤ u^4+1 := by
    by_cases hle : u ≤ 1
    · have : u^3 ≤ 1 := by simpa using pow_le_pow_left₀ hu hle 3
      nlinarith [pow_nonneg hu 4]
    · nlinarith [mul_nonneg (pow_nonneg hu 3) (show 0 ≤ u-1 by linarith)]
  nlinarith [pow_nonneg hu 4]


/-- A subquadratic, rather than quadratic, majorant for the initial integrand. -/
theorem heatIntegrand_zero_subquadratic {u : ℝ} (hu : 0 ≤ u) (z : ℂ) :
    ‖heatIntegrand 0 z u‖ ≤
      (44 * Real.exp ((|z.im|+1)*Real.sqrt (|z.im|+1)+2)) * Real.exp (-u^2) := by
  have hc : ‖Complex.cos (z*(u : ℂ))‖ ≤ Real.exp (|z.im| * u) := by
    simpa [Complex.mul_im, abs_mul, abs_of_nonneg hu] using norm_cos_le_exp_abs_im (z*(u : ℂ))
  have h := mul_le_mul (Phi_bound_nonneg hu) hc (norm_nonneg _) (by positivity)
  have hn : ‖heatIntegrand 0 z u‖ = ‖Phi u‖*‖Complex.cos (z*(u : ℂ))‖ := by
    simp only [heatIntegrand, zero_mul, Real.exp_zero, one_mul, norm_mul, Complex.norm_real]
  rw [hn]
  apply h.trans
  simp only [mul_assoc, ← Real.exp_add]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Real.exp_le_exp.mpr
  have he := subquadratic_exponent hu (show 0 ≤ |z.im|+1 by positivity)
  nlinarith

/-- The Gaussian mass is left symbolic; no numerical integration is needed. -/
theorem H_zero_subquadratic (z : ℂ) :
    ‖H 0 z‖ ≤ (44 * (∫ u in Ioi (0 : ℝ), Real.exp (-u^2))) *
      Real.exp ((|z.im|+1)*Real.sqrt (|z.im|+1)+2) := by
  have hg : IntegrableOn (fun u : ℝ => Real.exp (-u^2)) (Ioi 0) := by
    simpa only [neg_mul, one_mul] using
      (integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1)).integrableOn
  have h := norm_integral_le_of_norm_le
    (hg.const_mul (44 * Real.exp ((|z.im|+1)*Real.sqrt (|z.im|+1)+2)))
    ((ae_restrict_iff' measurableSet_Ioi).mpr
      (Filter.Eventually.of_forall (fun u hu => heatIntegrand_zero_subquadratic hu.le z)))
  rw [integral_const_mul] at h
  simpa only [H, mul_assoc, mul_left_comm, mul_comm] using h

/-- A coarse order-3/2 spatial bound; sufficient for genus-one Hadamard. -/
theorem H_zero_norm_le_exp_order :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, ‖H 0 z‖ ≤ Real.exp (C*(1+‖z‖)^(3/2 : ℝ)) := by
  let A : ℝ := 44 * (∫ u in Ioi (0 : ℝ), Real.exp (-u^2))
  refine ⟨|A|+3, by positivity, ?_⟩
  intro z
  have hx : 0 < 1+‖z‖ := by positivity
  have hy : |z.im|+1 ≤ 1+‖z‖ := by linarith [Complex.abs_im_le_norm z]
  have hs : (1+‖z‖)*Real.sqrt (1+‖z‖) = (1+‖z‖)^(3/2 : ℝ) := by
    rw [show (3/2 : ℝ) = 1+1/2 by norm_num, Real.rpow_add hx, Real.rpow_one, Real.sqrt_eq_rpow]
  have hb : (|z.im|+1)*Real.sqrt (|z.im|+1) ≤ (1+‖z‖)^(3/2 : ℝ) := by
    rw [← hs]
    exact mul_le_mul hy (Real.sqrt_le_sqrt hy) (Real.sqrt_nonneg _) hx.le
  have hB : 1 ≤ (1+‖z‖)^(3/2 : ℝ) := Real.one_le_rpow (by linarith [norm_nonneg z]) (by norm_num)
  have hA : A ≤ Real.exp |A| := by linarith [le_abs_self A, Real.add_one_le_exp |A|]
  calc
    ‖H 0 z‖ ≤ A * Real.exp ((|z.im|+1)*Real.sqrt (|z.im|+1)+2) := H_zero_subquadratic z
    _ ≤ Real.exp |A| * Real.exp ((|z.im|+1)*Real.sqrt (|z.im|+1)+2) :=
      mul_le_mul_of_nonneg_right hA (Real.exp_pos _).le
    _ ≤ Real.exp ((|A|+3)*(1+‖z‖)^(3/2 : ℝ)) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith [mul_nonneg (abs_nonneg A) (sub_nonneg.mpr hB)]

end LeanCert.Analysis.DBN
