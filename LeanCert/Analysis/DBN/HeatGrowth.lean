import LeanCert.Analysis.DBN.HeatRegularity

/-! Subquadratic spatial growth of the actual heat integral at every real time. -/
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
theorem heat_subquadratic_exponent (t : ℝ) {u y : ℝ} (hu : 0 ≤ u) (hy : 0 ≤ y) :
    t*u^2 + y*u - kernelScale u ≤ t^2 + y*Real.sqrt y + 2 - u^2 := by
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
  nlinarith [pow_nonneg hu 4, sq_nonneg (t-u^2), sq_nonneg t]


/-- A subquadratic spatial majorant, with time dependence isolated in `t²`. -/
theorem heatIntegrand_subquadratic (t : ℝ) {u : ℝ} (hu : 0 ≤ u) (z : ℂ) :
    ‖heatIntegrand t z u‖ ≤
      (44 * Real.exp (t^2+(|z.im|+1)*Real.sqrt (|z.im|+1)+2)) *
        Real.exp (-u^2) := by
  have hc : ‖Complex.cos (z*(u : ℂ))‖ ≤ Real.exp (|z.im| * u) := by
    simpa [Complex.mul_im, abs_mul, abs_of_nonneg hu] using
      norm_cos_le_exp_abs_im (z*(u : ℂ))
  have h := mul_le_mul
    (mul_le_mul_of_nonneg_left (Phi_bound_nonneg hu) (Real.exp_pos (t*u^2)).le)
    hc (norm_nonneg _) (by positivity)
  have hn : ‖heatIntegrand t z u‖ =
      Real.exp (t*u^2)*‖Phi u‖*‖Complex.cos (z*(u : ℂ))‖ := by
    simp only [heatIntegrand, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
  rw [hn]
  apply h.trans
  have he := heat_subquadratic_exponent t hu (show 0 ≤ |z.im|+1 by positivity)
  have hex : Real.exp (t*u^2)*(44*Real.exp (u-kernelScale u))*Real.exp (|z.im| *u) =
      44 * Real.exp (t*u^2+u-kernelScale u+|z.im| *u) := by
    rw [show t*u^2+u-kernelScale u+|z.im| *u =
      t*u^2+(u-kernelScale u)+|z.im| *u by ring, Real.exp_add, Real.exp_add]
    ring
  rw [hex, mul_assoc, ← Real.exp_add]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Real.exp_le_exp.mpr
  nlinarith

/-- The Gaussian mass is left symbolic; no numerical integration is needed. -/
theorem H_subquadratic (t : ℝ) (z : ℂ) :
    ‖H t z‖ ≤ (44 * (∫ u in Ioi (0 : ℝ), Real.exp (-u^2))) *
      Real.exp (t^2+(|z.im|+1)*Real.sqrt (|z.im|+1)+2) := by
  have hg : IntegrableOn (fun u : ℝ => Real.exp (-u^2)) (Ioi 0) := by
    simpa only [neg_mul, one_mul] using
      (integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1)).integrableOn
  have h := norm_integral_le_of_norm_le
    (hg.const_mul (44 * Real.exp (t^2+(|z.im|+1)*Real.sqrt (|z.im|+1)+2)))
    ((ae_restrict_iff' measurableSet_Ioi).mpr
      (Filter.Eventually.of_forall (fun u hu => heatIntegrand_subquadratic t hu.le z)))
  rw [integral_const_mul] at h
  simpa only [H, mul_assoc, mul_left_comm, mul_comm] using h

/-- A coarse order-3/2 spatial bound; sufficient for genus-one Hadamard. -/
theorem H_norm_le_exp_order (t : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, ‖H t z‖ ≤ Real.exp (C*(1+‖z‖)^(3/2 : ℝ)) := by
  let A : ℝ := 44 * (∫ u in Ioi (0 : ℝ), Real.exp (-u^2))
  refine ⟨|A|+t^2+3, by positivity, ?_⟩
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
    ‖H t z‖ ≤ A * Real.exp (t^2+(|z.im|+1)*Real.sqrt (|z.im|+1)+2) := H_subquadratic t z
    _ ≤ Real.exp |A| * Real.exp (t^2+(|z.im|+1)*Real.sqrt (|z.im|+1)+2) :=
      mul_le_mul_of_nonneg_right hA (Real.exp_pos _).le
    _ ≤ Real.exp ((|A|+t^2+3)*(1+‖z‖)^(3/2 : ℝ)) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith [mul_nonneg (abs_nonneg A) (sub_nonneg.mpr hB),
        mul_nonneg (sq_nonneg t) (sub_nonneg.mpr hB)]

/-- Compatibility specialization of the arbitrary-time exponent bound. -/
theorem subquadratic_exponent {u y : ℝ} (hu : 0 ≤ u) (hy : 0 ≤ y) :
    y*u - kernelScale u ≤ y*Real.sqrt y + 2 - u^2 := by
  simpa using heat_subquadratic_exponent 0 hu hy

theorem heatIntegrand_zero_subquadratic {u : ℝ} (hu : 0 ≤ u) (z : ℂ) :
    ‖heatIntegrand 0 z u‖ ≤
      (44 * Real.exp ((|z.im|+1)*Real.sqrt (|z.im|+1)+2)) * Real.exp (-u^2) := by
  simpa using heatIntegrand_subquadratic 0 hu z

theorem H_zero_subquadratic (z : ℂ) :
    ‖H 0 z‖ ≤ (44 * (∫ u in Ioi (0 : ℝ), Real.exp (-u^2))) *
      Real.exp ((|z.im|+1)*Real.sqrt (|z.im|+1)+2) := by
  simpa using H_subquadratic 0 z

theorem H_zero_norm_le_exp_order :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, ‖H 0 z‖ ≤ Real.exp (C*(1+‖z‖)^(3/2 : ℝ)) :=
  H_norm_le_exp_order 0

end LeanCert.Analysis.DBN
