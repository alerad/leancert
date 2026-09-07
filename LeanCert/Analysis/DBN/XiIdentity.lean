import LeanCert.Analysis.DBN.ThetaIntegral
import LeanCert.Analysis.DBN.Xi

/-!
# Exact H_0 / xi identity and the initial zero strip

Split Mathlib's modified theta kernel at 1, use theta inversion on (0,1),
and transform the resulting (1,infinity) integral by x = exp(4*u).
Convergence is obtained from Mathlib's strong FE-pair theorem before splitting
the Mellin integral. The point x = 1 is handled by the modified kernel's
actual value, and no division by the xi pole factors is used.

The conclusion concerns the original `H` integral, not a redefinition.
Strip shrinking at positive time remains a separate theorem.
-/
namespace LeanCert.Analysis.DBN
open MeasureTheory Set Complex HurwitzZeta

private noncomputable def thetaUpper (x : ℝ) : ℂ :=
  (Ioi (1 : ℝ)).indicator (fun y => (cosKernel 0 y : ℂ) - 1) x

private theorem modified_theta_decomposition {x : ℝ} (hx : 0 < x) :
    (hurwitzEvenFEPair 0).f_modif x = thetaUpper x +
      (x : ℂ)^(-1/2 : ℂ) * thetaUpper x⁻¹ := by
  have hpow : (x : ℂ)^(-1/2 : ℂ) = (x^(-(1/2 : ℝ)) : ℝ) := by
    simpa only [ofReal_neg, ofReal_div, ofReal_one, ofReal_ofNat, neg_div] using
      (ofReal_cpow hx.le (-(1/2 : ℝ))).symm
  have hfe := evenKernel_functional_equation 0 x
  rw [evenKernel_eq_cosKernel_of_zero] at hfe
  have hr : 1 / x^(1/2 : ℝ) = x^(-(1/2 : ℝ)) := by rw [Real.rpow_neg hx.le, one_div]
  rw [hr] at hfe
  rcases lt_trichotomy x 1 with h | rfl | h
  · have hinv : 1 < x⁻¹ := (one_lt_inv₀ hx).mpr h
    simp only [WeakFEPair.f_modif, hurwitzEvenFEPair, Function.comp_apply,
      Pi.add_apply, evenKernel_eq_cosKernel_of_zero, thetaUpper,
      indicator_of_notMem (show x ∉ Ioi (1 : ℝ) by exact not_lt.mpr h.le),
      indicator_of_mem (show x ∈ Ioo (0 : ℝ) 1 from ⟨hx, h⟩),
      indicator_of_mem (show x⁻¹ ∈ Ioi (1 : ℝ) from hinv),
      if_true, zero_add, one_mul, smul_eq_mul, mul_one, hpow]
    rw [hfe]
    push_cast
    simp only [one_div]
    ring
  · simp [WeakFEPair.f_modif, hurwitzEvenFEPair, thetaUpper]
  · have hinv : x⁻¹ < 1 := (inv_lt_one₀ hx).mpr h
    simp [WeakFEPair.f_modif, hurwitzEvenFEPair, thetaUpper,
      evenKernel_eq_cosKernel_of_zero, h, h.not_gt, hinv.not_gt]

private theorem modified_theta_integrable (s : ℂ) :
    MellinConvergent (hurwitzEvenFEPair 0).f_modif s :=
  ((hurwitzEvenFEPair 0).isStrongFEPair_toStrongFEPair.hasMellin s).1

private theorem thetaUpper_integrable (s : ℂ) : MellinConvergent thetaUpper s := by
  have h := Integrable.indicator (modified_theta_integrable s) (s := Ioi (1 : ℝ))
    measurableSet_Ioi
  apply h.congr
  filter_upwards with x
  by_cases hx : 1 < x
  · simp [thetaUpper, WeakFEPair.f_modif, hurwitzEvenFEPair, hx,
      evenKernel_eq_cosKernel_of_zero, hx.not_gt]
  · simp [thetaUpper, hx]

private theorem modified_theta_mellin (s : ℂ) :
    mellin (hurwitzEvenFEPair 0).f_modif s =
      mellin thetaUpper s + mellin thetaUpper (1/2-s) := by
  have hInv : MellinConvergent (fun x => thetaUpper x⁻¹) (s + (-1/2)) := by
    have h := (MellinConvergent.comp_rpow (f := thetaUpper) (s := s + (-1/2))
      (by norm_num : (-1 : ℝ) ≠ 0))
    have he : (s + (-1/2)) / ((-1 : ℝ) : ℂ) = 1/2-s := by push_cast; ring
    rw [he] at h
    simpa only [Real.rpow_neg_one] using h.mpr (thetaUpper_integrable (1/2-s))
  have hLow : MellinConvergent
      (fun x : ℝ => (x : ℂ)^(-1/2 : ℂ) • thetaUpper x⁻¹) s :=
    MellinConvergent.cpow_smul.mpr hInv
  calc
    _ = mellin (fun x : ℝ => thetaUpper x + (x : ℂ)^(-1/2 : ℂ) • thetaUpper x⁻¹) s := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      dsimp only
      rw [modified_theta_decomposition hx]
      rfl
    _ = mellin thetaUpper s +
        mellin (fun x : ℝ => (x : ℂ)^(-1/2 : ℂ) • thetaUpper x⁻¹) s :=
      (hasMellin_add (thetaUpper_integrable s) hLow).2
    _ = _ := by
      rw [mellin_cpow_smul, mellin_comp_inv]
      congr 2
      ring

private theorem thetaUpper_mellin (s : ℂ) :
    mellin thetaUpper s = ∫ x in Ioi (1 : ℝ), (x : ℂ)^(s-1) * ((cosKernel 0 x : ℂ)-1) := by
  simp_rw [mellin, thetaUpper, ← indicator_smul]
  simp only [integral_indicator measurableSet_Ioi,
    Measure.restrict_restrict_of_subset (Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 1)), smul_eq_mul]

private theorem thetaUpper_mellin_integrable (s : ℂ) :
    IntegrableOn (fun x : ℝ => (x : ℂ)^(s-1) * ((cosKernel 0 x : ℂ)-1)) (Ioi 1) := by
  have h := thetaUpper_integrable s
  simp_rw [MellinConvergent, thetaUpper, ← indicator_smul, IntegrableOn] at h
  simp only [integrable_indicator_iff measurableSet_Ioi, IntegrableOn,
    Measure.restrict_restrict_of_subset (Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 1)),
    smul_eq_mul] at h
  exact h

private noncomputable def thetaMellinIntegrand (s : ℂ) (x : ℝ) : ℂ :=
  (x : ℂ)^(s/2-1) * ((cosKernel 0 x : ℂ)-1) +
    (x : ℂ)^(1/2-s/2-1) * ((cosKernel 0 x : ℂ)-1)

private theorem completed_eq_thetaMellin (s : ℂ) :
    completedRiemannZeta₀ s = (∫ x in Ioi (1 : ℝ), thetaMellinIntegrand s x) / 2 := by
  change mellin (hurwitzEvenFEPair 0).f_modif (s/2) / 2 = _
  rw [modified_theta_mellin, thetaUpper_mellin, thetaUpper_mellin,
    ← integral_add (thetaUpper_mellin_integrable (s/2))
      (thetaUpper_mellin_integrable (1/2-s/2))]
  rfl

private theorem exp_mul_cpow (v : ℝ) (a : ℂ) :
    (Real.exp v : ℂ) * (Real.exp v : ℂ)^(a-1) = Complex.exp ((v : ℂ)*a) := by
  rw [cpow_def_of_ne_zero (ofReal_ne_zero.mpr (Real.exp_ne_zero v))]
  rw [Complex.ofReal_exp, Complex.log_exp (by simp [Real.pi_pos]) (by simp [Real.pi_pos.le])]
  rw [← Complex.exp_add]
  congr 1
  ring

private theorem thetaMellin_change_integrand (z : ℂ) (u : ℝ) :
    (4 : ℝ) • (Real.exp (4*u) •
      thetaMellinIntegrand (1/2 + I*z/2) (Real.exp (4*u))) =
        16 * thetaCosIntegrand z u := by
  have hp : ((4*u : ℝ) : ℂ)*((1/2+I*z/2)/2) = (u : ℂ)+(z*(u : ℂ))*I := by
    push_cast; ring
  have hm : ((4*u : ℝ) : ℂ)*(1/2-(1/2+I*z/2)/2) = (u : ℂ)+(-z*(u : ℂ))*I := by
    push_cast; ring
  simp only [thetaMellinIntegrand, Complex.real_smul]
  rw [mul_add]
  rw [← mul_assoc (Real.exp (4*u) : ℂ) _ _, ← mul_assoc (Real.exp (4*u) : ℂ) _ _]
  rw [exp_mul_cpow, exp_mul_cpow, hp, hm, Complex.exp_add, Complex.exp_add]
  simp only [thetaCosIntegrand, thetaPrimitive, ofReal_div, ofReal_mul, ofReal_sub,
    ofReal_one, ofReal_ofNat, ofReal_exp, Complex.cos]
  ring_nf

/-- The pole-subtracted completion in exactly the DBN cosine normalization. -/
theorem completedRiemannZeta₀_eq_thetaCosIntegral (z : ℂ) :
    completedRiemannZeta₀ (1/2 + I*z/2) = 8 * thetaCosIntegral z := by
  let g := thetaMellinIntegrand (1/2 + I*z/2)
  have hexp : (∫ x in Ioi (1 : ℝ), g x) =
      ∫ v in Ioi (0 : ℝ), Real.exp v • g (Real.exp v) := by
    simpa using (integral_comp_exp_Ioi g 0).symm
  have hscale : (∫ v in Ioi (0 : ℝ), Real.exp v • g (Real.exp v)) =
      ∫ u in Ioi (0 : ℝ), (4 : ℝ) • (Real.exp (4*u) • g (Real.exp (4*u))) := by
    rw [integral_smul]
    simpa using (integral_comp_mul_left_Ioi'
      (fun v => Real.exp v • g (Real.exp v)) 0 (by norm_num : (0 : ℝ) < 4)).symm
  rw [completed_eq_thetaMellin, hexp, hscale]
  have hi : (∫ u in Ioi (0 : ℝ), (4 : ℝ) • (Real.exp (4*u) • g (Real.exp (4*u)))) =
      16 * thetaCosIntegral z := by
    unfold thetaCosIntegral
    rw [← integral_const_mul]
    exact setIntegral_congr_fun measurableSet_Ioi (fun u _ => thetaMellin_change_integrand z u)
  rw [hi]
  ring

/-- Exact identity for the original heat integral, valid also at z = ±i. -/
theorem H_zero_eq_xiModel (z : ℂ) : H 0 z = xiModel z := by
  rw [H_zero_eq_thetaCosIntegral, xiModel, riemannXi, completedRiemannZeta₀_eq_thetaCosIntegral]
  have hI := Complex.I_sq
  ring_nf
  simp [hI]
  ring

/-- The classical normalization, with the entire pole-safe xi function. -/
theorem H_zero_eq_riemannXi (z : ℂ) :
    H 0 z = riemannXi (1/2 + I*z/2) / 8 := H_zero_eq_xiModel z

/-- The actual initial heat function has all its zeros in the closed unit strip. -/
theorem H_zero_strip {z : ℂ} (hz : H 0 z = 0) : |z.im| ≤ 1 := by
  apply xiModel_zero_strip
  rw [← H_zero_eq_xiModel]
  exact hz

theorem H_zero_ne_zero_of_one_lt_abs_im {z : ℂ} (hz : 1 < |z.im|) : H 0 z ≠ 0 :=
  fun h => (not_le_of_gt hz) (H_zero_strip h)

end LeanCert.Analysis.DBN
