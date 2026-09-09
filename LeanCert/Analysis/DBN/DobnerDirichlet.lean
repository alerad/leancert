/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Analysis.DBN.BackwardContour
import LeanCert.Analysis.DBN.DobnerGammaBounds
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Absolute integrability and termwise expansion on the initial contour. -/
namespace LeanCert.Analysis.DBN
open Complex MeasureTheory Set Filter
open scoped Topology

private theorem continuous_xiGamma_vertical (c : ℝ) :
    Continuous (fun x : ℝ => xiGamma (2+(c*x : ℝ)*I)) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  let s : ℂ := 2+(c*x : ℝ)*I
  have hs : 0 < s.re := by simp [s]
  have hg : DifferentiableAt ℂ Gammaℝ s := by
    have h := (differentiable_Gammaℝ_inv s).inv
      (inv_ne_zero (Gammaℝ_ne_zero_of_re_pos hs))
    change DifferentiableAt ℂ (fun w => ((Gammaℝ w)⁻¹)⁻¹) s at h
    simpa only [inv_inv] using h
  have hf : DifferentiableAt ℂ xiGamma s := by unfold xiGamma; fun_prop
  exact hf.continuousAt.comp (f := fun y : ℝ => (2 : ℂ)+(c*y : ℝ)*I)
    (show ContinuousAt (fun y : ℝ => (2 : ℂ)+(c*y : ℝ)*I) x by fun_prop)

theorem gaussianShift_norm_bound (q : ℂ) (x : ℝ) :
    ‖gaussianShift q x‖ ≤ Real.exp (q.re^2+q.im^2)*Real.exp (-x^2/2) := by
  rw [gaussianShift, Complex.norm_exp, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  simp only [neg_re, pow_two, mul_re, sub_re, ofReal_re, sub_im, ofReal_im]
  nlinarith [sq_nonneg (x-2*q.re)]

noncomputable def gammaContourWeight (q : ℂ) (c : ℝ) (x : ℝ) : ℂ :=
  gaussianShift q x * xiGamma (2+(c*x : ℝ)*I)

theorem gammaContourWeight_integrable (q : ℂ) (c : ℝ) :
    Integrable (gammaContourWeight q c) := by
  have hg : Integrable (fun x : ℝ => Real.exp (-x^2/2)) := by
    simpa only [neg_mul, one_div_mul_eq_div, neg_div] using
      integrable_exp_neg_mul_sq (b := (1/2 : ℝ)) (by norm_num)
  have hg2 : Integrable (fun x : ℝ => x^2*Real.exp (-x^2/2)) := by
    simpa only [Real.rpow_two, neg_mul, one_div_mul_eq_div, neg_div] using
      integrable_rpow_mul_exp_neg_mul_sq (b := (1/2 : ℝ)) (s := 2) (by norm_num) (by norm_num)
  have hm : Integrable (fun x : ℝ => Real.exp (q.re^2+q.im^2)*
      (18*Real.exp (-x^2/2)+2*c^2*(x^2*Real.exp (-x^2/2)))) :=
    ((hg.const_mul 18).add (hg2.const_mul (2*c^2))).const_mul _
  have hc : Continuous (gammaContourWeight q c) := by
    unfold gammaContourWeight
    exact (show Continuous (fun x : ℝ => gaussianShift q x) by
      unfold gaussianShift; fun_prop).mul (continuous_xiGamma_vertical c)
  apply hm.mono' hc.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro x
  have hp : (3+|c*x|)^2 ≤ 18+2*c^2*x^2 := by
    nlinarith [sq_nonneg (3-|c*x|), sq_abs (c*x)]
  have hnorm := norm_xiGamma_vertical (c*x)
  have h := mul_le_mul (gaussianShift_norm_bound q x) (hnorm.trans hp)
    (norm_nonneg _) (by positivity)
  simpa only [gammaContourWeight, norm_mul] using h.trans_eq (by ring)

noncomputable def plainDirichletTerm (s : ℂ) (k : ℕ) : ℂ :=
  Complex.exp (-s*(Real.log ((k : ℝ)+1) : ℂ))

private theorem plainDirichletTerm_eq (s : ℂ) (k : ℕ) :
    plainDirichletTerm s k = 1/((k : ℂ)+1)^s := by
  have hn : ((k : ℂ)+1) ≠ 0 := by
    exact_mod_cast (show (k : ℝ)+1 ≠ 0 by positivity)
  have hl : Complex.log ((k : ℂ)+1) = (Real.log ((k : ℝ)+1) : ℂ) := by
    rw [show (k : ℂ)+1 = (((k : ℝ)+1 : ℝ) : ℂ) by push_cast; rfl,
      Complex.ofReal_log (by positivity)]
  rw [plainDirichletTerm, cpow_def_of_ne_zero hn, hl, one_div, ← Complex.exp_neg]
  congr 1
  ring

theorem plainDirichletTerm_norm_bound {s : ℂ} (hs : s.re = 2) (k : ℕ) :
    ‖plainDirichletTerm s k‖ ≤ DirichletGaussian.envelope k := by
  rw [plainDirichletTerm_eq, norm_div, norm_one]
  have hpow : ‖((k : ℂ)+1)^s‖ = ((k : ℝ)+1)^2 := by
    rw [show (k : ℂ)+1 = (((k : ℝ)+1 : ℝ) : ℂ) by push_cast; rfl,
      norm_cpow_eq_rpow_re_of_pos (by positivity), hs, Real.rpow_two]
  rw [hpow]
  simpa only [one_div, inv_pow] using DirichletGaussian.inv_sq_le_envelope k

theorem zeta_eq_tsum_plainDirichletTerm {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s = ∑' k, plainDirichletTerm s k := by
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs]
  exact tsum_congr (fun k => (plainDirichletTerm_eq s k).symm)

/-- Termwise integration against any integrable weight on Re(s)=2. -/
theorem hasSum_integral_zeta_vertical {g : ℝ → ℂ} (hg : Integrable g) (c : ℝ) :
    HasSum (fun k => ∫ x : ℝ, g x * plainDirichletTerm (2+(c*x : ℝ)*I) k)
      (∫ x : ℝ, g x * riemannZeta (2+(c*x : ℝ)*I)) := by
  let F : ℕ → ℝ → ℂ := fun k x => g x * plainDirichletTerm (2+(c*x : ℝ)*I) k
  have hb (k : ℕ) (x : ℝ) : ‖F k x‖ ≤ DirichletGaussian.envelope k * ‖g x‖ := by
    dsimp [F]
    rw [norm_mul]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left
      (plainDirichletTerm_norm_bound (by simp : (2+(c*x : ℝ)*I).re = 2) k) (norm_nonneg _)
  have hF (k : ℕ) : Integrable (F k) := by
    apply (hg.norm.const_mul (DirichletGaussian.envelope k)).mono'
    · exact hg.aestronglyMeasurable.mul
        (show Continuous (fun x : ℝ => plainDirichletTerm (2+(c*x : ℝ)*I) k) by
          unfold plainDirichletTerm; fun_prop).aestronglyMeasurable
    · exact Filter.Eventually.of_forall (hb k)
  have hsum : Summable (fun k => ∫ x : ℝ, ‖F k x‖) := by
    apply ((by simpa using (DirichletGaussian.envelope_hasSum 0).summable :
      Summable DirichletGaussian.envelope).mul_right (∫ x : ℝ, ‖g x‖)).of_nonneg_of_le
    · intro k; exact integral_nonneg (fun _ => norm_nonneg _)
    · intro k
      have h := integral_mono (hF k).norm (hg.norm.const_mul (DirichletGaussian.envelope k)) (hb k)
      simpa only [integral_const_mul] using h
  have he : (∫ x : ℝ, ∑' k, F k x) =
      ∫ x : ℝ, g x*riemannZeta (2+(c*x : ℝ)*I) := by
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro x
    simp only [F, tsum_mul_left, ← zeta_eq_tsum_plainDirichletTerm (by simp : 1 < (2+(c*x : ℝ)*I).re)]
  rw [← he]
  exact hasSum_integral_of_summable_integral_norm hF hsum

/-- The value of the absolutely justified termwise integral expansion. -/
theorem integral_zeta_vertical {g : ℝ → ℂ} (hg : Integrable g) (c : ℝ) :
    (∑' k, ∫ x : ℝ, g x * plainDirichletTerm (2+(c*x : ℝ)*I) k) =
      ∫ x : ℝ, g x * riemannZeta (2+(c*x : ℝ)*I) :=
  (hasSum_integral_zeta_vertical hg c).tsum_eq

private theorem xiGamma_mul_zeta_vertical (y : ℝ) :
    xiGamma (2+(y : ℂ)*I)*riemannZeta (2+(y : ℂ)*I) = riemannXi (2+(y : ℂ)*I) := by
  let s : ℂ := 2+(y : ℂ)*I
  have h0 : s ≠ 0 := by intro h; have := congrArg Complex.re h; norm_num [s] at this
  have h1 : s ≠ 1 := by intro h; have := congrArg Complex.re h; norm_num [s] at this
  have hg := Gammaℝ_ne_zero_of_re_pos (s := s) (by simp [s])
  change xiGamma s * riemannZeta s = riemannXi s
  rw [riemannXi_eq_mul_completed h0 h1, riemannZeta_def_of_ne_zero h0, xiGamma]
  field_simp [hg]

noncomputable def dobnerContourTerm (q : ℂ) (c : ℝ) (k : ℕ) : ℂ :=
  ∫ x : ℝ, gammaContourWeight q c x * plainDirichletTerm (2+(c*x : ℝ)*I) k

/-- The contour series is genuinely summable, independently of its value. -/
theorem dobnerContourTerm_summable (q : ℂ) (c : ℝ) : Summable (dobnerContourTerm q c) :=
  (hasSum_integral_zeta_vertical (gammaContourWeight_integrable q c) c).summable

/-- Exact absolutely justified Dirichlet expansion of the Gaussian contour. -/
theorem dobnerContourTerm_tsum (q : ℂ) (c : ℝ) :
    (∑' k, dobnerContourTerm q c k) =
      ∫ x : ℝ, gaussianShift q x * riemannXi (2+(c*x : ℝ)*I) := by
  simp only [dobnerContourTerm]
  rw [integral_zeta_vertical (gammaContourWeight_integrable q c) c]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  dsimp only
  rw [gammaContourWeight, mul_assoc, xiGamma_mul_zeta_vertical]

/-- The contour terms sum to the ACTUAL negative-time heat function. -/
theorem dobnerContourTerm_tsum_eq_heat (q : ℂ) (c : ℝ) :
    (∑' k, dobnerContourTerm q c k) =
      (Real.sqrt Real.pi : ℂ)*xiHeat (-c^2) (2+(c : ℂ)*q*I) := by
  rw [dobnerContourTerm_tsum]
  let z := heatCoordinate (2 : ℂ)
  have harg (x : ℝ) : (1/2 : ℂ)+I*(z+(2*c*x : ℝ))/2 = 2+(c*x : ℝ)*I := by
    dsimp [z, heatCoordinate]
    push_cast
    field_simp
    ring
  have he (x : ℝ) : riemannXi (2+(c*x : ℝ)*I) = 8*H 0 (z+(2*c*x : ℝ)) := by
    rw [H_zero_eq_riemannXi, harg]
    ring
  simp only [he]
  simp_rw [show ∀ x : ℝ, gaussianShift q x*(8*H 0 (z+(2*c*x : ℝ))) =
    8*(gaussianShift q x*H 0 (z+(2*c*x : ℝ))) by intro x; ring]
  rw [integral_const_mul, gaussianShift_average_H_zero]
  have ht : -(2*c)^2/4 = -c^2 := by ring
  have hz : z+(2*c : ℝ)*q = heatCoordinate (2+(c : ℂ)*q*I) := by
    dsimp [z, heatCoordinate]
    push_cast
    field_simp
    ring
  rw [ht, hz]
  unfold xiHeat
  ring

/-- Center of the initial contour for evaluating the logarithmically shifted heat function. -/
noncomputable def dobnerContourCenter (a : ℝ) (s : ℂ) : ℂ :=
  (dobnerMap a s-2)/((2*Real.sqrt a : ℝ)*I)

/-- The concrete normalized contour summand whose saddle asymptotics remain to be proved. -/
noncomputable def normalizedContourTerm (a : ℝ) (s : ℂ) (k : ℕ) : ℂ :=
  dobnerContourTerm (dobnerContourCenter a s) (2*Real.sqrt a) k /
    ((Real.sqrt Real.pi : ℂ)*dobnerGamma a s)

theorem normalizedContourTerm_summable (a : ℝ) (s : ℂ) :
    Summable (normalizedContourTerm a s) :=
  (dobnerContourTerm_summable _ _).div_const _

/-- An exact series for the ACTUAL normalized heat function. There is no
replacement by the Gaussian Dirichlet main term in this identity. -/
theorem normalizedContourTerm_tsum {a : ℝ} (ha : 0 < a) (s : ℂ) :
    (∑' k, normalizedContourTerm a s k) = normalizedHeat a s := by
  have hc : (Real.sqrt a : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr ha).ne'
  have ht : -(2*Real.sqrt a)^2 = -4*a := by nlinarith [Real.sq_sqrt ha.le]
  have hz : (2 : ℂ)+(2*Real.sqrt a : ℝ)*dobnerContourCenter a s*I = dobnerMap a s := by
    unfold dobnerContourCenter
    push_cast
    field_simp [hc]
    ring
  simp only [normalizedContourTerm, tsum_div_const]
  rw [dobnerContourTerm_tsum_eq_heat, ht, hz]
  unfold normalizedHeat
  exact mul_div_mul_left _ _ (show (Real.sqrt Real.pi : ℂ) ≠ 0 by
    exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne')

/-- Exact residual series. Proving its uniform decay is the remaining analytic
step; this identity alone does not bound the residual. -/
theorem normalizedHeat_sub_series {a : ℝ} (ha : 0 < a) (s : ℂ) :
    normalizedHeat a s - DirichletGaussian.series a s =
      ∑' k, (normalizedContourTerm a s k - DirichletGaussian.term a s k) := by
  rw [← normalizedContourTerm_tsum ha s, DirichletGaussian.series,
    ← (normalizedContourTerm_summable a s).tsum_sub (DirichletGaussian.summable_term ha s)]

end LeanCert.Analysis.DBN
