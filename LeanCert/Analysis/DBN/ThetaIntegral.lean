import LeanCert.Analysis.DBN.ThetaDerivatives
import LeanCert.Analysis.DBN.HeatFlow
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# The cosine-transform identity for the actual heat integral at time zero

The integration-by-parts boundary term is retained. No xi identity is assumed.
-/
namespace LeanCert.Analysis.DBN
open MeasureTheory Set Filter
open scoped Topology

private theorem kernel_as_theta (u : ℝ) (n : ℕ) :
    kernelTerm u n =
      (2*(Real.pi*((n : ℝ)+1)^2*Real.exp (4*u))^2 -
        3*(Real.pi*((n : ℝ)+1)^2*Real.exp (4*u))) * thetaTerm u n := by
  have h9 : Real.exp (9*u) = Real.exp (4*u)^2 * Real.exp u := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; ring
  have h5 : Real.exp (5*u) = Real.exp (4*u) * Real.exp u := by
    rw [← Real.exp_add]; congr 1; ring
  simp only [kernelTerm, thetaTerm, h9, h5]
  ring

private theorem theta_term_domination {u : ℝ} (hu : 0 ≤ u) (n : ℕ) :
    ‖thetaTerm u n‖ ≤ kernelTerm u n ∧
      ‖thetaTermDeriv u n‖ ≤ 2 * kernelTerm u n := by
  let a := Real.pi*((n : ℝ)+1)^2*Real.exp (4*u)
  have hn : (1 : ℝ) ≤ ((n : ℝ)+1)^2 := by
    have : (0 : ℝ) ≤ n := by positivity
    nlinarith
  have he : 1 ≤ Real.exp (4*u) := Real.one_le_exp (by positivity)
  have ha : 3 ≤ a := by
    have h := mul_le_mul hn he (by positivity) (by positivity)
    have h' := mul_le_mul_of_nonneg_left h Real.pi_pos.le
    dsimp [a]
    nlinarith [Real.pi_gt_three]
  have hp : 0 ≤ thetaTerm u n := by unfold thetaTerm; positivity
  rw [kernel_as_theta]
  change ‖thetaTerm u n‖ ≤ (2*a^2-3*a)*thetaTerm u n ∧
    ‖(1-4*a)*thetaTerm u n‖ ≤ 2*((2*a^2-3*a)*thetaTerm u n)
  rw [Real.norm_of_nonneg hp, norm_mul, Real.norm_eq_abs, Real.norm_of_nonneg hp]
  have h1 : 1 ≤ 2*a^2-3*a := by nlinarith [sq_nonneg (a-3)]
  have h2 : |1-4*a| ≤ 2*(2*a^2-3*a) := by
    rw [abs_of_nonpos (by linarith)]
    nlinarith [sq_nonneg (a-3)]
  constructor
  · simpa using mul_le_mul_of_nonneg_right h1 hp
  · nlinarith [mul_le_mul_of_nonneg_right h2 hp]

theorem thetaPrimitive_norm_le_Phi {u : ℝ} (hu : 0 ≤ u) :
    ‖thetaPrimitive u‖ ≤ ‖Phi u‖ := by
  rw [thetaPrimitive_eq_tsum]
  exact (norm_tsum_le_tsum_norm (hasSum_thetaTerm u).summable.norm).trans
    (((hasSum_thetaTerm u).summable.norm.tsum_le_tsum
      (fun n => (theta_term_domination hu n).1) (kernel_summable u)).trans (le_abs_self (Phi u)))

theorem deriv_thetaPrimitive_norm_le_Phi {u : ℝ} (hu : 0 ≤ u) :
    ‖deriv thetaPrimitive u‖ ≤ 2 * ‖Phi u‖ := by
  rw [deriv_thetaPrimitive]
  apply (norm_tsum_le_tsum_norm (summable_thetaTermDeriv u).norm).trans
  have h := (summable_thetaTermDeriv u).norm.tsum_le_tsum
    (fun n => (theta_term_domination hu n).2) ((kernel_summable u).mul_left 2)
  rw [tsum_mul_left] at h
  exact h.trans (mul_le_mul_of_nonneg_left (le_abs_self (Phi u)) (by norm_num))

/-- The absolutely convergent cosine transform of the theta primitive. -/
noncomputable def thetaCosIntegrand (z : ℂ) (u : ℝ) : ℂ :=
  (thetaPrimitive u : ℂ) * Complex.cos (z * (u : ℂ))

noncomputable def thetaCosIntegral (z : ℂ) : ℂ :=
  ∫ u in Ioi (0 : ℝ), thetaCosIntegrand z u

private theorem trig_cos_bound (z : ℂ) {u : ℝ} (hu : 0 ≤ u) :
    ‖Complex.cos (z*(u : ℂ))‖ ≤ Real.exp (|z.im| * u) := by
  simpa [Complex.mul_im, abs_mul, abs_of_nonneg hu] using
    norm_cos_le_exp_abs_im (z*(u : ℂ))

private theorem trig_sin_bound (z : ℂ) {u : ℝ} (hu : 0 ≤ u) :
    ‖Complex.sin (z*(u : ℂ))‖ ≤ Real.exp (|z.im| * u) := by
  rw [← Complex.cos_sub_pi_div_two]
  simpa [Complex.sub_im, Complex.mul_im, abs_mul, abs_of_nonneg hu] using
    norm_cos_le_exp_abs_im (z*(u : ℂ)-Real.pi/2)

theorem thetaCosIntegrand_bound (z : ℂ) {u : ℝ} (hu : 0 ≤ u) :
    ‖thetaCosIntegrand z u‖ ≤ heatMajorant 0 z * Real.exp (-u^2) := by
  have h := mul_le_mul (thetaPrimitive_norm_le_Phi hu) (trig_cos_bound z hu)
    (norm_nonneg _) (norm_nonneg _)
  have hw := heat_weight_bound 0 z hu
  simpa [thetaCosIntegrand, norm_mul] using h.trans (by simpa using hw)

theorem thetaCosIntegrand_integrable (z : ℂ) :
    IntegrableOn (thetaCosIntegrand z) (Ioi 0) := by
  have hc : Continuous (thetaCosIntegrand z) := by
    have hf := differentiable_thetaPrimitive.continuous
    unfold thetaCosIntegrand
    fun_prop
  have hg : IntegrableOn (fun u : ℝ => heatMajorant 0 z * Real.exp (-u^2)) (Ioi 0) := by
    simpa only [IntegrableOn, neg_mul, one_mul] using
      (integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1)).integrableOn.const_mul
        (heatMajorant 0 z)
  apply hg.mono' hc.measurable.aestronglyMeasurable
  exact (ae_restrict_iff' measurableSet_Ioi).mpr
    (Eventually.of_forall (fun u hu => thetaCosIntegrand_bound z hu.le))

/-- The boundary expression for two integrations by parts. -/
noncomputable def thetaBoundary (z : ℂ) (u : ℝ) : ℂ :=
  ((deriv thetaPrimitive u : ℝ) : ℂ) * Complex.cos (z*(u : ℂ)) +
    z * (thetaPrimitive u : ℂ) * Complex.sin (z*(u : ℂ))

theorem thetaBoundary_zero (z : ℂ) : thetaBoundary z 0 = -1/2 := by
  simp [thetaBoundary, hasDerivAt_thetaPrimitive_zero.deriv]

theorem thetaBoundary_bound (z : ℂ) {u : ℝ} (hu : 0 ≤ u) :
    ‖thetaBoundary z u‖ ≤ (2+‖z‖) * (heatMajorant 0 z * Real.exp (-u^2)) := by
  have h1 := mul_le_mul (deriv_thetaPrimitive_norm_le_Phi hu) (trig_cos_bound z hu)
    (norm_nonneg _) (by positivity)
  have h2 := mul_le_mul (thetaPrimitive_norm_le_Phi hu) (trig_sin_bound z hu)
    (norm_nonneg _) (norm_nonneg _)
  have hw : ‖Phi u‖ * Real.exp (|z.im| * u) ≤ heatMajorant 0 z * Real.exp (-u^2) :=
    by simpa using heat_weight_bound 0 z hu
  have hn := norm_add_le
    (((deriv thetaPrimitive u : ℝ) : ℂ) * Complex.cos (z*(u : ℂ)))
    (z * (thetaPrimitive u : ℂ) * Complex.sin (z*(u : ℂ)))
  simp only [norm_mul, Complex.norm_real] at hn
  change ‖thetaBoundary z u‖ ≤ _ at hn
  nlinarith [mul_le_mul_of_nonneg_left h2 (norm_nonneg z),
    mul_le_mul_of_nonneg_left hw (norm_nonneg z)]

theorem thetaBoundary_tendsto_zero (z : ℂ) : Tendsto (thetaBoundary z) atTop (𝓝 0) := by
  have hg : Tendsto (fun u : ℝ => Real.exp (-u^2)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp (tendsto_pow_atTop two_ne_zero))
  apply squeeze_zero_norm' _ (by simpa using (hg.const_mul (heatMajorant 0 z)).const_mul (2+‖z‖))
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with u hu
  exact thetaBoundary_bound z hu

theorem hasDerivAt_thetaBoundary (z : ℂ) (u : ℝ) :
    HasDerivAt (thetaBoundary z)
      (8 * heatIntegrand 0 z u + (1+z^2)*thetaCosIntegrand z u) u := by
  have hf := (hasDerivAt_thetaPrimitive u).ofReal_comp
  have hf' := (hasDerivAt_deriv_thetaPrimitive u).ofReal_comp
  have hz := (Complex.ofRealCLM.hasDerivAt (x := u)).const_mul z
  have hc := (Complex.hasDerivAt_cos (z*(u : ℂ))).comp u hz
  have hs := (Complex.hasDerivAt_sin (z*(u : ℂ))).comp u hz
  have h := (hf'.mul hc).add ((hf.const_mul z).mul hs)
  rw [← deriv_thetaPrimitive] at h
  convert! h using 1
  simp only [heatIntegrand, thetaCosIntegrand, zero_mul, Real.exp_zero, one_mul,
    Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_ofNat, Function.comp_apply,
    Complex.ofRealCLM_apply, Complex.ofReal_one, mul_one]
  ring

/-- Exact identity for the actual H_0 integral, with its nonzero endpoint term. -/
theorem H_zero_eq_thetaCosIntegral (z : ℂ) :
    H 0 z = 1/16 - (z^2+1)*thetaCosIntegral z/8 := by
  have hi := ((heatIntegrand_integrable 0 z).const_mul (8 : ℂ)).add
    ((thetaCosIntegrand_integrable z).const_mul (1+z^2))
  have h := integral_Ioi_of_hasDerivAt_of_tendsto'
    (fun u (_ : u ∈ Ici (0 : ℝ)) => hasDerivAt_thetaBoundary z u) hi
    (thetaBoundary_tendsto_zero z)
  rw [thetaBoundary_zero] at h
  rw [integral_add ((heatIntegrand_integrable 0 z).const_mul (8 : ℂ))
    ((thetaCosIntegrand_integrable z).const_mul (1+z^2)), integral_const_mul,
    integral_const_mul] at h
  change 8 * H 0 z + (1+z^2)*thetaCosIntegral z = 0 - (-1/2) at h
  linear_combination h / 8

/-- An exact value of the actual heat integral at an initial-strip endpoint. -/
theorem H_zero_I : H 0 Complex.I = 1/16 := by
  rw [H_zero_eq_thetaCosIntegral]
  norm_num [Complex.I_sq]

theorem H_zero_neg_I : H 0 (-Complex.I) = 1/16 := by
  rw [H_zero_eq_thetaCosIntegral]
  norm_num [Complex.I_sq]

end LeanCert.Analysis.DBN
