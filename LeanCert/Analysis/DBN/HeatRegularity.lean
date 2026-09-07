import LeanCert.Analysis.DBN.HeatMoments
import LeanCert.Analysis.DBN.HeatSymmetry

/-! Joint continuity, entire spatial dependence, and the backward heat equation
for the actual de Bruijn–Newman heat integral. -/
namespace LeanCert.Analysis.DBN
open MeasureTheory Set Filter

theorem continuous_H : Continuous (fun p : ℝ × ℂ => H p.1 p.2) := by
  simpa only [moment_zero] using continuous_moment 0

theorem hasDerivAt_H_z (t : ℝ) (z : ℂ) : HasDerivAt (H t) (moment 1 t z) z := by
  have h := hasDerivAt_moment_z 0 t z
  rw [show moment 0 t = H t from funext (moment_zero t)] at h
  exact h

/-- Entire means complex differentiability at every complex argument. -/
theorem H_entire (t : ℝ) : Differentiable ℂ (H t) :=
  fun z => (hasDerivAt_H_z t z).differentiableAt

theorem deriv_H_z (t : ℝ) : deriv (H t) = moment 1 t :=
  funext fun z => (hasDerivAt_H_z t z).deriv

theorem deriv2_H_z (t : ℝ) (z : ℂ) : deriv (deriv (H t)) z = moment 2 t z := by
  rw [deriv_H_z]
  exact (hasDerivAt_moment_z 1 t z).deriv

theorem momentIntegrand_two (t : ℝ) (z : ℂ) (u : ℝ) :
    momentIntegrand 2 t z u = -((u : ℂ)^2 * heatIntegrand t z u) := by
  unfold momentIntegrand heatIntegrand
  norm_num only [Nat.cast_ofNat]
  rw [show (2 : ℂ)*(Real.pi : ℂ)/2 = (Real.pi : ℂ) by ring, Complex.cos_add_pi]
  ring

theorem hasDerivAt_heatIntegrand_t (t u : ℝ) (z : ℂ) :
    HasDerivAt (fun s : ℝ => heatIntegrand s z u) (-momentIntegrand 2 t z u) t := by
  have hd := (((Real.hasDerivAt_exp (t*u^2)).comp t ((hasDerivAt_id t).mul_const (u^2))).mul_const
    (Phi u)).ofReal_comp.mul_const (Complex.cos (z*(u : ℂ)))
  convert! hd using 1
  rw [momentIntegrand_two]
  unfold heatIntegrand
  push_cast
  ring

/-- Differentiation in real time, including at t=0, with no boundary restriction. -/
theorem hasDerivAt_H_t (t : ℝ) (z : ℂ) :
    HasDerivAt (fun s : ℝ => H s z) (-moment 2 t z) t := by
  have h := (ParametricIntegral.hasDerivAt_integral
    (fun s u => heatIntegrand s z u) (fun s u => -momentIntegrand 2 s z u)
    (fun s => heatMajorant s z) (fun u : ℝ => u^2*Real.exp (-u^2))
    (by unfold heatMajorant; fun_prop) (integrableOn_gaussian_moment 2)
    ((ae_restrict_iff' measurableSet_Ioi).mpr
      (Eventually.of_forall fun u _ => mul_nonneg (sq_nonneg u) (Real.exp_pos _).le))
    (fun s => (measurable_heatIntegrand s z).aestronglyMeasurable)
    (fun s => (measurable_momentIntegrand 2 s z).neg.aestronglyMeasurable)
    ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun u hu s => by
      simpa only [norm_neg] using momentIntegrand_bound 2 s z hu.le))
    (Eventually.of_forall fun u s => hasDerivAt_heatIntegrand_t s u z)
    t (heatIntegrand_integrable t z)).2
  simpa only [H, moment, integral_neg] using h

/-- The real-time derivative as the integral of the explicit u²-weighted kernel. -/
theorem hasDerivAt_H_t_integral (t : ℝ) (z : ℂ) :
    HasDerivAt (fun s : ℝ => H s z)
      (∫ u in Ioi (0 : ℝ), (u : ℂ)^2 * heatIntegrand t z u) t := by
  simpa only [moment, momentIntegrand_two, integral_neg, neg_neg] using hasDerivAt_H_t t z

/-- Sign dictated by exp(t*u²) and the second derivative of cos(z*u). -/
theorem heat_equation (t : ℝ) (z : ℂ) :
    deriv (fun s : ℝ => H s z) t = -deriv (deriv (H t)) z := by
  rw [(hasDerivAt_H_t t z).deriv, deriv2_H_z]

end LeanCert.Analysis.DBN
