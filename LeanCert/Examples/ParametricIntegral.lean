import LeanCert.Analysis.ParametricIntegral
import LeanCert.Analysis.GaussianMoments
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Util.AssertNoSorry

/-! Differentiation of a non-DBN Gaussian sine transform using the shared
continuous-majorant adapter. No closed form of the transform is used. -/
namespace LeanCert.Examples.ParametricIntegral
open MeasureTheory Set Filter

theorem sine_gaussian_derivative (s : ℝ) :
    HasDerivAt (fun r : ℝ => ∫ u in Ioi (0 : ℝ), Real.sin (r*u)*Real.exp (-u^2))
      (∫ u in Ioi (0 : ℝ), (u*Real.cos (s*u))*Real.exp (-u^2)) s := by
  have hi : IntegrableOn (fun u : ℝ => Real.sin (s*u)*Real.exp (-u^2)) (Ioi 0) := by
    apply (integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1)).integrableOn.mono'
      (by fun_prop)
    apply Eventually.of_forall
    intro u
    simp only [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    simpa using mul_le_mul_of_nonneg_right (Real.abs_sin_le_one (s*u)) (Real.exp_pos (-u^2)).le
  apply (Analysis.ParametricIntegral.hasDerivAt_integral
    (fun r u => Real.sin (r*u)*Real.exp (-u^2))
    (fun r u => (u*Real.cos (r*u))*Real.exp (-u^2))
    (fun _ : ℝ => (1 : ℝ)) (fun u : ℝ => u*Real.exp (-u^2)) continuous_const
    (by simpa only [IntegrableOn, pow_one] using Analysis.integrableOn_gaussian_moment 1) _
    (fun _ => by fun_prop) (fun _ => by fun_prop) _ _ s hi).2
  · exact (ae_restrict_iff' measurableSet_Ioi).mpr
      (Eventually.of_forall fun u hu => mul_nonneg hu.le (Real.exp_pos _).le)
  · apply (ae_restrict_iff' measurableSet_Ioi).mpr
    apply Eventually.of_forall
    intro u hu r
    have hu0 : 0 ≤ u := (mem_Ioi.mp hu).le
    simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg hu0, abs_of_pos (Real.exp_pos _), one_mul]
    exact mul_le_mul_of_nonneg_right
      (by simpa using mul_le_mul_of_nonneg_left (Real.abs_cos_le_one (r*u)) hu0)
      (Real.exp_pos _).le
  · apply Eventually.of_forall
    intro u r
    convert! ((Real.hasDerivAt_sin (r*u)).comp r ((hasDerivAt_id r).mul_const u)).mul_const
      (Real.exp (-u^2)) using 1
    ring

assert_no_sorry sine_gaussian_derivative
/-- info: 'LeanCert.Examples.ParametricIntegral.sine_gaussian_derivative' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms sine_gaussian_derivative

end LeanCert.Examples.ParametricIntegral
