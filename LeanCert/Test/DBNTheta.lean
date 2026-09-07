import LeanCert.Analysis.DBN.ThetaIntegral
import Mathlib.Util.AssertNoSorry

namespace LeanCert.Test.DBNTheta
open Analysis.DBN

-- Keep the theta series indexed by n+1, matching the actual DBN kernel.
example (u : ℝ) : thetaTerm u 0 =
    Real.exp u * Real.exp (-Real.pi * Real.exp (4*u)) := by simp [thetaTerm]
example (u : ℝ) : HasSum (thetaTerm u) (thetaPrimitive u) := hasSum_thetaTerm u
example (u : ℝ) : thetaLift (-u) = thetaLift u := thetaLift_even u
example : HasDerivAt thetaLift 0 0 := hasDerivAt_thetaLift_zero
example : deriv thetaPrimitive 0 = -1/2 := hasDerivAt_thetaPrimitive_zero.deriv
example : (∑' n, thetaTermDeriv 0 n) = -1/2 := by
  rw [← deriv_thetaPrimitive, hasDerivAt_thetaPrimitive_zero.deriv]

-- Local bounds work on either side of zero, not just on the integration half-line.
example : DifferentiableAt ℝ thetaPrimitive (-1) := differentiable_thetaPrimitive (-1)
example : HasDerivAt (deriv thetaPrimitive)
    (8 * Phi (-1) + thetaPrimitive (-1)) (-1) := hasDerivAt_deriv_thetaPrimitive (-1)
example (u : ℝ) : HasDerivAt (deriv thetaPrimitive)
    (8 * Phi u + thetaPrimitive u) u := hasDerivAt_deriv_thetaPrimitive u
example (u : ℝ) : Phi u =
    (deriv (deriv thetaPrimitive) u - thetaPrimitive u) / 8 :=
  Phi_eq_thetaPrimitive_deriv2 u

-- All complex arguments are permitted; no decay/endpoint assumptions are left to callers.
example (z : ℂ) : MeasureTheory.IntegrableOn (thetaCosIntegrand z) (Set.Ioi 0) :=
  thetaCosIntegrand_integrable z
example (z : ℂ) : thetaBoundary z 0 = -1/2 := thetaBoundary_zero z
example (z : ℂ) : H 0 z = 1/16 - (z^2+1)*thetaCosIntegral z/8 :=
  H_zero_eq_thetaCosIntegral z
example : H 0 Complex.I = 1/16 := H_zero_I
example : H 0 (-Complex.I) = 1/16 := H_zero_neg_I
example : H 0 Complex.I ≠ 0 := by rw [H_zero_I]; norm_num
example : H 0 (-Complex.I) ≠ 0 := by rw [H_zero_neg_I]; norm_num

assert_no_sorry hasSum_thetaTerm
assert_no_sorry thetaLift_even
assert_no_sorry hasDerivAt_thetaLift_zero
assert_no_sorry hasDerivAt_thetaPrimitive_zero
assert_no_sorry hasDerivAt_thetaPrimitive
assert_no_sorry hasDerivAt_deriv_thetaPrimitive
assert_no_sorry Phi_eq_thetaPrimitive_deriv2
assert_no_sorry thetaCosIntegrand_integrable
assert_no_sorry thetaBoundary_tendsto_zero
assert_no_sorry H_zero_eq_thetaCosIntegral
assert_no_sorry H_zero_I
assert_no_sorry H_zero_neg_I
/-- info: 'LeanCert.Analysis.DBN.hasDerivAt_thetaPrimitive_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms hasDerivAt_thetaPrimitive_zero
/-- info: 'LeanCert.Analysis.DBN.Phi_eq_thetaPrimitive_deriv2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Phi_eq_thetaPrimitive_deriv2
/-- info: 'LeanCert.Analysis.DBN.H_zero_eq_thetaCosIntegral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms H_zero_eq_thetaCosIntegral
/-- info: 'LeanCert.Analysis.DBN.H_zero_I' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms H_zero_I

end LeanCert.Test.DBNTheta
