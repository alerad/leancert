import LeanCert.Analysis.DBN.HeatRegularity
import LeanCert.Examples.ParametricIntegral
import Mathlib.Util.AssertNoSorry

namespace LeanCert.Test.HeatRegularity
open Analysis.DBN MeasureTheory Set

-- Joint continuity can be composed with paths varying time and space together.
example : Continuous (fun r : ℝ => H r ((r : ℂ)+Complex.I)) :=
  continuous_H.comp (by fun_prop : Continuous (fun r : ℝ => (r, (r : ℂ)+Complex.I)))
example (t : ℝ) : Differentiable ℂ (H t) := H_entire t
example (m : ℕ) (t : ℝ) (z : ℂ) :
    HasDerivAt (moment m t) (moment (m+1) t z) z := hasDerivAt_moment_z m t z

-- No strictly positive time hypothesis: the full real derivative exists at zero.
example (z : ℂ) : HasDerivAt (fun s : ℝ => H s z) (-moment 2 0 z) 0 := hasDerivAt_H_t 0 z
example (z : ℂ) : deriv (fun s : ℝ => H s z) (-1) = -deriv (deriv (H (-1))) z :=
  heat_equation (-1) z
example (t : ℝ) (z : ℂ) :
    HasDerivAt (fun s : ℝ => H s z)
      (∫ u in Ioi (0 : ℝ), (u : ℂ)^2 * heatIntegrand t z u) t := hasDerivAt_H_t_integral t z

-- Pin the derivative sign and phase convention, including u=0.
example (t : ℝ) (z : ℂ) (u : ℝ) :
    momentIntegrand 2 t z u = -((u : ℂ)^2*heatIntegrand t z u) := momentIntegrand_two t z u
example (t : ℝ) (z : ℂ) : momentIntegrand 2 t z 0 = 0 := by simp [momentIntegrand_two]
example (t : ℝ) (z : ℂ) : moment 0 t z = H t z := moment_zero t z
example (t : ℝ) (z : ℂ) : H t (-z) = H t z := H_even t z
example (t : ℝ) (z : ℂ) : H t (starRingEnd ℂ z) = starRingEnd ℂ (H t z) := H_conj t z
example (t x : ℝ) : (H t (x : ℂ)).im = 0 := H_real t x
example : IntegrableOn (fun u : ℝ => u^0*Real.exp (-u^2)) (Ioi 0) :=
  Analysis.integrableOn_gaussian_moment 0

assert_no_sorry Analysis.ParametricIntegral.continuous_integral
assert_no_sorry Analysis.ParametricIntegral.hasDerivAt_integral
assert_no_sorry continuous_H
assert_no_sorry hasDerivAt_moment_z
assert_no_sorry H_entire
assert_no_sorry hasDerivAt_H_t_integral
assert_no_sorry heat_equation
assert_no_sorry H_even
assert_no_sorry H_conj
assert_no_sorry H_real
/-- info: 'LeanCert.Analysis.DBN.heat_equation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms heat_equation
/-- info: 'LeanCert.Analysis.DBN.H_entire' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms H_entire
/-- info: 'LeanCert.Analysis.DBN.H_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms H_real

end LeanCert.Test.HeatRegularity
