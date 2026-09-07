import LeanCert.Examples.HeatKernel
import Mathlib.Util.AssertNoSorry

namespace LeanCert.Test.HeatKernel
open Analysis.DBN MeasureTheory Set

-- Pin the exact downstream series normalization without importing its stubs.
example (u : ℝ) : Phi u = ∑' n : ℕ,
    (2 * Real.pi ^ 2 * ((n : ℝ) + 1) ^ 4 * Real.exp (9 * u)
        - 3 * Real.pi * ((n : ℝ) + 1) ^ 2 * Real.exp (5 * u))
      * Real.exp (-Real.pi * ((n : ℝ) + 1) ^ 2 * Real.exp (4 * u)) := rfl
example (t : ℝ) (z : ℂ) : H t z = ∫ u in Ioi (0 : ℝ),
    ((Real.exp (t * u ^ 2) * Phi u : ℝ) : ℂ) * Complex.cos (z * (u : ℂ)) := rfl

-- Zero-based summand 0 is positive index 1, not a vanishing n=0 term.
example : kernelTerm 0 0 = (2*Real.pi^2-3*Real.pi)*Real.exp (-Real.pi) := by
  norm_num [kernelTerm]
example (u : ℝ) : Summable (fun n => ‖kernelTerm u n‖) := kernel_norm_summable u
example : Summable (kernelTerm (-10)) := kernel_summable _
example (u : ℝ) : ‖Phi u‖ ≤ 22*Real.exp u*Real.exp (-kernelScale u) /
    (1-Real.exp (-3*kernelScale u)) := Phi_bound u
example (u : ℝ) : ‖Phi u - kernelTerm u 0‖ ≤
    22*Real.exp u*Real.exp (-kernelScale u*4) / (1-Real.exp (-kernelScale u*5)) := by
  have h := (kernel_tail u 1).2
  norm_num at h ⊢
  exact h

-- Endpoint and time checks: no t>0 assumption is hidden in integrability.
example (u : ℝ) : heatIntegrand 0 0 u = (Phi u : ℂ) := by simp [heatIntegrand]
example : IntegrableOn (heatIntegrand 0 Complex.I) (Ioi 0) := heatIntegrand_integrable _ _
example : IntegrableOn (heatIntegrand (-10) (3+2*Complex.I)) (Ioi 0) := heatIntegrand_integrable _ _
example (t : ℝ) (z : ℂ) : ‖heatIntegrand t z 0‖ ≤ heatMajorant t z := by
  simpa using heatIntegrand_bound t z (u := 0) (by norm_num)
example : ¬ (0 : ℝ) < 0 := by norm_num -- the tail formula requires a positive cutoff
example : (0 : ℝ)^0 * Real.exp (-0) ≤ (2^0 * (Nat.factorial 0 : ℝ))*Real.exp (-0/2) :=
  Analysis.pow_mul_exp_neg_le 0 (by norm_num) 0

assert_no_sorry kernelTerm_bound
assert_no_sorry kernel_tail
assert_no_sorry kernel_norm_summable
assert_no_sorry Phi_bound_nonneg
assert_no_sorry measurable_Phi
assert_no_sorry heatIntegrand_bound
assert_no_sorry heatIntegrand_bound_box
assert_no_sorry heatIntegrand_integrable
assert_no_sorry H_tail
/-- info: 'LeanCert.Analysis.DBN.kernel_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms kernel_tail
/-- info: 'LeanCert.Analysis.DBN.heatIntegrand_integrable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms heatIntegrand_integrable

end LeanCert.Test.HeatKernel
