import LeanCert.Analysis.DBN.HeatRegularity
import Mathlib.Util.AssertNoSorry

/-! Reusable growth estimates and their application to the actual heat integral. -/
namespace LeanCert.Examples.HeatKernel

/-- Polynomial absorption, independent of any DBN definitions. -/
theorem quartic_decay (x : ℝ) (hx : 0 ≤ x) :
    x^4 * Real.exp (-x) ≤ 384 * Real.exp (-x/2) := by
  have h := Analysis.pow_mul_exp_neg_le x hx 4
  norm_num at h
  exact h

/-- Uniform control of complex cosine on a horizontal strip. -/
theorem cosine_strip {z : ℂ} {Y : ℝ} (hz : |z.im| ≤ Y) :
    ‖Complex.cos z‖ ≤ Real.exp Y :=
  (Analysis.norm_cos_le_exp_abs_im z).trans (Real.exp_le_exp.mpr hz)

open MeasureTheory Set Analysis.DBN in
/-- A finite quadrature can approximate the genuine H integral with a proved
tail; the statement does not supply the finite quadrature enclosure itself. -/
theorem heat_quadrature_error (t : ℝ) (z : ℂ) {b : ℝ} (hb : 0 < b) :
    ‖H t z - ∫ u in (0 : ℝ)..b, heatIntegrand t z u‖ ≤
      heatMajorant t z * Real.exp (-b^2) / b := H_tail t z b hb

assert_no_sorry quartic_decay
assert_no_sorry cosine_strip
assert_no_sorry heat_quadrature_error

/-- The heat equation is an identity for the actual integral, not an assumption. -/
theorem heat_equation (t : ℝ) (z : ℂ) :
    deriv (fun s : ℝ => Analysis.DBN.H s z) t =
      -deriv (deriv (Analysis.DBN.H t)) z := Analysis.DBN.heat_equation t z

assert_no_sorry heat_equation
/-- info: 'LeanCert.Examples.HeatKernel.heat_quadrature_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms heat_quadrature_error

end LeanCert.Examples.HeatKernel
