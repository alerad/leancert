import LeanCert.Analysis.DBN.HeatShift
import Mathlib.Util.AssertNoSorry

namespace LeanCert.Test.DBNHeatShift
open Analysis.DBN Complex Polynomial

example (t : ℝ) : H t 0 ≠ 0 := H_zero_ne_zero t
example : 0 < (H (1/2) 0).re := H_zero_re_pos (1/2)
example {u : ℝ} (hu : 0 ≤ u) : 0 < Phi u := Phi_pos hu
example (a : ℝ) (p : ℂ[X]) : shiftPolynomialIter a 0 p = p := rfl
example (t a : ℝ) (z : ℂ) :
    shiftIter a 0 (H t) z = H t z := rfl
example (p : ℂ[X]) (hp : p ≠ 0) (hc : p.map (starRingEnd ℂ) = p)
    (hs : ∀ z : ℂ, p.eval z = 0 → z.im^2 ≤ 1) (n : ℕ) (hn : 0 < n)
    {z : ℂ} (hz : (shiftPolynomialIter (Real.sqrt (1/(n : ℝ))) n p).eval z = 0) :
    z.im = 0 := shiftPolynomialIter_unit_real p hp hc hs n hn hz
example (t a : ℝ) (n : ℕ) (z : ℂ) :
    shiftIter a n (H t) z = ∫ u in Set.Ioi (0 : ℝ), shiftHeatIntegrand t a n z u :=
  shiftIter_H_eq_integral t a n z

assert_no_sorry Phi_pos
assert_no_sorry H_zero_ne_zero
assert_no_sorry shiftPolynomialIter_unit_real
assert_no_sorry shiftIter_H_eq_integral
assert_no_sorry shiftHeatIntegrand_bound_unit
/-- info: 'LeanCert.Analysis.DBN.H_zero_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms H_zero_ne_zero
/-- info: 'LeanCert.Analysis.DBN.shiftPolynomialIter_unit_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms shiftPolynomialIter_unit_real
/-- info: 'LeanCert.Analysis.DBN.shiftIter_H_eq_integral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms shiftIter_H_eq_integral
/-- info: 'LeanCert.Analysis.DBN.shiftHeatIntegrand_bound_unit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms shiftHeatIntegrand_bound_unit

end LeanCert.Test.DBNHeatShift
