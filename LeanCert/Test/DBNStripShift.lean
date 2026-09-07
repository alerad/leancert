import LeanCert.Analysis.DBN.StripShift
import Mathlib.Util.AssertNoSorry

namespace LeanCert.Test.DBNStripShift
open Analysis.DBN Complex Polynomial

-- The zero shift is exactly the identity.
example (f : ℂ → ℂ) (z : ℂ) : shiftAverage f 0 z = f z := by
  simp [shiftAverage]

-- Nonzero constants stay nonzero.
example {c : ℂ} (hc : c ≠ 0) (a : ℝ) (z : ℂ) :
    shiftAverage (fun _ => c) a z ≠ 0 := by
  simpa [shiftAverage] using hc

-- Quadratics realize the exact squared-width change.
example (a b : ℝ) (z : ℂ) :
    shiftAverage (fun w => w^2 + (b : ℂ)^2) a z = z^2 + (b : ℂ)^2 - (a : ℂ)^2 := by
  simp only [shiftAverage]
  linear_combination ((a : ℂ)^2) * I_mul_I

-- A repeated real root is covered without a simplicity assumption.
example {a : ℝ} (ha : 0 < a) {z : ℂ}
    (hz : shiftAverage (fun w => w^2) a z = 0) : z.im = 0 := by
  apply polynomial_shiftAverage_real (X^2 : ℂ[X]) (by simp) (by simp) ha
    (b := 0) (by simpa using sq_nonneg a) ?_ (by simpa using hz)
  intro r hr
  simp only [eval_pow, eval_X, pow_eq_zero_iff (by decide : 2 ≠ 0)] at hr
  simp [hr]

assert_no_sorry conjugate_pair_shift_difference
assert_no_sorry rootProduct_shift_lt
assert_no_sorry polynomial_shiftAverage_strip
assert_no_sorry polynomial_shiftAverage_real
assert_no_sorry realPolynomial_shiftAverage_strip
/-- info: 'LeanCert.Analysis.DBN.polynomial_shiftAverage_strip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms polynomial_shiftAverage_strip
/-- info: 'LeanCert.Analysis.DBN.realPolynomial_shiftAverage_strip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms realPolynomial_shiftAverage_strip

end LeanCert.Test.DBNStripShift
