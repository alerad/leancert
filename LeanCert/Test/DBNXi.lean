import LeanCert.Analysis.DBN.XiIdentity
import Mathlib.Util.AssertNoSorry

namespace LeanCert.Test.DBNXi
open Analysis.DBN Complex

-- These values guard against introducing spurious zeros at the removed poles.
example : riemannXi 0 = 1 / 2 := riemannXi_zero
example : riemannXi 1 = 1 / 2 := riemannXi_one
example : riemannXi 0 ≠ 0 := by simp
example : riemannXi 1 ≠ 0 := by simp
example : Differentiable ℂ riemannXi := riemannXi_entire
example (s : ℂ) : riemannXi (1 - s) = riemannXi s := riemannXi_one_sub s
example {s : ℂ} (h : riemannXi s = 0) : 0 ≤ s.re ∧ s.re ≤ 1 :=
  riemannXi_zero_strip h
example : Differentiable ℂ xiModel := xiModel_entire
example (z : ℂ) : xiModel (-z) = xiModel z := xiModel_even z
example {z : ℂ} (h : xiModel z = 0) : |z.im| ≤ 1 := xiModel_zero_strip h
example {z : ℂ} (h : 1 < z.im) : xiModel z ≠ 0 :=
  xiModel_ne_zero_of_one_lt_abs_im (h.trans_le (le_abs_self _))
example {z : ℂ} (h : z.im < -1) : xiModel z ≠ 0 :=
  xiModel_ne_zero_of_one_lt_abs_im (by rw [abs_of_neg (by linarith)]; linarith)

-- The factors 1/2 and 1/8 make both strip endpoints equal to 1/16.
example : xiModel I = 1 / 16 := by
  norm_num [xiModel, I_mul_I]
example : xiModel (-I) = 1 / 16 := by
  rw [xiModel_even]
  norm_num [xiModel, I_mul_I]

-- The bridge is unconditional for every complex argument, including both removed poles.
example (z : ℂ) : completedRiemannZeta₀ (1/2 + I*z/2) = 8*thetaCosIntegral z :=
  completedRiemannZeta₀_eq_thetaCosIntegral z
example (z : ℂ) : H 0 z = riemannXi (1/2 + I*z/2)/8 := H_zero_eq_riemannXi z
example : H 0 I = 1/16 := by
  rw [H_zero_eq_riemannXi]
  norm_num [I_mul_I]
example : H 0 (-I) = 1/16 := by
  rw [H_zero_eq_riemannXi]
  norm_num [I_mul_I]
example : H 0 0 = riemannXi (1/2)/8 := by simpa using H_zero_eq_riemannXi 0
example {z : ℂ} (h : H 0 z = 0) : |z.im| ≤ 1 := H_zero_strip h
example {z : ℂ} (h : 1 < z.im) : H 0 z ≠ 0 :=
  H_zero_ne_zero_of_one_lt_abs_im (h.trans_le (le_abs_self _))
example {z : ℂ} (h : z.im < -1) : H 0 z ≠ 0 :=
  H_zero_ne_zero_of_one_lt_abs_im (by rw [abs_of_neg (by linarith)]; linarith)

assert_no_sorry riemannXi_eq_mul_completed
assert_no_sorry riemannXi_entire
assert_no_sorry riemannXi_one_sub
assert_no_sorry riemannXi_zero_strip
assert_no_sorry xiModel_entire
assert_no_sorry xiModel_even
assert_no_sorry xiModel_zero_strip
assert_no_sorry completedRiemannZeta₀_eq_thetaCosIntegral
assert_no_sorry H_zero_eq_xiModel
assert_no_sorry H_zero_eq_riemannXi
assert_no_sorry H_zero_strip
assert_no_sorry H_zero_ne_zero_of_one_lt_abs_im
/-- info: 'LeanCert.Analysis.DBN.riemannXi_zero_strip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms riemannXi_zero_strip
/-- info: 'LeanCert.Analysis.DBN.xiModel_zero_strip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms xiModel_zero_strip
/-- info: 'LeanCert.Analysis.DBN.completedRiemannZeta₀_eq_thetaCosIntegral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms completedRiemannZeta₀_eq_thetaCosIntegral
/-- info: 'LeanCert.Analysis.DBN.H_zero_eq_xiModel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms H_zero_eq_xiModel
/-- info: 'LeanCert.Analysis.DBN.H_zero_strip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms H_zero_strip

end LeanCert.Test.DBNXi
