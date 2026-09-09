import LeanCert.Analysis.DBN.ForwardPreservation
import Mathlib.Util.AssertNoSorry

open LeanCert.Analysis.DBN Complex Set Filter
open scoped Topology

-- Approximation and convergence have no sign restriction on the starting time.
example (t : ℝ) :
    TendstoLocallyUniformly (fun n z => (TimeApproximation.HZeroPolynomial t n).eval z)
      (H t) atTop := TimeApproximation.HZeroPolynomial_convergence t

example : TendstoLocallyUniformly (timeShift (-100) 0) (H (-100)) atTop := by
  simpa using timeShift_convergence (-100) 0 (by norm_num)

example (δ : ℝ) (hδ : 0 ≤ δ) :
    TendstoLocallyUniformly (timeShift (-100) δ) (H (-100+δ)) atTop :=
  timeShift_convergence (-100) δ hδ

-- Zero elapsed time and zero strip width are valid boundary cases.
example (t b : ℝ) (hs : ∀ z, H t z = 0 → z.im^2 ≤ b^2)
    {z : ℂ} (hz : H t z = 0) : z.im^2 ≤ b^2 := by
  have h := H_forward_strip t b 0 (by norm_num) hs (by simpa using hz)
  simpa only [mul_zero, sub_zero, max_eq_left (sq_nonneg b)] using h

example (t : ℝ) (ht : t ∈ realZeroTimes) : t+0 ∈ realZeroTimes :=
  H_forward_real t 0 (by norm_num) ht

example {t : ℝ} (ht : (1/2 : ℝ) ≤ t) (z : ℂ) (hz : H t z = 0) : z.im = 0 :=
  H_real_zeros_of_half_le ht z hz

example (z : ℂ) (hz : H 1 z = 0) : z.im = 0 :=
  H_real_zeros_of_half_le (by norm_num) z hz

-- Recovery of the original endpoint through the general contraction theorem.
example (z : ℂ) (hz : H (1/2) z = 0) : z.im = 0 := by
  have h := H_forward_strip 0 1 (1/2) (by norm_num)
    (fun w hw => by
      have hb := abs_le.mp (H_zero_strip hw)
      nlinarith)
    (z := z) (by simpa using hz)
  norm_num at h
  nlinarith [sq_nonneg z.im]

assert_no_sorry H_stripApproximation
assert_no_sorry timeShift_convergence
assert_no_sorry H_forward_strip
assert_no_sorry realZeroTimes_forward
assert_no_sorry H_real_zeros_of_half_le

/-- info: 'LeanCert.Analysis.DBN.H_forward_strip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms H_forward_strip
/-- info: 'LeanCert.Analysis.DBN.realZeroTimes_forward' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms realZeroTimes_forward
/-- info: 'LeanCert.Analysis.DBN.H_real_zeros_of_half_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms H_real_zeros_of_half_le
