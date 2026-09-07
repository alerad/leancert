import LeanCert.Analysis.DBN.RealZeros
import Mathlib.Util.AssertNoSorry

open LeanCert.Analysis.DBN Complex Polynomial Filter

-- Pin the unconditional endpoint and its zero-free-region interface.
example : ∀ z : ℂ, H (1/2) z = 0 → z.im = 0 := H_half_real_zeros
example {z : ℂ} (hz : z.im ≠ 0) : H (1/2) z ≠ 0 :=
  H_half_ne_zero_of_im_ne_zero hz
example : H (1/2) Complex.I ≠ 0 := H_half_ne_zero_of_im_ne_zero (by simp)
example : H (1/2) (-Complex.I) ≠ 0 := H_half_ne_zero_of_im_ne_zero (by simp)

-- The radius-zero cutoff is genuinely empty; no special nonempty-divisor assumption.
example : HZeroCutoff 0 = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro p hp
  have h := (mem_HZeroCutoff 0 p).mp hp
  have hz : Hadamard.divisorZeroIndex₀_val p = 0 := norm_eq_zero.mp (by simpa using h)
  exact Hadamard.divisorZeroIndex₀_val_ne_zero p hz

example (n : ℕ) : (HZeroPolynomial n).eval 0 = H 0 0 := HZeroPolynomial_at_zero n
example (n : ℕ) : HZeroPolynomial n ≠ 0 := HZeroPolynomial_ne_zero n
example (n : ℕ) : (HZeroPolynomial n).map (starRingEnd ℂ) = HZeroPolynomial n :=
  HZeroPolynomial_conj n
example (n : ℕ) (z : ℂ) (hz : (HZeroPolynomial n).eval z = 0) : z.im^2 ≤ 1 :=
  HZeroPolynomial_strip n z hz
example {z : ℂ} (hz : unitShift 0 z = 0) : z.im = 0 := unitShift_real 0 hz

assert_no_sorry HZeroPolynomial_convergence
assert_no_sorry entire_limit_ne_zero
assert_no_sorry shiftIter_H_unit_real
assert_no_sorry unitShift_convergence
assert_no_sorry H_half_real_zeros

/-- info: 'LeanCert.Analysis.DBN.HZeroPolynomial_convergence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms HZeroPolynomial_convergence
/-- info: 'LeanCert.Analysis.DBN.entire_limit_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms entire_limit_ne_zero
/-- info: 'LeanCert.Analysis.DBN.unitShift_convergence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms unitShift_convergence
/-- info: 'LeanCert.Analysis.DBN.H_half_real_zeros' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms H_half_real_zeros
