import LeanCert.Analysis.DBN.Threshold
import Mathlib.Util.AssertNoSorry

open LeanCert.Analysis.DBN Complex Set Filter
open scoped Topology

-- The obstruction is an exact strict inequality for the actual infinite series.
example : Phi 3 * (Phi 1)^15 < (Phi 0)^10 * (Phi 2)^6 :=
  Phi_four_point_obstruction
example : Continuous evenPhi := continuous_evenPhi
example : MeasureTheory.Integrable evenPhi := integrable_evenPhi

-- All real centers, including the origin and negative centers.
example (x : ℝ) : Tendsto (fun n : ℕ => gaussianAverage (n+1) x) atTop
    (𝓝 (Real.sqrt Real.pi * evenPhi x)) := gaussianAverage_tendsto x
example : Tendsto (fun n : ℕ => gaussianAverage (n+1) 0) atTop
    (𝓝 (Real.sqrt Real.pi * Phi 0)) := by
  simpa [evenPhi] using gaussianAverage_tendsto 0
example : Tendsto (fun n : ℕ => gaussianAverage (n+1) (-2)) atTop
    (𝓝 (Real.sqrt Real.pi * Phi 2)) := by
  simpa [evenPhi] using gaussianAverage_tendsto (-2)

-- The contradiction produces genuine bad times, not a bound hypothesis.
example : ∃ n : ℕ, -((n : ℝ)+1)^2 ∉ realZeroTimes := exists_bad_negative_square
example : ∃ t : ℝ, ∃ z : ℂ, H t z = 0 ∧ z.im ≠ 0 := by
  obtain ⟨t, ht⟩ := exists_bad_time
  change ¬ ∀ z : ℂ, H t z = 0 → z.im = 0 at ht
  push Not at ht
  exact ⟨t, ht⟩

example : BddBelow realZeroTimes := realZeroTimes_bddBelow
example : Lambda ≤ (1/2 : ℝ) := Lambda_le_half
example (t : ℝ) : (∀ z : ℂ, H t z = 0 → z.im = 0) ↔ Lambda ≤ t :=
  real_zeros_iff_Lambda_le t

-- The threshold itself is included; strictly earlier times are bad.
example (z : ℂ) (hz : H Lambda z = 0) : z.im = 0 := H_Lambda_real_zeros z hz
example {t : ℝ} (ht : t < Lambda) : ∃ z : ℂ, H t z = 0 ∧ z.im ≠ 0 :=
  nonreal_zero_of_lt_Lambda ht
example : ∃ z : ℂ, H (Lambda-1) z = 0 ∧ z.im ≠ 0 :=
  nonreal_zero_of_lt_Lambda (by linarith)

example {a : ℝ}
    (ha : ∀ t : ℝ, (∀ z : ℂ, H t z = 0 → z.im = 0) ↔ a ≤ t) : a = Lambda :=
  Lambda_unique ha

example : ∃ a : ℝ, a ≤ (1/2 : ℝ) ∧
    ∀ t : ℝ, (∀ z : ℂ, H t z = 0 → z.im = 0) ↔ a ≤ t := dbn_certificate

assert_no_sorry Phi_four_point_obstruction
assert_no_sorry H_four_point_normSq
assert_no_sorry gaussianAverage_eq_H
assert_no_sorry gaussianAverage_tendsto
assert_no_sorry exists_bad_negative_square
assert_no_sorry realZeroTimes_bddBelow
assert_no_sorry real_zeros_iff_Lambda_le
assert_no_sorry Lambda_le_half
assert_no_sorry dbn_certificate

/-- info: 'LeanCert.Analysis.DBN.Phi_four_point_obstruction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Phi_four_point_obstruction
/-- info: 'LeanCert.Analysis.DBN.H_four_point_normSq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms H_four_point_normSq
/-- info: 'LeanCert.Analysis.DBN.gaussianAverage_tendsto' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms gaussianAverage_tendsto
/-- info: 'LeanCert.Analysis.DBN.exists_bad_negative_square' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms exists_bad_negative_square
/-- info: 'LeanCert.Analysis.DBN.real_zeros_iff_Lambda_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms real_zeros_iff_Lambda_le
/-- info: 'LeanCert.Analysis.DBN.dbn_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms dbn_certificate
