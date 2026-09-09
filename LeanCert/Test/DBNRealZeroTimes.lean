import LeanCert.Analysis.DBN.RealZeroTimes
import Mathlib.Util.AssertNoSorry

open LeanCert.Analysis.DBN Set Filter
open scoped Topology

example : IsClosed realZeroTimes := isClosed_realZeroTimes
example : realZeroTimes.Nonempty := realZeroTimes_nonempty
example : (1/2 : ℝ) ∈ realZeroTimes := half_mem_realZeroTimes

example {τ : ℕ → ℝ} {t : ℝ} (hτ : Tendsto τ atTop (𝓝 t))
    (hreal : ∀ n, τ n ∈ realZeroTimes) : t ∈ realZeroTimes :=
  realZeroTimes_limit hτ hreal

-- The lower bound is deliberately present even for the infimum inequality.
example (hb : BddBelow realZeroTimes) : sInf realZeroTimes ≤ (1/2 : ℝ) :=
  realZeroTimes_sInf_le_half hb

example (hb : BddBelow realZeroTimes)
    (hforward : ∀ s ∈ realZeroTimes, ∀ t, s ≤ t → t ∈ realZeroTimes) (t : ℝ) :
    (∀ z : ℂ, H t z = 0 → z.im = 0) ↔ sInf realZeroTimes ≤ t := by
  change t ∈ realZeroTimes ↔ _
  exact Set.ext_iff.mp (realZeroTimes_eq_Ici hb hforward) t

-- A bad time only bounds *all* good times in combination with preservation.
example (hforward : ∀ s ∈ realZeroTimes, ∀ t, s ≤ t → t ∈ realZeroTimes)
    {b : ℝ} {z : ℂ} (hz : H b z = 0) (him : z.im ≠ 0) :
    BddBelow realZeroTimes :=
  realZeroTimes_bddBelow_of_bad_time hforward (fun hb => him (hb z hz))

assert_no_sorry H_time_tendstoLocallyUniformly
assert_no_sorry realZeroTimes_limit
assert_no_sorry isClosed_realZeroTimes
assert_no_sorry realZeroTimes_isLeast_sInf
assert_no_sorry realZeroTimes_sInf_le_half
assert_no_sorry realZeroTimes_eq_Ici
assert_no_sorry realZeroTimes_bddBelow_of_bad_time

/-- info: 'LeanCert.Analysis.DBN.isClosed_realZeroTimes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms isClosed_realZeroTimes
/-- info: 'LeanCert.Analysis.DBN.realZeroTimes_eq_Ici' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms realZeroTimes_eq_Ici
