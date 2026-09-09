import LeanCert.Analysis.DBN.RealZeros
import Mathlib.Topology.Sequences
import Mathlib.Topology.Order.Monotone

/-!
# The set of real-zero times

The actual heat integral varies locally uniformly with time. Hurwitz therefore
makes its set of real-zero times closed; the endpoint theorem makes it nonempty.

The threshold conclusions below explicitly require lower-boundedness and, for
an upper-ray characterization, forward preservation. Neither analytic input is
proved in this foundational module; they are discharged downstream in
`ForwardPreservation` and `BadTime`. The `Threshold` module then defines the
unconditional constant. Here we do not define a real-valued DBN
constant by taking the infimum of a possibly unbounded set.
-/
namespace LeanCert.Analysis.DBN
open Complex Set Filter
open scoped Topology

/-- Times at which every complex zero of the actual heat integral is real. -/
def realZeroTimes : Set ℝ := {t | ∀ z : ℂ, H t z = 0 → z.im = 0}

set_option maxHeartbeats 800000 in
/-- Joint continuity upgrades convergence in time to locally uniform convergence
in the complex spatial argument. This applies to arbitrary index filters. -/
theorem H_time_tendstoLocallyUniformly {ι : Type*} {l : Filter ι}
    {τ : ι → ℝ} {t : ℝ} (hτ : Tendsto τ l (𝓝 t)) :
    TendstoLocallyUniformly (fun i => H (τ i)) (H t) l := by
  apply tendstoLocallyUniformly_iff_forall_tendsto.mpr
  intro z
  have hp : Tendsto (fun p : ι × ℂ => (τ p.1, p.2))
      (l ×ˢ 𝓝 z) (𝓝 (t, z)) :=
    (hτ.comp (tendsto_fst (g := 𝓝 z))).prodMk_nhds tendsto_snd
  have hj : Tendsto (fun p : ι × ℂ => H (τ p.1) p.2)
      (l ×ˢ 𝓝 z) (𝓝 (H t z)) :=
    (continuous_H.tendsto (t, z)).comp hp
  exact (((H_entire t).continuous.tendsto z |>.comp tendsto_snd).prodMk_nhds hj).mono_right (nhds_le_uniformity _)

/-- A convergent family of real-zero times cannot acquire a nonreal zero. -/
theorem realZeroTimes_limit {ι : Type*} {l : Filter ι} [l.NeBot]
    {τ : ι → ℝ} {t : ℝ} (hτ : Tendsto τ l (𝓝 t))
    (hreal : ∀ i, τ i ∈ realZeroTimes) : t ∈ realZeroTimes := by
  intro z hz
  by_contra him
  exact (entire_limit_ne_zero (fun i => H_entire (τ i)) (H_entire t)
    ⟨0, H_zero_ne_zero t⟩ (H_time_tendstoLocallyUniformly hτ)
    (U := {w : ℂ | w.im ≠ 0}) (isOpen_ne.preimage Complex.continuous_im)
    (fun i w hw hzero => hw (hreal i w hzero)) him) hz

theorem isClosed_realZeroTimes : IsClosed realZeroTimes := by
  apply IsSeqClosed.isClosed
  intro τ t hreal hτ
  exact realZeroTimes_limit hτ hreal

theorem half_mem_realZeroTimes : (1/2 : ℝ) ∈ realZeroTimes := H_half_real_zeros

theorem realZeroTimes_nonempty : realZeroTimes.Nonempty := ⟨1/2, half_mem_realZeroTimes⟩

/-- Lower-boundedness is the missing input needed to obtain an attained finite
infimum. Nonemptiness alone does not suffice in a conditionally complete order. -/
theorem realZeroTimes_isLeast_sInf (hb : BddBelow realZeroTimes) :
    IsLeast realZeroTimes (sInf realZeroTimes) :=
  isClosed_realZeroTimes.isLeast_csInf realZeroTimes_nonempty hb

theorem realZeroTimes_sInf_le_half (hb : BddBelow realZeroTimes) :
    sInf realZeroTimes ≤ (1/2 : ℝ) :=
  (realZeroTimes_isLeast_sInf hb).2 half_mem_realZeroTimes

/-- Once forward preservation and lower-boundedness are supplied, the closed
nonempty set of good times is exactly the upper ray starting at its infimum. -/
theorem realZeroTimes_eq_Ici (hb : BddBelow realZeroTimes)
    (hforward : ∀ s ∈ realZeroTimes, ∀ t, s ≤ t → t ∈ realZeroTimes) :
    realZeroTimes = Ici (sInf realZeroTimes) := by
  ext t
  exact ⟨fun ht => (realZeroTimes_isLeast_sInf hb).2 ht,
    fun ht => hforward _ (realZeroTimes_isLeast_sInf hb).1 t ht⟩

/-- A single bad time supplies a lower bound *if* forward preservation is known.
Producing that bad time remains a substantive analytic obligation. -/
theorem realZeroTimes_bddBelow_of_bad_time
    (hforward : ∀ s ∈ realZeroTimes, ∀ t, s ≤ t → t ∈ realZeroTimes)
    {b : ℝ} (hbad : b ∉ realZeroTimes) : BddBelow realZeroTimes := by
  refine ⟨b, fun s hs => ?_⟩
  exact le_of_lt (lt_of_not_ge (fun h => hbad (hforward s hs b h)))

end LeanCert.Analysis.DBN
