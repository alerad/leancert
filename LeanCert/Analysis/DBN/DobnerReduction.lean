/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Analysis.DBN.DobnerGeometry
import LeanCert.Analysis.DBN.ZeroTransfer
import LeanCert.Analysis.DBN.Threshold
import LeanCert.Analysis.DirichletGaussian.Recurrence

/-!
# Conditional final step of the Dobner route

The approximation hypotheses below are NOT yet established for the actual
heat integral. They remain explicit arguments, not axioms or instances.
-/
namespace LeanCert.Analysis.DBN
open Complex Filter Set Metric
open scoped Topology

/-- The exact remaining interface: a locally uniform normalized heat limit
along upward translations forces a genuine nonreal heat zero. The multiplier
need not be nonzero for this direction of zero transfer, but constructing F
by division would require proving that separately. -/
theorem nonreal_zero_of_dobner_limit {t : ℝ} (ht : t < 0)
    {τ : ℕ → ℝ} (hτ : Tendsto τ atTop atTop)
    {F G : ℕ → ℂ → ℂ}
    (hF : ∀ K : Set ℂ, IsCompact K → ∀ᶠ n in atTop, DifferentiableOn ℂ (F n) K)
    (hlim : TendstoLocallyUniformly F (DirichletGaussian.series (-t/4)) atTop)
    (hidentity : ∀ K : Set ℂ, IsCompact K → ∀ᶠ n in atTop, ∀ s ∈ K,
      xiHeat t (dobnerMap (-t/4) (s+(τ n : ℂ)*I)) = G n s * F n s) :
    ∃ z : ℂ, H t z = 0 ∧ z.im ≠ 0 := by
  have ha : 0 < -t/4 := by linarith
  obtain ⟨z, hz⟩ := DirichletGaussian.exists_zero ha
  have hnot : ∃ w, DirichletGaussian.series (-t/4) w ≠ 0 := by
    refine ⟨0, ?_⟩
    intro h
    have := DirichletGaussian.one_lt_re_series_zero ha
    norm_num [h] at this
  have he := eventually_exists_zero_of_locally_uniform hF
    (DirichletGaussian.entire_series ha) hnot hlim isOpen_ball
    (mem_ball_self (by norm_num : (0 : ℝ) < 1)) hz
  have hc := isCompact_closedBall z (1 : ℝ)
  obtain ⟨n, hn, hid, hright⟩ := (he.and ((hidentity _ hc).and
    (eventually_dobnerMap_right_on_compact ha hτ hc))).exists
  obtain ⟨s, hs, hs0⟩ := hn
  have hsc := ball_subset_closedBall hs
  have hzero : xiHeat t (dobnerMap (-t/4) (s+(τ n : ℂ)*I)) = 0 := by
    rw [hid s hsc, hs0, mul_zero]
  exact ⟨_, nonreal_heat_zero_of_xiHeat_zero hzero (hright s hsc)⟩

/-- Logical last step only: the universal negative-time obstruction is still
an input. This is not an unconditional nonnegative DBN bound. -/
theorem Lambda_nonneg_of_negative_time_zeros
    (h : ∀ t : ℝ, t < 0 → ∃ z : ℂ, H t z = 0 ∧ z.im ≠ 0) : 0 ≤ Lambda := by
  by_contra hn
  obtain ⟨z, hz, him⟩ := h Lambda (lt_of_not_ge hn)
  exact him (H_Lambda_real_zeros z hz)

end LeanCert.Analysis.DBN
