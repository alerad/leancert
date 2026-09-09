/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Analysis.DBN.ZeroLimit

/-! A local zero-transfer theorem allowing approximants which are only
holomorphic on compact sets eventually (for example, logarithmic coordinates
translated into the upper half-plane). -/
namespace LeanCert.Analysis.DBN
open Complex Complex.Hadamard Set Metric Filter
open scoped Topology

/-- A zero of a nontrivial entire limit forces zeros of the approximants in
every open neighborhood, eventually. No global holomorphy of the approximants
is required. -/
theorem eventually_exists_zero_of_locally_uniform {ι : Type*} {l : Filter ι}
    {F : ι → ℂ → ℂ} {f : ℂ → ℂ}
    (hF : ∀ K : Set ℂ, IsCompact K → ∀ᶠ n in l, DifferentiableOn ℂ (F n) K)
    (hf : Differentiable ℂ f) (hnot : ∃ w, f w ≠ 0)
    (hlim : TendstoLocallyUniformly F f l)
    {U : Set ℂ} (hU : IsOpen U) {z : ℂ} (hz : z ∈ U) (hfz : f z = 0) :
    ∀ᶠ n in l, ∃ w ∈ U, F n w = 0 := by
  have hfin := analyticOrderAt_ne_top_of_exists_ne_zero hf hnot z
  have hp : ∀ᶠ w in 𝓝[≠] z, f w ≠ 0 :=
    (hf.analyticAt z).eventually_eq_zero_or_eventually_ne_zero.resolve_left
      (by intro h; exact hfin (analyticOrderAt_eq_top.mpr h))
  obtain ⟨r₀, hr₀, hball⟩ := Metric.mem_nhdsWithin_iff.mp hp
  obtain ⟨r₁, hr₁, hsub⟩ := Metric.isOpen_iff.mp hU z hz
  let r := min r₀ r₁ / 2
  have hr : 0 < r := by dsimp [r]; positivity
  have hr0 : r < r₀ := by dsimp [r]; linarith [min_le_left r₀ r₁]
  have hr1 : r < r₁ := by dsimp [r]; linarith [min_le_right r₀ r₁]
  have hclosed : closedBall z r ⊆ U := fun w hw =>
    hsub (mem_ball.mpr ((mem_closedBall.mp hw).trans_lt hr1))
  have hsphere : ∀ w ∈ sphere z r, f w ≠ 0 := by
    intro w hw
    have hd := mem_sphere.mp hw
    apply hball
    exact ⟨mem_ball.mpr (hd.trans_lt hr0), by
      simp only [mem_compl_iff, mem_singleton_iff]
      intro he; subst w; simp at hd; linarith⟩
  obtain ⟨w, hw, hmin⟩ := (isCompact_sphere z r).exists_isMinOn
    (NormedSpace.sphere_nonempty.mpr hr.le) hf.continuous.norm.continuousOn
  have hm : 0 < ‖f w‖ := norm_pos_iff.mpr (hsphere w hw)
  have hc := (tendstoLocallyUniformly_iff_forall_isCompact.mp hlim)
    (closedBall z r) (isCompact_closedBall z r)
  filter_upwards [(Metric.tendstoUniformlyOn_iff.mp hc) (‖f w‖ / 3) (by positivity),
    hF (closedBall z r) (isCompact_closedBall z r)] with n hn hd
  by_contra hnzero
  have hne : ∀ y ∈ U, F n y ≠ 0 := by simpa using hnzero
  have hb : ∀ y ∈ sphere z r, ‖f w‖ / 2 ≤ ‖F n y‖ := by
    intro y hy
    have hh := hn y (sphere_subset_closedBall hy)
    have hmn : ‖f w‖ ≤ ‖f y‖ := hmin hy
    have ht := norm_sub_norm_le (f y) (F n y)
    rw [dist_eq_norm] at hh
    linarith
  have hl := disk_lower_bound hr (by positivity : 0 < ‖f w‖ / 2)
    hd (fun y hy => hne y (hclosed hy)) hb
  have hh := hn z (mem_closedBall_self hr.le)
  simp only [hfz, dist_zero_left] at hh
  linarith

end LeanCert.Analysis.DBN
