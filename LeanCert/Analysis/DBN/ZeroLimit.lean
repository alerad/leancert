import LeanCert.Analysis.DBN.Hadamard
import Mathlib.Analysis.Complex.AbsMax

/-! Zero exclusion under locally uniform limits of entire functions. -/
namespace LeanCert.Analysis.DBN
open Complex Complex.Hadamard Set Metric Filter
open scoped Topology

/-- A reciprocal maximum principle supplies the local ingredient of Hurwitz. -/
theorem disk_lower_bound {f : ℂ → ℂ} {c : ℂ} {r m : ℝ}
    (hr : 0 < r) (hm : 0 < m)
    (hf : DifferentiableOn ℂ f (closedBall c r))
    (hn : ∀ z ∈ closedBall c r, f z ≠ 0)
    (hb : ∀ z ∈ sphere c r, m ≤ ‖f z‖) : m ≤ ‖f c‖ := by
  have hd : DiffContOnCl ℂ (fun z => (f z)⁻¹) (ball c r) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball c hr.ne']
    exact hf.inv hn
  have h := Complex.norm_le_of_forall_mem_frontier_norm_le (isBounded_ball : Bornology.IsBounded (ball c r)) hd
    (C := m⁻¹) (by
      intro z hz
      rw [frontier_ball c hr.ne'] at hz
      rw [norm_inv]
      exact inv_anti₀ hm (hb z hz))
    (z := c) (by rw [closure_ball c hr.ne']; exact mem_closedBall_self hr.le)
  rw [norm_inv] at h
  exact (inv_le_inv₀ (norm_pos_iff.mpr (hn c (mem_closedBall_self hr.le))) hm).mp h


/-- A nontrivial entire limit cannot acquire a zero in an open region where
every approximant is zero-free. The index may be any nontrivial filter. -/
theorem entire_limit_ne_zero {ι : Type*} {l : Filter ι} [l.NeBot]
    {F : ι → ℂ → ℂ} {f : ℂ → ℂ}
    (hF : ∀ n, Differentiable ℂ (F n)) (hf : Differentiable ℂ f)
    (hnot : ∃ w, f w ≠ 0) (hlim : TendstoLocallyUniformly F f l)
    {U : Set ℂ} (hU : IsOpen U) (hn : ∀ n, ∀ z ∈ U, F n z ≠ 0)
    {z : ℂ} (hz : z ∈ U) : f z ≠ 0 := by
  intro hfz
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
  have hc : TendstoUniformlyOn F f l (closedBall z r) :=
    (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact (isCompact_closedBall z r)).mp
      (hlim.tendstoLocallyUniformlyOn (s := closedBall z r))
  have he := (Metric.tendstoUniformlyOn_iff.mp hc) (‖f w‖ / 3) (by positivity)
  obtain ⟨n, hn'⟩ := he.exists
  have hb : ∀ y ∈ sphere z r, ‖f w‖ / 2 ≤ ‖F n y‖ := by
    intro y hy
    have hh := hn' y (sphere_subset_closedBall hy)
    have hmn : ‖f w‖ ≤ ‖f y‖ := hmin hy
    have ht := norm_sub_norm_le (f y) (F n y)
    rw [dist_eq_norm] at hh
    linarith
  have hl := disk_lower_bound hr (by positivity : 0 < ‖f w‖ / 2)
    (hF n).differentiableOn (fun y hy => hn n y (hclosed hy)) hb
  have hh := hn' z (mem_closedBall_self hr.le)
  simp only [hfz, dist_zero_left] at hh
  linarith

end LeanCert.Analysis.DBN
