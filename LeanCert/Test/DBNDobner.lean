import LeanCert.Analysis.DBN.DobnerReduction
import Mathlib.Util.AssertNoSorry

open LeanCert.Analysis LeanCert.Analysis.DBN Complex Filter Set Metric
open scoped Topology

example (ω : ℕ → ℝ) : ∃ τ : ℕ → ℝ, Tendsto τ atTop atTop ∧
    ∀ k, Tendsto (fun n => Circle.exp (τ n * ω k)) atTop (𝓝 1) :=
  DirichletGaussian.exists_phase_returns ω

example {a : ℝ} (ha : 0 < a) : ∃ c : ℝ, ∀ B : ℝ, ∃ s : ℂ,
    |s.re-c| < 1 ∧ B < s.im ∧ DirichletGaussian.series a s = 0 :=
  DirichletGaussian.zeros_at_arbitrary_height ha

example : ∃ s : ℂ, 1000000 < s.im ∧ DirichletGaussian.series 1 s = 0 := by
  obtain ⟨c, hc⟩ := DirichletGaussian.zeros_at_arbitrary_height (a := 1) (by norm_num)
  obtain ⟨s, _, hh, hz⟩ := hc 1000000
  exact ⟨s, hh, hz⟩

example (s : ℂ) : xiHeat 0 s = riemannXi s := xiHeat_zero s
example (s : ℂ) : (heatCoordinate s).im = 1-2*s.re := heatCoordinate_im s
example {a R : ℝ} (ha : 0 < a) {s : ℂ} (hs : -R ≤ s.re)
    (hh : 2*Real.pi*Real.exp ((R+1)/a) ≤ |s.im|) :
    (1/2 : ℝ) < (dobnerMap a s).re := dobnerMap_re_gt_half ha hs hh

-- Local zero transfer does not require entire approximants.
example {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ}
    (hF : ∀ K : Set ℂ, IsCompact K → ∀ᶠ n in atTop, DifferentiableOn ℂ (F n) K)
    (hf : Differentiable ℂ f) (hn : ∃ w, f w ≠ 0)
    (hl : TendstoLocallyUniformly F f atTop) {z : ℂ} (hz : f z = 0) :
    ∀ᶠ n in atTop, ∃ w ∈ ball z 1, F n w = 0 :=
  eventually_exists_zero_of_locally_uniform hF hf hn hl isOpen_ball
    (mem_ball_self (by norm_num)) hz

-- This input remains required; no unconditional lower bound is asserted.
example (h : ∀ t : ℝ, t < 0 → ∃ z : ℂ, H t z = 0 ∧ z.im ≠ 0) : 0 ≤ Lambda :=
  Lambda_nonneg_of_negative_time_zeros h

assert_no_sorry DirichletGaussian.zeros_at_arbitrary_height
assert_no_sorry eventually_exists_zero_of_locally_uniform
assert_no_sorry dobnerMap_re_gt_half
assert_no_sorry nonreal_zero_of_dobner_limit
