import LeanCert.Tactic.IntervalAuto
import LeanCert.Tactic.DyadicAuto

theorem edge_decide_exp : Real.exp (1:ℝ) ≤ (3 : ℚ) := by
  interval_decide 15

theorem edge_decide_sqrt : Real.sqrt (2:ℝ) ≤ (2 : ℚ) := by
  interval_decide

theorem edge_decide_pi : Real.pi < (4 : ℚ) := by
  interval_decide

theorem edge_decide_sin : Real.sin (1:ℝ) < (1 : ℚ) := by
  interval_decide

theorem edge_fast_bound : ∀ x ∈ Set.Icc (0:ℝ) 1, x * x ≤ (1 : ℚ) := by
  certify_kernel_fallback

theorem edge_fast_bound_precise : ∀ x ∈ Set.Icc (0:ℝ) 1, Real.sin x ≤ (1 : ℚ) := by
  certify_kernel_precise_fallback

theorem edge_fast_bound_quick : ∀ x ∈ Set.Icc (0:ℝ) 1, Real.exp x ≤ (3 : ℚ) := by
  certify_kernel_quick_fallback
