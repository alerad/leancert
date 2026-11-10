module

public import LeanCert.Tactic.IntervalAuto

public section

open Set

-- Subdivision-heavy stress tests.
example : ∀ x ∈ Icc (0 : ℝ) 1, Real.sin x ≤ 1 := by
  interval_bound_subdiv 20 4

example : ∀ x ∈ Icc (0 : ℝ) 1, Real.exp x ≤ 3 := by
  interval_bound_subdiv 20 4

example : ∀ x ∈ Icc (-1 : ℝ) 1, (-1 : ℝ) ≤ Real.cos x := by
  interval_bound_subdiv 20 4

example : ∀ x ∈ Icc (0 : ℝ) 1, Real.exp (x - x ^ 2) ≤ 3 := by
  interval_bound_subdiv 20 4
