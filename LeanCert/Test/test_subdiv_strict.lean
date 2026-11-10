module

/-
  Test interval_bound_subdiv with strict inequalities
-/
public import LeanCert.Tactic.IntervalAuto

public section

open LeanCert.Core
open Set

-- Strict upper bound (f x < c)
example : ∀ x ∈ Icc (0 : ℝ) 1, x * x < 2 := by
  interval_bound_subdiv

example : ∀ x ∈ Icc (0 : ℝ) 1, Real.sin x < 2 := by
  interval_bound_subdiv

example : ∀ x ∈ Icc (0 : ℝ) 1, Real.exp x < 4 := by
  interval_bound_subdiv 15

-- Strict lower bound (c < f x)
example : ∀ x ∈ Icc (0 : ℝ) 1, -1 < x * x := by
  interval_bound_subdiv

example : ∀ x ∈ Icc (0 : ℝ) 1, -2 < Real.sin x := by
  interval_bound_subdiv

example : ∀ x ∈ Icc (0 : ℝ) 1, 0 < Real.exp x := by
  interval_bound_subdiv 15

-- Combining strict and non-strict
example : ∀ x ∈ Icc (0 : ℝ) 1, x * x ≤ 1 := by
  interval_bound_subdiv

example : ∀ x ∈ Icc (0 : ℝ) 1, x * x < (3/2 : ℚ) := by
  interval_bound_subdiv

-- tanh strict bounds
example : ∀ x ∈ Icc (-5 : ℝ) 5, Real.tanh x < 2 := by
  interval_bound_subdiv

example : ∀ x ∈ Icc (-5 : ℝ) 5, -2 < Real.tanh x := by
  interval_bound_subdiv
