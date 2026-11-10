module

/-
  Test interval_bound_subdiv with lower bounds
-/
public import LeanCert.Tactic.IntervalAuto

public section

open LeanCert.Core
open Set

-- Simple lower bound - should work without subdivision
example : ∀ x ∈ Icc (0 : ℝ) 1, 0 ≤ x * x := by
  interval_bound_subdiv

-- Lower bound with transcendental
example : ∀ x ∈ Icc (0 : ℝ) 1, -1 ≤ Real.sin x := by
  interval_bound_subdiv

-- Lower bound on exp (always ≥ 1 for positive input, but exp 0 = 1)
example : ∀ x ∈ Icc (0 : ℝ) 1, 1 ≤ Real.exp x := by
  interval_bound_subdiv 15

-- x² - x has minimum at x=0.5 with value -0.25
-- With subdivision, we can prove tighter bounds than without
-- Without subdivision: interval arithmetic gives [-1, 1]
-- With subdivision to depth 5: can prove ≥ -1 easily (and tighter)
example : ∀ x ∈ Icc (0 : ℝ) 1, -1 ≤ x * x - x := by
  interval_bound_subdiv 10 3

-- Upper and lower together
example : ∀ x ∈ Icc (0 : ℝ) 1, 0 ≤ x * x := by
  interval_bound_subdiv

example : ∀ x ∈ Icc (0 : ℝ) 1, x * x ≤ 1 := by
  interval_bound_subdiv

-- tanh bounds
example : ∀ x ∈ Icc (-5 : ℝ) 5, -1 ≤ Real.tanh x := by
  interval_bound_subdiv

example : ∀ x ∈ Icc (-5 : ℝ) 5, Real.tanh x ≤ 1 := by
  interval_bound_subdiv

-- cosh is always ≥ 1
example : ∀ x ∈ Icc (-2 : ℝ) 2, 1 ≤ Real.cosh x := by
  interval_bound_subdiv

-- cos is in [-1, 1]
example : ∀ x ∈ Icc (0 : ℝ) 7, -1 ≤ Real.cos x := by
  interval_bound_subdiv
