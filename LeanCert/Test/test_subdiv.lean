/-
  Test interval_bound_subdiv tactic
-/
import LeanCert.Tactic.IntervalAuto

open LeanCert.Core
open Set

-- Simple test - should work without subdivision
example : ∀ x ∈ Icc (0 : ℝ) 1, x * x ≤ 1 := by
  interval_bound_subdiv

-- This should also work with subdivision
example : ∀ x ∈ Icc (0 : ℝ) 1, x * x + x ≤ 2 := by
  interval_bound_subdiv

-- Test with transcendental - should work
example : ∀ x ∈ Icc (0 : ℝ) 1, Real.sin x ≤ 1 := by
  interval_bound_subdiv

-- Test on larger interval
example : ∀ x ∈ Icc (0 : ℝ) 2, x * x ≤ 4 := by
  interval_bound_subdiv

-- Test with exp (needs Taylor depth)
example : ∀ x ∈ Icc (0 : ℝ) 1, Real.exp x ≤ 3 := by
  interval_bound_subdiv 15

-- Lower-bound subdivision coverage lives in `test_subdiv_lower.lean`.
