/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Tactic

/-! Regression tests for fixed-cutoff eventual bounds. -/

#guard LeanCert.Validity.checkReciprocalPowerUpper 1 (1 / 100) 2 10
#guard !LeanCert.Validity.checkReciprocalPowerUpper 1 (1 / 100) 2 9
#guard !LeanCert.Validity.checkReciprocalPowerUpper 1 1 1 0

example : ∀ n : Nat, 10 ≤ n → (1 : ℝ) / (n : ℝ) ^ 2 ≤ 1 / 100 := by
  eventual_bound

example : ∀ n : Nat, 100 ≤ n → (1 : ℝ) / n ≤ 1 / 100 := by
  eventual_bound

example : ∃ N : Nat, ∀ n : Nat, N ≤ n → (3 : ℝ) / (n : ℝ) ^ 2 ≤ 3 / 100 := by
  eventual_bound using 10

example : ∃ N : Nat, ∀ n ≥ N, (1 : ℝ) / n ≤ 1 / 100 := by
  eventual_bound using 100

example : ∀ n : Nat, 10 ≤ n → (2 : ℝ) / n ^ 2 ≤ 1 / 50 := by
  eventual_bound?

example : True := by
  fail_if_success
    have : ∀ n : Nat, 9 ≤ n → (1 : ℝ) / n ^ 2 ≤ 1 / 100 := by
      eventual_bound
  trivial
