/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Tactic

/-! Regression tests for fixed and discovered-cutoff eventual bounds. -/

#guard LeanCert.Validity.checkReciprocalPowerUpper 1 (1 / 100) 2 10
#guard !LeanCert.Validity.checkReciprocalPowerUpper 1 (1 / 100) 2 9
#guard !LeanCert.Validity.checkReciprocalPowerUpper 1 1 1 0

#guard (LeanCert.Tactic.discoverReciprocalPowerCutoff 3 (1 / 1000) 2 64).toOption.map
  (·.cutoff) == some 55
#guard (LeanCert.Tactic.discoverReciprocalPowerCutoff 0 0 7 1).toOption.map
  (·.cutoff) == some 1
#guard (LeanCert.Tactic.discoverReciprocalPowerCutoff 3 (1 / 1000) 2 7).toOption.map
  (fun result => (result.cutoff, result.refinementComplete)) == some (64, false)
#guard match LeanCert.Tactic.discoverReciprocalPowerCutoff 0 (-1) 2 64 with
  | .error _ => true
  | .ok _ => false

private def discoveredCutoffIsSound (q bound : ℚ) (k maxChecks : Nat) : Bool :=
  match LeanCert.Tactic.discoverReciprocalPowerCutoff q bound k maxChecks with
  | .error _ => false
  | .ok result =>
      LeanCert.Validity.checkReciprocalPowerUpper q bound k result.cutoff

private def completedDiscoveryIsMinimal (q bound : ℚ) (k maxChecks : Nat) : Bool :=
  match LeanCert.Tactic.discoverReciprocalPowerCutoff q bound k maxChecks with
  | .error _ => false
  | .ok result =>
      !result.refinementComplete || result.cutoff = 1 ||
        !LeanCert.Validity.checkReciprocalPowerUpper q bound k (result.cutoff - 1)

/- Exact-square, just-above-square, deep-search, and bounded-refinement cases
exercise the untrusted search independently of tactic proof construction. -/
#guard (LeanCert.Tactic.discoverReciprocalPowerCutoff 1 (1 / 100) 2 64).toOption.map
  (·.cutoff) == some 10
#guard (LeanCert.Tactic.discoverReciprocalPowerCutoff 1 (1 / 101) 2 64).toOption.map
  (·.cutoff) == some 11
#guard (LeanCert.Tactic.discoverReciprocalPowerCutoff 1000 (1 / 1000000) 2 64).toOption.map
  (·.cutoff) == some 31623
#guard discoveredCutoffIsSound 3 (1 / 1000) 2 7
#guard completedDiscoveryIsMinimal 1 (1 / 100) 2 64
#guard completedDiscoveryIsMinimal 1 (1 / 101) 2 64
#guard completedDiscoveryIsMinimal 1000 (1 / 1000000) 2 64

example : ∀ n : Nat, 10 ≤ n → (1 : ℝ) / (n : ℝ) ^ 2 ≤ 1 / 100 := by
  eventual_bound

example : ∀ n : Nat, 100 ≤ n → (1 : ℝ) / n ≤ 1 / 100 := by
  eventual_bound

example : ∃ N : Nat, ∀ n : Nat, N ≤ n → (3 : ℝ) / (n : ℝ) ^ 2 ≤ 3 / 100 := by
  eventual_bound using 10

example : ∃ N : Nat, ∀ n ≥ N, (1 : ℝ) / n ≤ 1 / 100 := by
  eventual_bound using 100

example : ∃ N : Nat, ∀ n ≥ N, (3 : ℝ) / n ^ 2 ≤ 1 / 1000 := by
  eventual_bound

example : ∃ N : Nat, ∀ n ≥ N, (3 : ℝ) / n ^ 2 ≤ 1 / 1000 := by
  eventual_bound (maxIterations := 64)

example : ∃ N : Nat, ∀ n ≥ N, (3 : ℝ) / n ^ 2 ≤ 1 / 1000 := by
  leancert

example : ∃ N : Nat, ∀ n ≥ N, (3 : ℝ) / n ^ 2 ≤ 1 / 1000 := by
  leancert (maxIterations := 7)

example : ∃ N : Nat, ∀ n, n ≥ N → (2 : ℝ) / n ^ 3 ≤ 1 / 10000 := by
  leancert

example : ∀ n : Nat, 100 ≤ n → (1 : ℝ) / n ≤ 1 / 100 := by
  leancert

example : ∃ N : Nat, ∀ n ≥ N, (3 : ℝ) / n ^ 2 ≤ 1 / 1000 := by
  leancert?

example : ∃ N : Nat, ∀ n ≥ N, (3 : ℝ) / n ^ 2 ≤ 1 / 1000 := by
  eventual_bound?

example : True := by
  fail_if_success
    have : ∃ N : Nat, ∀ n ≥ N, (3 : ℝ) / n ^ 2 ≤ 1 / 1000 := by
      eventual_bound (maxIterations := 1)
  trivial

example : True := by
  fail_if_success
    have : ∃ N : Nat, ∀ n ≥ N, (3 : ℝ) / n ^ 2 ≤ 1 / 1000 := by
      leancert (maxIterations := 1)
  trivial

example : True := by
  fail_if_success
    have : ∃ N : Nat, ∀ n ≥ N,
        Real.log (n : ℝ) / (n : ℝ) ≤ 1 / 100 := by
      leancert
  trivial

example : ∀ n : Nat, 10 ≤ n → (2 : ℝ) / n ^ 2 ≤ 1 / 50 := by
  eventual_bound?

example : True := by
  fail_if_success
    have : ∀ n : Nat, 9 ≤ n → (1 : ℝ) / n ^ 2 ≤ 1 / 100 := by
      eventual_bound
  trivial
