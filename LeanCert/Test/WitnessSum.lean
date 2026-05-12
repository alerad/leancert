/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Tactic.FinSumBound

/-!
# Tests for the Witness Sum API

Verifies:
- `finsum_witness` tactic (standalone)
- `finsum_bound using` (integrated witness mode)
- Bridge theorems (`verify_witness_sum_upper`/`lower`)
-/

namespace LeanCert.Test.WitnessSum

open LeanCert.Core
open LeanCert.Engine

/-! ## Witness evaluators for testing -/

/-- Constant evaluator: always returns [1, 1]. -/
def constEval (_k : Nat) (_cfg : DyadicConfig) : IntervalDyadic :=
  IntervalDyadic.singleton (Core.Dyadic.ofInt 1)

/-- Correctness: `(1 : ℝ) ∈ constEval k cfg`. -/
theorem constEval_correct (k : Nat) (cfg : DyadicConfig) :
    (1 : ℝ) ∈ constEval k cfg := by
  show (1 : ℝ) ∈ IntervalDyadic.singleton (Core.Dyadic.ofInt 1)
  have h := IntervalDyadic.mem_singleton (Core.Dyadic.ofInt 1)
  rw [Core.Dyadic.toRat_ofInt] at h
  simpa using h

/-- Identity evaluator: returns [k, k] for each k. -/
def identityEval (k : Nat) (_cfg : DyadicConfig) : IntervalDyadic :=
  IntervalDyadic.singleton (Core.Dyadic.ofInt ↑k)

/-- Correctness: `(↑k : ℝ) ∈ identityEval k cfg`. -/
theorem identityEval_correct (k : Nat) (cfg : DyadicConfig) :
    (↑k : ℝ) ∈ identityEval k cfg := by
  show (↑k : ℝ) ∈ IntervalDyadic.singleton (Core.Dyadic.ofInt ↑k)
  have h := IntervalDyadic.mem_singleton (Core.Dyadic.ofInt ↑k)
  rw [Core.Dyadic.toRat_ofInt] at h
  simpa using h

/-! ## Tests via `finsum_witness` tactic (standalone) -/

-- Basic: ∑ 1 ≤ 11 via constant witness
example : ∑ _k ∈ Finset.Icc 1 10, (1 : ℝ) ≤ 11 := by
  finsum_witness constEval using (fun _ _ _ => constEval_correct _ _)

-- Lower bound: 1 ≤ ∑ 1 via constant witness
example : (1 : ℝ) ≤ ∑ _k ∈ Finset.Icc 1 10, (1 : ℝ) := by
  finsum_witness constEval using (fun _ _ _ => constEval_correct _ _)

-- Empty sum: ∑ over Icc 5 3 (empty range)
example : ∑ _k ∈ Finset.Icc 5 3, (1 : ℝ) ≤ 1 := by
  finsum_witness constEval using (fun _ _ _ => constEval_correct _ _)

-- Larger sum: 100 terms via constant witness
example : ∑ _k ∈ Finset.Icc 1 100, (1 : ℝ) ≤ 101 := by
  finsum_witness constEval using (fun _ _ _ => constEval_correct _ _)

-- Identity: ∑ k for k ∈ Icc 1 10 ≤ 56 (actual = 55)
example : ∑ k ∈ Finset.Icc (1 : ℕ) 10, (↑k : ℝ) ≤ 56 := by
  finsum_witness identityEval using (fun k _ _ => identityEval_correct k _)

-- Identity lower bound: 50 ≤ ∑ k for k ∈ Icc 1 10
example : (50 : ℝ) ≤ ∑ k ∈ Finset.Icc (1 : ℕ) 10, (↑k : ℝ) := by
  finsum_witness identityEval using (fun k _ _ => identityEval_correct k _)

/-! ## Tests via `finsum_bound using` (integrated witness mode) -/

-- finsum_bound using: constant witness upper bound
example : ∑ _k ∈ Finset.Icc 1 10, (1 : ℝ) ≤ 11 := by
  finsum_bound using constEval (fun _ _ _ => constEval_correct _ _)

-- finsum_bound using: constant witness lower bound
example : (1 : ℝ) ≤ ∑ _k ∈ Finset.Icc 1 10, (1 : ℝ) := by
  finsum_bound using constEval (fun _ _ _ => constEval_correct _ _)

-- finsum_bound using: identity witness upper bound
example : ∑ k ∈ Finset.Icc (1 : ℕ) 10, (↑k : ℝ) ≤ 56 := by
  finsum_bound using identityEval (fun k _ _ => identityEval_correct k _)

-- finsum_bound using: identity witness lower bound
example : (50 : ℝ) ≤ ∑ k ∈ Finset.Icc (1 : ℕ) 10, (↑k : ℝ) := by
  finsum_bound using identityEval (fun k _ _ => identityEval_correct k _)

-- finsum_bound using: empty range
example : ∑ _k ∈ Finset.Icc 5 3, (1 : ℝ) ≤ 1 := by
  finsum_bound using constEval (fun _ _ _ => constEval_correct _ _)

-- finsum_bound using: larger sum
example : ∑ _k ∈ Finset.Icc 1 100, (1 : ℝ) ≤ 101 := by
  finsum_bound using constEval (fun _ _ _ => constEval_correct _ _)

-- finsum_bound using: identity witness, larger range
example : ∑ k ∈ Finset.Icc (1 : ℕ) 100, (↑k : ℝ) ≤ 5051 := by
  finsum_bound using identityEval (fun k _ _ => identityEval_correct k _)

/-! ## Tests via direct bridge theorem application -/

-- Direct use of verify_witness_sum_upper (no tactic)
example : ∑ _k ∈ Finset.Icc 1 10, (1 : ℝ) ≤ 11 :=
  verify_witness_sum_upper (fun _ => 1) constEval 1 10 11
    { precision := -53, taylorDepth := 10, roundAfterOps := 0 }
    (fun _ _ _ => constEval_correct _ _)
    (by native_decide)

-- Direct use of verify_witness_sum_lower (no tactic)
example : (1 : ℝ) ≤ ∑ _k ∈ Finset.Icc 1 10, (1 : ℝ) := by
  have h := verify_witness_sum_lower (fun _ => (1 : ℝ)) constEval 1 10 1
    { precision := -53, taylorDepth := 10, roundAfterOps := 0 }
    (fun _ _ _ => constEval_correct _ _)
    (by native_decide)
  norm_cast at h

end LeanCert.Test.WitnessSum
