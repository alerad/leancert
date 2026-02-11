/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Tactic.FinSumBound

/-!
# Tests for `finsum_bound`

Verifies that the `finsum_bound` tactic can prove bounds on finite sums
with O(1) proof size via `native_decide`.
-/

namespace LeanCert.Test.FinSumBound

-- Basic: sum of constants (upper)
example : ∑ _k ∈ Finset.Icc 1 10, (1 : ℝ) ≤ 11 := by
  finsum_bound

-- Basic: sum of constants (lower)
example : (1 : ℝ) ≤ ∑ _k ∈ Finset.Icc 1 10, (1 : ℝ) := by
  finsum_bound

-- Edge: singleton sum
example : ∑ _k ∈ Finset.Icc 5 5, (1 : ℝ) ≤ 2 := by
  finsum_bound

-- Edge: empty sum
example : ∑ _k ∈ Finset.Icc 5 3, (1 : ℝ) ≤ 1 := by
  finsum_bound

-- Sum using the index: ∑ ↑k (Nat → ℝ cast)
example : ∑ k ∈ Finset.Icc (1 : ℕ) 10, (↑k : ℝ) ≤ 56 := by
  finsum_bound

-- Transcendental: ∑ exp(constant)
example : ∑ _k ∈ Finset.Icc 1 5, Real.exp (1 : ℝ) ≤ 15 := by
  finsum_bound

-- Larger sum: 100 terms (would blow up with finsum_expand)
example : ∑ _k ∈ Finset.Icc 1 100, (1 : ℝ) ≤ 101 := by
  finsum_bound

/-! ## Tier 2: Bodies with inv/log (domain validity checked per-k) -/

-- inv: ∑ 1/(k*k) upper bound (uses ExprSupportedWithInv)
example : ∑ k ∈ Finset.Icc (1 : ℕ) 100, (1 : ℝ) / (↑k * ↑k) ≤ 2 := by
  finsum_bound

-- inv: harmonic partial sum lower bound
example : (1 : ℝ) ≤ ∑ k ∈ Finset.Icc (1 : ℕ) 10, (1 : ℝ) / ↑k := by
  finsum_bound

-- log: ∑ log(k) for k ≥ 1 (positive domain)
example : ∑ k ∈ Finset.Icc (1 : ℕ) 10, Real.log ↑k ≤ 16 := by
  finsum_bound

-- Combined: exp(1/k) with inv inside exp
example : ∑ k ∈ Finset.Icc (1 : ℕ) 10, Real.exp ((1 : ℝ) / ↑k) ≤ 20 := by
  finsum_bound

-- Larger N with inv (stress test O(1) proof size)
example : ∑ k ∈ Finset.Icc (1 : ℕ) 500, (1 : ℝ) / (↑k * ↑k) ≤ 2 := by
  finsum_bound

/-! ## Tier 3: Witness mode (`finsum_bound using`) -/

open LeanCert.Core
open LeanCert.Engine

/-- Constant evaluator: always returns [1, 1]. -/
def constEval (_k : Nat) (_cfg : DyadicConfig) : IntervalDyadic :=
  IntervalDyadic.singleton (Core.Dyadic.ofInt 1)

theorem constEval_correct (k : Nat) (cfg : DyadicConfig) :
    (1 : ℝ) ∈ constEval k cfg := by
  show (1 : ℝ) ∈ IntervalDyadic.singleton (Core.Dyadic.ofInt 1)
  have h := IntervalDyadic.mem_singleton (Core.Dyadic.ofInt 1)
  rw [Core.Dyadic.toRat_ofInt] at h
  simpa using h

/-- Identity evaluator: returns [k, k] for each k. -/
def identityEval (k : Nat) (_cfg : DyadicConfig) : IntervalDyadic :=
  IntervalDyadic.singleton (Core.Dyadic.ofInt ↑k)

theorem identityEval_correct (k : Nat) (cfg : DyadicConfig) :
    (↑k : ℝ) ∈ identityEval k cfg := by
  show (↑k : ℝ) ∈ IntervalDyadic.singleton (Core.Dyadic.ofInt ↑k)
  have h := IntervalDyadic.mem_singleton (Core.Dyadic.ofInt ↑k)
  rw [Core.Dyadic.toRat_ofInt] at h
  simpa using h

-- Witness: constant upper bound
example : ∑ _k ∈ Finset.Icc 1 10, (1 : ℝ) ≤ 11 := by
  finsum_bound using constEval (fun _ _ _ => constEval_correct _ _)

-- Witness: constant lower bound
example : (1 : ℝ) ≤ ∑ _k ∈ Finset.Icc 1 10, (1 : ℝ) := by
  finsum_bound using constEval (fun _ _ _ => constEval_correct _ _)

-- Witness: identity upper bound (each term = k)
example : ∑ k ∈ Finset.Icc (1 : ℕ) 10, (↑k : ℝ) ≤ 56 := by
  finsum_bound using identityEval (fun k _ _ => identityEval_correct k _)

-- Witness: identity lower bound
example : (50 : ℝ) ≤ ∑ k ∈ Finset.Icc (1 : ℕ) 10, (↑k : ℝ) := by
  finsum_bound using identityEval (fun k _ _ => identityEval_correct k _)

-- Witness: empty range
example : ∑ _k ∈ Finset.Icc 5 3, (1 : ℝ) ≤ 1 := by
  finsum_bound using constEval (fun _ _ _ => constEval_correct _ _)

-- Witness: larger sum (100 terms)
example : ∑ _k ∈ Finset.Icc 1 100, (1 : ℝ) ≤ 101 := by
  finsum_bound using constEval (fun _ _ _ => constEval_correct _ _)

-- Witness: identity, larger range (∑ k for k=1..100 = 5050)
example : ∑ k ∈ Finset.Icc (1 : ℕ) 100, (↑k : ℝ) ≤ 5051 := by
  finsum_bound using identityEval (fun k _ _ => identityEval_correct k _)

/-! ## Tier 4: Arbitrary finite sets (list path) -/

-- Finset.range
example : ∑ _k ∈ Finset.range 10, (1 : ℝ) ≤ 11 := by finsum_bound

-- Finset.Ico
example : ∑ k ∈ Finset.Ico (1 : ℕ) 11, (1 : ℝ) / ↑k ≤ 4 := by finsum_bound

-- Finset.Ioc
example : ∑ k ∈ Finset.Ioc (0 : ℕ) 5, (↑k : ℝ) ≤ 16 := by finsum_bound

-- Explicit finset
example : ∑ k ∈ ({1, 3, 5, 7} : Finset ℕ), (↑k : ℝ) ≤ 17 := by finsum_bound

-- Explicit finset with inv
example : ∑ k ∈ ({1, 2, 4, 8} : Finset ℕ), (1 : ℝ) / ↑k ≤ 2 := by finsum_bound

-- Lower bound with Finset.range
example : (10 : ℝ) ≤ ∑ k ∈ Finset.range 6, (↑k : ℝ) := by finsum_bound

-- Sparse set with exp
example : ∑ k ∈ ({1, 10, 100} : Finset ℕ), Real.exp (-(↑k : ℝ)) ≤ 1 := by finsum_bound

/-! ## Tier 5: Nested inv/exp/log (deep nesting stress tests) -/

-- Nested exp: exp(exp(1/k))
example : ∑ k ∈ Finset.Icc (1 : ℕ) 5, Real.exp (Real.exp ((1 : ℝ) / ↑k)) ≤ 35 := by
  finsum_bound

-- Nested inv: 1/(1 + 1/k) = k/(k+1)
example : ∑ k ∈ Finset.Icc (1 : ℕ) 10, (1 : ℝ) / ((1 : ℝ) + (1 : ℝ) / ↑k) ≤ 9 := by
  finsum_bound

-- Log with inv: log(k)/k
example : ∑ k ∈ Finset.Icc (1 : ℕ) 10, Real.log ↑k / ↑k ≤ 6 := by
  finsum_bound

-- Deep nesting on explicit finset: 1/(k * log(k))
example : ∑ k ∈ ({2, 3, 5, 7} : Finset ℕ), (1 : ℝ) / (↑k * Real.log ↑k) ≤ 2 := by
  finsum_bound

-- Nested exp on explicit finset: exp(exp(1/k))
example : ∑ k ∈ ({1, 2, 3} : Finset ℕ), Real.exp (Real.exp ((1 : ℝ) / ↑k)) ≤ 26 := by
  finsum_bound

-- exp of log: exp(log(k)) = k for k ≥ 1
example : ∑ k ∈ Finset.Icc (1 : ℕ) 10, Real.exp (Real.log ↑k) ≤ 56 := by
  finsum_bound

-- Triple nesting: exp(1/(1 + exp(-k)))
example : ∑ k ∈ Finset.Icc (1 : ℕ) 5, Real.exp ((1 : ℝ) / ((1 : ℝ) + Real.exp (-(↑k : ℝ)))) ≤ 14 := by
  finsum_bound

end LeanCert.Test.FinSumBound
