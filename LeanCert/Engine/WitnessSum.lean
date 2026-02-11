/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Engine.FinSumDyadic

/-!
# Witness-Based Finite Sum Evaluator

Generic accumulator loop for finite sums parameterized by a user-provided
per-term evaluator. Unlike `FinSumDyadic` (which uses `Core.Expr` + `evalIntervalDyadic`),
this module accepts any computable evaluator `Nat → DyadicConfig → IntervalDyadic`
paired with a correctness proof.

## Motivation

`finsum_bound` auto-reifies to `Core.Expr`, which covers +, *, inv, exp, sin, log, etc.
Functions outside `Core.Expr` (like `rpow` in BKLNW's `x^(1/k - 1/3)`) need a custom
evaluator. The witness API provides the accumulator + bridge theorems; the user provides
the per-term evaluator + its correctness proof.

## Usage

```lean
-- User defines:
def myEval (k : Nat) (cfg : DyadicConfig) : IntervalDyadic := ...
theorem myEval_correct (k : Nat) ... : myF k ∈ myEval k cfg := ...

-- Prove bound:
example : ∑ k ∈ Finset.Icc 1 100, myF k ≤ target :=
  verify_witness_sum_upper myF myEval 1 100 target cfg myEval_correct (by native_decide)
```
-/

namespace LeanCert.Engine

open LeanCert.Core

/-! ### Accumulator Loop -/

/-- Accumulator loop parameterized by a user-provided evaluator.
    Computes an interval containing `∑ k ∈ Icc current limit, f k`. -/
def witnessSumAux (evalTerm : Nat → DyadicConfig → IntervalDyadic)
    (current limit : Nat) (acc : IntervalDyadic)
    (cfg : DyadicConfig) : IntervalDyadic :=
  if current > limit then acc
  else
    let term := evalTerm current cfg
    let newAcc := (IntervalDyadic.add acc term).roundOut cfg.precision
    witnessSumAux evalTerm (current + 1) limit newAcc cfg
  termination_by limit + 1 - current

/-- Main entry point: interval for `∑ k ∈ Icc a b, f k` using a witness evaluator. -/
def witnessSumDyadic (evalTerm : Nat → DyadicConfig → IntervalDyadic)
    (a b : Nat) (cfg : DyadicConfig) : IntervalDyadic :=
  witnessSumAux evalTerm a b finSumZero cfg

/-! ### Certificate Checkers -/

/-- Check if `∑ k ∈ Icc a b, f k ≤ target` using the witness evaluator. -/
def checkWitnessSumUpperBound (evalTerm : Nat → DyadicConfig → IntervalDyadic)
    (a b : Nat) (target : ℚ) (cfg : DyadicConfig) : Bool :=
  (witnessSumDyadic evalTerm a b cfg).upperBoundedBy target

/-- Check if `target ≤ ∑ k ∈ Icc a b, f k` using the witness evaluator. -/
def checkWitnessSumLowerBound (evalTerm : Nat → DyadicConfig → IntervalDyadic)
    (a b : Nat) (target : ℚ) (cfg : DyadicConfig) : Bool :=
  (witnessSumDyadic evalTerm a b cfg).lowerBoundedBy target

/-! ### Correctness Theorems -/

/-- Accumulator correctness: if the evaluator is sound for each term,
    the accumulator produces a sound interval for the partial sum. -/
theorem mem_witnessSumAux (f : Nat → ℝ) (evalTerm : Nat → DyadicConfig → IntervalDyadic)
    (current limit : Nat) (acc : IntervalDyadic) (partialSum : ℝ)
    (hacc : partialSum ∈ acc) (cfg : DyadicConfig)
    (hmem : ∀ k, current ≤ k → k ≤ limit → f k ∈ evalTerm k cfg) :
    (partialSum + ∑ k ∈ Finset.Icc current limit, f k)
      ∈ witnessSumAux evalTerm current limit acc cfg := by
  generalize hm : limit + 1 - current = m
  induction m using Nat.strongRecOn generalizing current acc partialSum with
  | ind m ih =>
    unfold witnessSumAux
    split_ifs with h
    · simp only [Finset.Icc_eq_empty (by omega : ¬current ≤ limit), Finset.sum_empty, add_zero]
      exact hacc
    · have hcur_le : current ≤ limit := Nat.le_of_not_gt h
      rw [Finset.sum_Icc_eq_add_sum_Ioc' _ current limit hcur_le]
      rw [Finset.Ioc_eq_Icc_succ']
      rw [← add_assoc]
      have hterm := hmem current (Nat.le_refl current) hcur_le
      have hnewAcc : partialSum + f current ∈
          (IntervalDyadic.add acc (evalTerm current cfg)).roundOut cfg.precision := by
        apply IntervalDyadic.roundOut_contains
        exact IntervalDyadic.mem_add hacc hterm
      have hm' : limit + 1 - (current + 1) < m := by omega
      have hmem' : ∀ k, current + 1 ≤ k → k ≤ limit → f k ∈ evalTerm k cfg :=
        fun k hk1 hk2 => hmem k (by omega) hk2
      exact ih (limit + 1 - (current + 1)) hm' (current + 1) _ _ hnewAcc hmem' rfl

/-- Golden theorem: the computed interval contains the true sum. -/
theorem mem_witnessSumDyadic (f : Nat → ℝ) (evalTerm : Nat → DyadicConfig → IntervalDyadic)
    (a b : Nat) (cfg : DyadicConfig)
    (hmem : ∀ k, a ≤ k → k ≤ b → f k ∈ evalTerm k cfg) :
    (∑ k ∈ Finset.Icc a b, f k) ∈ witnessSumDyadic evalTerm a b cfg := by
  unfold witnessSumDyadic
  have h := mem_witnessSumAux f evalTerm a b finSumZero 0 mem_finSumZero cfg hmem
  simp only [zero_add] at h
  exact h

/-! ### Bridge Theorems -/

/-- If checkWitnessSumUpperBound returns true, the sum is bounded above. -/
theorem verify_witness_sum_upper (f : Nat → ℝ)
    (evalTerm : Nat → DyadicConfig → IntervalDyadic)
    (a b : Nat) (target : ℚ) (cfg : DyadicConfig)
    (hmem : ∀ k, a ≤ k → k ≤ b → f k ∈ evalTerm k cfg)
    (h_check : checkWitnessSumUpperBound evalTerm a b target cfg = true) :
    ∑ k ∈ Finset.Icc a b, f k ≤ target := by
  have hsum := mem_witnessSumDyadic f evalTerm a b cfg hmem
  have hhi : ∑ k ∈ Finset.Icc a b, f k ≤
      ((witnessSumDyadic evalTerm a b cfg).hi.toRat : ℝ) := hsum.2
  simp only [checkWitnessSumUpperBound, IntervalDyadic.upperBoundedBy,
    decide_eq_true_eq] at h_check
  exact le_trans hhi (by exact_mod_cast h_check)

/-- If checkWitnessSumLowerBound returns true, the sum is bounded below. -/
theorem verify_witness_sum_lower (f : Nat → ℝ)
    (evalTerm : Nat → DyadicConfig → IntervalDyadic)
    (a b : Nat) (target : ℚ) (cfg : DyadicConfig)
    (hmem : ∀ k, a ≤ k → k ≤ b → f k ∈ evalTerm k cfg)
    (h_check : checkWitnessSumLowerBound evalTerm a b target cfg = true) :
    target ≤ ∑ k ∈ Finset.Icc a b, f k := by
  have hsum := mem_witnessSumDyadic f evalTerm a b cfg hmem
  have hlo : ((witnessSumDyadic evalTerm a b cfg).lo.toRat : ℝ) ≤
      ∑ k ∈ Finset.Icc a b, f k := hsum.1
  simp only [checkWitnessSumLowerBound, IntervalDyadic.lowerBoundedBy,
    decide_eq_true_eq] at h_check
  exact le_trans (by exact_mod_cast h_check) hlo

end LeanCert.Engine
