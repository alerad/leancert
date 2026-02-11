/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Engine.IntervalEvalDyadic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat

/-!
# General Finite Sum Evaluator with O(1) Proof Size

This module provides a general accumulator-based evaluator for finite sums
over `Core.Expr`, achieving O(1) proof term size via `native_decide`.

## Motivation

`finsum_expand` expands `∑ k ∈ Icc a b, f k` into `f a + f(a+1) + ... + f b`,
creating an O(N) expression tree that blows up for N > ~100.

`ReflectiveSum` solves this with an accumulator + `native_decide`, but is
hardcoded for one specific function (BKLNW's `x^(1/k - 1/3)`).

This module generalizes the pattern: any function expressible as a `Core.Expr`
(with `var 0` as the summation index) can be bounded via the same accumulator
loop, using `evalIntervalDyadic` per term.

## Main definitions

* `finSumDyadic` - Interval bound for `∑ k ∈ Icc a b, Expr.eval [k] body`
* `checkFinSumUpperBound` - Certificate checker for upper bounds
* `checkFinSumLowerBound` - Certificate checker for lower bounds
* `verify_finsum_upper` - Bridge theorem: checker = true → sum ≤ target
* `verify_finsum_lower` - Bridge theorem: checker = true → target ≤ sum

## Usage

```lean
-- Verify ∑ k ∈ Icc 1 100, 1/k² ≤ 2 with O(1) proof:
example : checkFinSumUpperBound (Expr.inv (Expr.mul (Expr.var 0) (Expr.var 0)))
    1 100 2 { precision := -53 } = true := by native_decide
```

## Architecture

```
evalIntervalDyadic (per-term, from IntervalEvalDyadic.lean)
  ↓
finSumAux (accumulator loop)
  ↓
checkFinSumUpperBound : Bool
  ↓  native_decide
verify_finsum_upper (bridge theorem)
```
-/

namespace LeanCert.Engine

open LeanCert.Core

/-! ### Sum Lemmas

These are general lemmas for peeling elements from Finset sums.
Reusable by any accumulator-based sum evaluator. -/

/-- Sum over Icc starting at first element -/
theorem Finset.sum_Icc_eq_add_sum_Ioc' {α : Type*} [AddCommMonoid α] (f : ℕ → α) (a b : ℕ)
    (h : a ≤ b) : ∑ k ∈ Finset.Icc a b, f k = f a + ∑ k ∈ Finset.Ioc a b, f k := by
  rw [← Finset.sum_insert (s := Finset.Ioc a b) (a := a)]
  · congr 1
    ext k
    simp only [Finset.mem_insert, Finset.mem_Icc, Finset.mem_Ioc]
    omega
  · simp only [Finset.mem_Ioc]
    omega

/-- Ioc a b equals Icc (a+1) b -/
theorem Finset.Ioc_eq_Icc_succ' (a b : ℕ) : Finset.Ioc a b = Finset.Icc (a + 1) b := by
  ext k
  simp only [Finset.mem_Ioc, Finset.mem_Icc]
  omega

/-! ### Environment Helpers -/

/-- Environment for evaluating the sum body at index k.
    Maps all variables to the singleton interval [k, k].

    For single-variable bodies (var 0 = summation index), this is sufficient.
    For multi-variable bodies, a shifted version would be needed (future work). -/
def sumBodyEnvSimple (k : Nat) (prec : Int) : IntervalDyadicEnv :=
  fun _ => IntervalDyadic.ofIntervalRat (IntervalRat.singleton (k : ℚ)) prec

/-- Real environment: all variables equal (k : ℝ). -/
noncomputable def sumBodyRealEnv (k : Nat) : Nat → ℝ := fun _ => (k : ℝ)

/-- The real environment is contained in the dyadic environment. -/
theorem sumBodyEnvSimple_correct (k : Nat) (prec : Int) (hprec : prec ≤ 0) :
    envMemDyadic (sumBodyRealEnv k) (sumBodyEnvSimple k prec) := by
  intro i
  simp only [sumBodyRealEnv, sumBodyEnvSimple]
  apply IntervalDyadic.mem_ofIntervalRat _ prec hprec
  have : ((k : ℚ) : ℝ) = (k : ℝ) := by push_cast; ring
  rw [← this]
  exact IntervalRat.mem_singleton (k : ℚ)

/-! ### Per-term Evaluation -/

/-- Evaluate a single term of the sum: body evaluated at index k. -/
def evalSumTermDyadic (body : Expr) (k : Nat) (cfg : DyadicConfig) : IntervalDyadic :=
  evalIntervalDyadic body (sumBodyEnvSimple k cfg.precision) cfg

/-! ### Accumulator Loop -/

/-- Zero interval for accumulator initialization. -/
def finSumZero : IntervalDyadic := IntervalDyadic.singleton Core.Dyadic.zero

/-- Zero is in the zero interval. -/
theorem mem_finSumZero : (0 : ℝ) ∈ finSumZero := by
  simp only [finSumZero, IntervalDyadic.singleton, IntervalDyadic.mem_def]
  have hz : Core.Dyadic.zero.toRat = 0 := Core.Dyadic.toRat_zero
  simp only [hz, Rat.cast_zero, le_refl, and_self]

/-- Accumulator loop for general finite sums.
    Computes an interval containing `∑ k ∈ Icc current limit, Expr.eval [k] body`. -/
def finSumAux (body : Expr) (current limit : Nat)
    (acc : IntervalDyadic) (cfg : DyadicConfig) : IntervalDyadic :=
  if h : current > limit then
    acc
  else
    let term := evalSumTermDyadic body current cfg
    let newAcc := (IntervalDyadic.add acc term).roundOut cfg.precision
    finSumAux body (current + 1) limit newAcc cfg
  termination_by limit + 1 - current

/-- Main entry point: interval for `∑ k ∈ Icc a b, Expr.eval [k] body`. -/
def finSumDyadic (body : Expr) (a b : Nat) (cfg : DyadicConfig := {}) : IntervalDyadic :=
  finSumAux body a b finSumZero cfg

/-! ### Certificate Checkers -/

/-- Check if `∑ k ∈ Icc a b, Expr.eval [k] body ≤ target`. -/
def checkFinSumUpperBound (body : Expr) (a b : Nat) (target : ℚ)
    (cfg : DyadicConfig := {}) : Bool :=
  (finSumDyadic body a b cfg).upperBoundedBy target

/-- Check if `target ≤ ∑ k ∈ Icc a b, Expr.eval [k] body`. -/
def checkFinSumLowerBound (body : Expr) (a b : Nat) (target : ℚ)
    (cfg : DyadicConfig := {}) : Bool :=
  (finSumDyadic body a b cfg).lowerBoundedBy target

/-! ### Correctness Theorems -/

/-- Per-term correctness: the true value is in the computed interval. -/
theorem mem_evalSumTermDyadic (body : Expr) (hsupp : ExprSupportedCore body)
    (k : Nat) (cfg : DyadicConfig) (hprec : cfg.precision ≤ 0 := by norm_num)
    (hdom : evalDomainValidDyadic body (sumBodyEnvSimple k cfg.precision) cfg) :
    Expr.eval (sumBodyRealEnv k) body ∈ evalSumTermDyadic body k cfg :=
  evalIntervalDyadic_correct body hsupp (sumBodyRealEnv k)
    (sumBodyEnvSimple k cfg.precision) (sumBodyEnvSimple_correct k cfg.precision hprec)
    cfg hprec hdom

/-- Accumulator correctness: if we've accumulated correctly so far,
    adding terms preserves correctness.

    Proof structure mirrors `mem_bklnwSumAux` from ReflectiveSum.lean. -/
theorem mem_finSumAux (body : Expr) (hsupp : ExprSupportedCore body)
    (current limit : Nat) (acc : IntervalDyadic) (partialSum : ℝ)
    (hacc : partialSum ∈ acc)
    (cfg : DyadicConfig) (hprec : cfg.precision ≤ 0 := by norm_num)
    (hdom : ∀ k, current ≤ k → k ≤ limit →
        evalDomainValidDyadic body (sumBodyEnvSimple k cfg.precision) cfg) :
    (partialSum + ∑ k ∈ Finset.Icc current limit, Expr.eval (sumBodyRealEnv k) body)
      ∈ finSumAux body current limit acc cfg := by
  generalize hm : limit + 1 - current = m
  induction m using Nat.strongRecOn generalizing current acc partialSum with
  | ind m ih =>
    unfold finSumAux
    split_ifs with h
    · -- Base case: current > limit, sum is empty
      simp only [Finset.Icc_eq_empty (by omega : ¬current ≤ limit), Finset.sum_empty, add_zero]
      exact hacc
    · -- Inductive case: peel first element and recurse
      have hcur_le : current ≤ limit := Nat.le_of_not_gt h
      -- Split the sum
      rw [Finset.sum_Icc_eq_add_sum_Ioc' _ current limit hcur_le]
      rw [Finset.Ioc_eq_Icc_succ']
      -- Reassociate
      rw [← add_assoc]
      -- Term membership
      have hterm := mem_evalSumTermDyadic body hsupp current cfg hprec
        (hdom current (Nat.le_refl current) hcur_le)
      -- (partialSum + term) ∈ newAcc
      have hnewAcc : partialSum + Expr.eval (sumBodyRealEnv current) body ∈
          (IntervalDyadic.add acc (evalSumTermDyadic body current cfg)).roundOut cfg.precision := by
        apply IntervalDyadic.roundOut_contains
        exact IntervalDyadic.mem_add hacc hterm
      -- Apply induction hypothesis
      have hm' : limit + 1 - (current + 1) < m := by omega
      have hdom' : ∀ k, current + 1 ≤ k → k ≤ limit →
          evalDomainValidDyadic body (sumBodyEnvSimple k cfg.precision) cfg :=
        fun k hk1 hk2 => hdom k (by omega) hk2
      exact ih (limit + 1 - (current + 1)) hm' (current + 1) _ _ hnewAcc hdom' rfl

/-- Main correctness theorem: the computed interval contains the true sum.

    This is the "golden theorem" connecting the computable evaluator to the
    mathematical definition of the finite sum. -/
theorem mem_finSumDyadic (body : Expr) (hsupp : ExprSupportedCore body)
    (a b : Nat) (cfg : DyadicConfig := {}) (hprec : cfg.precision ≤ 0 := by norm_num)
    (hdom : ∀ k, a ≤ k → k ≤ b →
        evalDomainValidDyadic body (sumBodyEnvSimple k cfg.precision) cfg) :
    (∑ k ∈ Finset.Icc a b, Expr.eval (sumBodyRealEnv k) body) ∈ finSumDyadic body a b cfg := by
  unfold finSumDyadic
  have h := mem_finSumAux body hsupp a b finSumZero 0 mem_finSumZero cfg hprec hdom
  simp only [zero_add] at h
  exact h

/-! ### Bridge Theorems -/

/-- If checkFinSumUpperBound returns true, the sum is bounded above.

    This connects `native_decide` verification to mathematical truth. -/
theorem verify_finsum_upper (body : Expr) (hsupp : ExprSupportedCore body)
    (a b : Nat) (target : ℚ) (cfg : DyadicConfig := {})
    (hprec : cfg.precision ≤ 0 := by norm_num)
    (hdom : ∀ k, a ≤ k → k ≤ b →
        evalDomainValidDyadic body (sumBodyEnvSimple k cfg.precision) cfg)
    (h_check : checkFinSumUpperBound body a b target cfg = true) :
    ∑ k ∈ Finset.Icc a b, Expr.eval (sumBodyRealEnv k) body ≤ target := by
  have hmem := mem_finSumDyadic body hsupp a b cfg hprec hdom
  have hhi : ∑ k ∈ Finset.Icc a b, Expr.eval (sumBodyRealEnv k) body ≤
      ((finSumDyadic body a b cfg).hi.toRat : ℝ) := hmem.2
  simp only [checkFinSumUpperBound, IntervalDyadic.upperBoundedBy, decide_eq_true_eq] at h_check
  exact le_trans hhi (by exact_mod_cast h_check)

/-- If checkFinSumLowerBound returns true, the sum is bounded below. -/
theorem verify_finsum_lower (body : Expr) (hsupp : ExprSupportedCore body)
    (a b : Nat) (target : ℚ) (cfg : DyadicConfig := {})
    (hprec : cfg.precision ≤ 0 := by norm_num)
    (hdom : ∀ k, a ≤ k → k ≤ b →
        evalDomainValidDyadic body (sumBodyEnvSimple k cfg.precision) cfg)
    (h_check : checkFinSumLowerBound body a b target cfg = true) :
    target ≤ ∑ k ∈ Finset.Icc a b, Expr.eval (sumBodyRealEnv k) body := by
  have hmem := mem_finSumDyadic body hsupp a b cfg hprec hdom
  have hlo : ((finSumDyadic body a b cfg).lo.toRat : ℝ) ≤
      ∑ k ∈ Finset.Icc a b, Expr.eval (sumBodyRealEnv k) body := hmem.1
  simp only [checkFinSumLowerBound, IntervalDyadic.lowerBoundedBy, decide_eq_true_eq] at h_check
  exact le_trans (by exact_mod_cast h_check) hlo

/-! ### Domain Validity Checking Over Range -/

/-- Check domain validity for all indices in [current, limit]. -/
def checkDomainValidAllAux (body : Expr) (current limit : Nat)
    (cfg : DyadicConfig) : Bool :=
  if current > limit then true
  else
    checkDomainValidDyadic body (sumBodyEnvSimple current cfg.precision) cfg &&
    checkDomainValidAllAux body (current + 1) limit cfg
  termination_by limit + 1 - current

/-- Check domain validity for all indices in [a, b]. -/
def checkDomainValidAll (body : Expr) (a b : Nat) (cfg : DyadicConfig) : Bool :=
  checkDomainValidAllAux body a b cfg

/-- Bridge theorem: if checkDomainValidAllAux returns true,
    domain validity holds for all indices in [current, limit]. -/
theorem checkDomainValidAllAux_correct (body : Expr) (current limit : Nat)
    (cfg : DyadicConfig)
    (h : checkDomainValidAllAux body current limit cfg = true) :
    ∀ k, current ≤ k → k ≤ limit →
      evalDomainValidDyadic body (sumBodyEnvSimple k cfg.precision) cfg := by
  generalize hm : limit + 1 - current = m
  induction m using Nat.strongRecOn generalizing current with
  | ind m ih =>
    unfold checkDomainValidAllAux at h
    split_ifs at h with hgt
    · -- current > limit: vacuously true
      intro k hk1 hk2; omega
    · -- current ≤ limit: split the && check
      have hcur_le : current ≤ limit := Nat.le_of_not_gt hgt
      rw [Bool.and_eq_true] at h
      intro k hk1 hk2
      by_cases heq : k = current
      · subst heq
        exact checkDomainValidDyadic_correct body
          (sumBodyEnvSimple k cfg.precision) cfg h.1
      · have hk1' : current + 1 ≤ k := by omega
        have hm' : limit + 1 - (current + 1) < m := by omega
        exact ih (limit + 1 - (current + 1)) hm' (current + 1) h.2 rfl k hk1' hk2

/-- Bridge theorem for checkDomainValidAll. -/
theorem checkDomainValidAll_correct (body : Expr) (a b : Nat) (cfg : DyadicConfig)
    (h : checkDomainValidAll body a b cfg = true) :
    ∀ k, a ≤ k → k ≤ b →
      evalDomainValidDyadic body (sumBodyEnvSimple k cfg.precision) cfg :=
  checkDomainValidAllAux_correct body a b cfg h

/-! ### Combined Certificate Checkers (Domain + Bound) -/

/-- Check upper bound with integrated domain validity. -/
def checkFinSumUpperBoundFull (body : Expr) (a b : Nat) (target : ℚ)
    (cfg : DyadicConfig := {}) : Bool :=
  checkDomainValidAll body a b cfg && checkFinSumUpperBound body a b target cfg

/-- Check lower bound with integrated domain validity. -/
def checkFinSumLowerBoundFull (body : Expr) (a b : Nat) (target : ℚ)
    (cfg : DyadicConfig := {}) : Bool :=
  checkDomainValidAll body a b cfg && checkFinSumLowerBound body a b target cfg

/-! ### Combined Bridge Theorems (ExprSupportedCore) -/

/-- If checkFinSumUpperBoundFull returns true, the sum is bounded above.
    Domain validity is verified as part of the check. -/
theorem verify_finsum_upper_full (body : Expr) (hsupp : ExprSupportedCore body)
    (a b : Nat) (target : ℚ) (cfg : DyadicConfig := {})
    (hprec : cfg.precision ≤ 0 := by norm_num)
    (h_check : checkFinSumUpperBoundFull body a b target cfg = true) :
    ∑ k ∈ Finset.Icc a b, Expr.eval (sumBodyRealEnv k) body ≤ target := by
  simp only [checkFinSumUpperBoundFull, Bool.and_eq_true] at h_check
  exact verify_finsum_upper body hsupp a b target cfg hprec
    (checkDomainValidAll_correct body a b cfg h_check.1) h_check.2

/-- If checkFinSumLowerBoundFull returns true, the sum is bounded below.
    Domain validity is verified as part of the check. -/
theorem verify_finsum_lower_full (body : Expr) (hsupp : ExprSupportedCore body)
    (a b : Nat) (target : ℚ) (cfg : DyadicConfig := {})
    (hprec : cfg.precision ≤ 0 := by norm_num)
    (h_check : checkFinSumLowerBoundFull body a b target cfg = true) :
    target ≤ ∑ k ∈ Finset.Icc a b, Expr.eval (sumBodyRealEnv k) body := by
  simp only [checkFinSumLowerBoundFull, Bool.and_eq_true] at h_check
  exact verify_finsum_lower body hsupp a b target cfg hprec
    (checkDomainValidAll_correct body a b cfg h_check.1) h_check.2

/-! ### WithInv Correctness Chain -/

/-- Per-term correctness for ExprSupportedWithInv bodies. -/
theorem mem_evalSumTermDyadic_withInv (body : Expr) (hsupp : ExprSupportedWithInv body)
    (k : Nat) (cfg : DyadicConfig) (hprec : cfg.precision ≤ 0 := by norm_num)
    (hdom : evalDomainValidDyadic body (sumBodyEnvSimple k cfg.precision) cfg) :
    Expr.eval (sumBodyRealEnv k) body ∈ evalSumTermDyadic body k cfg :=
  evalIntervalDyadic_correct_withInv body hsupp (sumBodyRealEnv k)
    (sumBodyEnvSimple k cfg.precision) (sumBodyEnvSimple_correct k cfg.precision hprec)
    cfg hprec hdom

/-- Accumulator correctness for ExprSupportedWithInv bodies. -/
theorem mem_finSumAux_withInv (body : Expr) (hsupp : ExprSupportedWithInv body)
    (current limit : Nat) (acc : IntervalDyadic) (partialSum : ℝ)
    (hacc : partialSum ∈ acc)
    (cfg : DyadicConfig) (hprec : cfg.precision ≤ 0 := by norm_num)
    (hdom : ∀ k, current ≤ k → k ≤ limit →
        evalDomainValidDyadic body (sumBodyEnvSimple k cfg.precision) cfg) :
    (partialSum + ∑ k ∈ Finset.Icc current limit, Expr.eval (sumBodyRealEnv k) body)
      ∈ finSumAux body current limit acc cfg := by
  generalize hm : limit + 1 - current = m
  induction m using Nat.strongRecOn generalizing current acc partialSum with
  | ind m ih =>
    unfold finSumAux
    split_ifs with h
    · simp only [Finset.Icc_eq_empty (by omega : ¬current ≤ limit), Finset.sum_empty, add_zero]
      exact hacc
    · have hcur_le : current ≤ limit := Nat.le_of_not_gt h
      rw [Finset.sum_Icc_eq_add_sum_Ioc' _ current limit hcur_le]
      rw [Finset.Ioc_eq_Icc_succ']
      rw [← add_assoc]
      have hterm := mem_evalSumTermDyadic_withInv body hsupp current cfg hprec
        (hdom current (Nat.le_refl current) hcur_le)
      have hnewAcc : partialSum + Expr.eval (sumBodyRealEnv current) body ∈
          (IntervalDyadic.add acc (evalSumTermDyadic body current cfg)).roundOut cfg.precision := by
        apply IntervalDyadic.roundOut_contains
        exact IntervalDyadic.mem_add hacc hterm
      have hm' : limit + 1 - (current + 1) < m := by omega
      have hdom' : ∀ k, current + 1 ≤ k → k ≤ limit →
          evalDomainValidDyadic body (sumBodyEnvSimple k cfg.precision) cfg :=
        fun k hk1 hk2 => hdom k (by omega) hk2
      exact ih (limit + 1 - (current + 1)) hm' (current + 1) _ _ hnewAcc hdom' rfl

/-- Golden theorem for ExprSupportedWithInv bodies. -/
theorem mem_finSumDyadic_withInv (body : Expr) (hsupp : ExprSupportedWithInv body)
    (a b : Nat) (cfg : DyadicConfig := {}) (hprec : cfg.precision ≤ 0 := by norm_num)
    (hdom : ∀ k, a ≤ k → k ≤ b →
        evalDomainValidDyadic body (sumBodyEnvSimple k cfg.precision) cfg) :
    (∑ k ∈ Finset.Icc a b, Expr.eval (sumBodyRealEnv k) body) ∈ finSumDyadic body a b cfg := by
  unfold finSumDyadic
  have h := mem_finSumAux_withInv body hsupp a b finSumZero 0 mem_finSumZero cfg hprec hdom
  simp only [zero_add] at h
  exact h

/-- Bridge theorem: upper bound for ExprSupportedWithInv. -/
theorem verify_finsum_upper_withInv (body : Expr) (hsupp : ExprSupportedWithInv body)
    (a b : Nat) (target : ℚ) (cfg : DyadicConfig := {})
    (hprec : cfg.precision ≤ 0 := by norm_num)
    (hdom : ∀ k, a ≤ k → k ≤ b →
        evalDomainValidDyadic body (sumBodyEnvSimple k cfg.precision) cfg)
    (h_check : checkFinSumUpperBound body a b target cfg = true) :
    ∑ k ∈ Finset.Icc a b, Expr.eval (sumBodyRealEnv k) body ≤ target := by
  have hmem := mem_finSumDyadic_withInv body hsupp a b cfg hprec hdom
  have hhi : ∑ k ∈ Finset.Icc a b, Expr.eval (sumBodyRealEnv k) body ≤
      ((finSumDyadic body a b cfg).hi.toRat : ℝ) := hmem.2
  simp only [checkFinSumUpperBound, IntervalDyadic.upperBoundedBy, decide_eq_true_eq] at h_check
  exact le_trans hhi (by exact_mod_cast h_check)

/-- Bridge theorem: lower bound for ExprSupportedWithInv. -/
theorem verify_finsum_lower_withInv (body : Expr) (hsupp : ExprSupportedWithInv body)
    (a b : Nat) (target : ℚ) (cfg : DyadicConfig := {})
    (hprec : cfg.precision ≤ 0 := by norm_num)
    (hdom : ∀ k, a ≤ k → k ≤ b →
        evalDomainValidDyadic body (sumBodyEnvSimple k cfg.precision) cfg)
    (h_check : checkFinSumLowerBound body a b target cfg = true) :
    target ≤ ∑ k ∈ Finset.Icc a b, Expr.eval (sumBodyRealEnv k) body := by
  have hmem := mem_finSumDyadic_withInv body hsupp a b cfg hprec hdom
  have hlo : ((finSumDyadic body a b cfg).lo.toRat : ℝ) ≤
      ∑ k ∈ Finset.Icc a b, Expr.eval (sumBodyRealEnv k) body := hmem.1
  simp only [checkFinSumLowerBound, IntervalDyadic.lowerBoundedBy, decide_eq_true_eq] at h_check
  exact le_trans (by exact_mod_cast h_check) hlo

/-! ### Combined Bridge Theorems (ExprSupportedWithInv) -/

/-- Combined upper bound check for ExprSupportedWithInv bodies. -/
theorem verify_finsum_upper_full_withInv (body : Expr) (hsupp : ExprSupportedWithInv body)
    (a b : Nat) (target : ℚ) (cfg : DyadicConfig := {})
    (hprec : cfg.precision ≤ 0 := by norm_num)
    (h_check : checkFinSumUpperBoundFull body a b target cfg = true) :
    ∑ k ∈ Finset.Icc a b, Expr.eval (sumBodyRealEnv k) body ≤ target := by
  simp only [checkFinSumUpperBoundFull, Bool.and_eq_true] at h_check
  exact verify_finsum_upper_withInv body hsupp a b target cfg hprec
    (checkDomainValidAll_correct body a b cfg h_check.1) h_check.2

/-- Combined lower bound check for ExprSupportedWithInv bodies. -/
theorem verify_finsum_lower_full_withInv (body : Expr) (hsupp : ExprSupportedWithInv body)
    (a b : Nat) (target : ℚ) (cfg : DyadicConfig := {})
    (hprec : cfg.precision ≤ 0 := by norm_num)
    (h_check : checkFinSumLowerBoundFull body a b target cfg = true) :
    target ≤ ∑ k ∈ Finset.Icc a b, Expr.eval (sumBodyRealEnv k) body := by
  simp only [checkFinSumLowerBoundFull, Bool.and_eq_true] at h_check
  exact verify_finsum_lower_withInv body hsupp a b target cfg hprec
    (checkDomainValidAll_correct body a b cfg h_check.1) h_check.2

end LeanCert.Engine
