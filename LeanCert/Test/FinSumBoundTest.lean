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

-- Nested exp: exp(exp(1/k))
example : ∑ k ∈ Finset.Icc (1 : ℕ) 5, Real.exp (Real.exp ((1 : ℝ) / ↑k)) ≤ 35 := by
  finsum_bound

-- Nested inv: 1/(1 + 1/k) = k/(k+1)
example : ∑ k ∈ Finset.Icc (1 : ℕ) 10, (1 : ℝ) / ((1 : ℝ) + (1 : ℝ) / ↑k) ≤ 9 := by
  finsum_bound

-- Log with inv: log(k)/k
example : ∑ k ∈ Finset.Icc (1 : ℕ) 10, Real.log ↑k / ↑k ≤ 6 := by
  finsum_bound

-- exp of log: exp(log(k)) = k for k ≥ 1
example : ∑ k ∈ Finset.Icc (1 : ℕ) 10, Real.exp (Real.log ↑k) ≤ 56 := by
  finsum_bound

-- Triple nesting: exp(1/(1 + exp(-k)))
example : ∑ k ∈ Finset.Icc (1 : ℕ) 5, Real.exp ((1 : ℝ) / ((1 : ℝ) + Real.exp (-(↑k : ℝ)))) ≤ 14 := by
  finsum_bound

/-! ## Tier 3: Witness mode (`finsum_bound using`)

Unlike the automatic mode (Tier 1–2), witness mode lets the user supply
a custom per-term interval evaluator.  The evaluators below use the
engine's `evalSumTermDyadic` which calls `evalIntervalDyadic`—producing
*real* intervals with dyadic rounding error, not point singletons. -/

open LeanCert.Core
open LeanCert.Engine

/-- Interval evaluator for exp(k) via Taylor series + dyadic rounding. -/
def expEval (k : Nat) (cfg : DyadicConfig) : IntervalDyadic :=
  evalSumTermDyadic (.exp (.var 0)) k cfg

theorem expEval_correct (k : Nat) (cfg : DyadicConfig)
    (hprec : cfg.precision ≤ 0 := by norm_num) :
    Real.exp (↑k : ℝ) ∈ expEval k cfg :=
  mem_evalSumTermDyadic (.exp (.var 0)) (.exp (.var 0)) k cfg hprec trivial

/-- Interval evaluator for 1/k via dyadic interval arithmetic. -/
def invEval (k : Nat) (cfg : DyadicConfig) : IntervalDyadic :=
  evalSumTermDyadic (.inv (.var 0)) k cfg

theorem invEval_correct (k : Nat) (cfg : DyadicConfig)
    (hprec : cfg.precision ≤ 0 := by norm_num)
    (hdom : evalDomainValidDyadic (.inv (.var 0)) (sumBodyEnvSimple k cfg.precision) cfg) :
    (1 : ℝ) / ↑k ∈ invEval k cfg := by
  rw [one_div]
  exact mem_evalSumTermDyadic_withInv (.inv (.var 0)) (.inv (.var 0)) k cfg hprec hdom

/-- Interval evaluator for exp(1/k): nested inv inside exp. -/
def expInvEval (k : Nat) (cfg : DyadicConfig) : IntervalDyadic :=
  evalSumTermDyadic (.exp (.inv (.var 0))) k cfg

theorem expInvEval_correct (k : Nat) (cfg : DyadicConfig)
    (hprec : cfg.precision ≤ 0 := by norm_num)
    (hdom : evalDomainValidDyadic (.exp (.inv (.var 0))) (sumBodyEnvSimple k cfg.precision) cfg) :
    Real.exp ((1 : ℝ) / ↑k) ∈ expInvEval k cfg := by
  rw [one_div]
  exact mem_evalSumTermDyadic_withInv (.exp (.inv (.var 0))) (.exp (.inv (.var 0))) k cfg hprec hdom

/-- Interval evaluator for 1/(k*k). -/
def invSqEval (k : Nat) (cfg : DyadicConfig) : IntervalDyadic :=
  evalSumTermDyadic (.inv (.mul (.var 0) (.var 0))) k cfg

theorem invSqEval_correct (k : Nat) (cfg : DyadicConfig)
    (hprec : cfg.precision ≤ 0 := by norm_num)
    (hdom : evalDomainValidDyadic (.inv (.mul (.var 0) (.var 0)))
        (sumBodyEnvSimple k cfg.precision) cfg) :
    (1 : ℝ) / (↑k * ↑k) ∈ invSqEval k cfg := by
  rw [one_div]
  exact mem_evalSumTermDyadic_withInv (.inv (.mul (.var 0) (.var 0)))
    (.inv (.mul (.var 0) (.var 0))) k cfg hprec hdom

-- Witness: exp(k) upper bound (trivial domain, no inv/log)
example : ∑ k ∈ Finset.Icc (1 : ℕ) 5, Real.exp (↑k : ℝ) ≤ 234 := by
  finsum_bound using expEval (fun k _ _ => expEval_correct k _)

-- Witness: exp(k) lower bound
example : (233 : ℝ) ≤ ∑ k ∈ Finset.Icc (1 : ℕ) 5, Real.exp (↑k : ℝ) := by
  finsum_bound using expEval (fun k _ _ => expEval_correct k _)

-- Witness: 1/k upper bound (domain check via native_decide)
example : ∑ k ∈ Finset.Icc (1 : ℕ) 10, (1 : ℝ) / ↑k ≤ 4 := by
  finsum_bound using invEval (fun k ha hb => invEval_correct k {} (hdom :=
    checkDomainValidAll_correct (.inv (.var 0)) 1 10 {} (by native_decide) k ha hb))

-- Witness: 1/k lower bound
example : (1 : ℝ) ≤ ∑ k ∈ Finset.Icc (1 : ℕ) 10, (1 : ℝ) / ↑k := by
  finsum_bound using invEval (fun k ha hb => invEval_correct k {} (hdom :=
    checkDomainValidAll_correct (.inv (.var 0)) 1 10 {} (by native_decide) k ha hb))

-- Witness: exp(1/k) upper bound (nested inv inside exp, domain check)
example : ∑ k ∈ Finset.Icc (1 : ℕ) 10, Real.exp ((1 : ℝ) / ↑k) ≤ 20 := by
  finsum_bound using expInvEval (fun k ha hb => expInvEval_correct k {} (hdom :=
    checkDomainValidAll_correct (.exp (.inv (.var 0))) 1 10 {} (by native_decide) k ha hb))

-- Witness: 1/(k*k) on 100 terms (stress test)
example : ∑ k ∈ Finset.Icc (1 : ℕ) 100, (1 : ℝ) / (↑k * ↑k) ≤ 2 := by
  finsum_bound using invSqEval (fun k ha hb => invSqEval_correct k {} (hdom :=
    checkDomainValidAll_correct (.inv (.mul (.var 0) (.var 0))) 1 100 {} (by native_decide) k ha hb))

-- Witness: empty range
example : ∑ k ∈ Finset.Icc (5 : ℕ) 3, Real.exp (↑k : ℝ) ≤ 1 := by
  finsum_bound using expEval (fun k _ _ => expEval_correct k _)

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

-- Deep nesting on explicit finset: 1/(k * log(k))
example : ∑ k ∈ ({2, 3, 5, 7} : Finset ℕ), (1 : ℝ) / (↑k * Real.log ↑k) ≤ 2 := by finsum_bound

-- Nested exp on explicit finset: exp(exp(1/k))
example : ∑ k ∈ ({1, 2, 3} : Finset ℕ), Real.exp (Real.exp ((1 : ℝ) / ↑k)) ≤ 26 := by finsum_bound

end LeanCert.Test.FinSumBound
