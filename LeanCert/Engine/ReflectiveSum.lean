/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Engine.WitnessSum
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Reflective Sum Evaluator for O(1) Proof Size

This module provides a reflective (accumulator-based) evaluator for finite sums
that keeps proof term size constant regardless of the number of iterations.

## Motivation

When proving bounds on sums like `∑ k ∈ Icc 3 N, f(x, k)`, the standard approach
using `finsum_expand` creates an expression tree with O(N) nodes. For N=400+,
this causes:
- Memory explosion during elaboration
- Extremely slow compilation times (30+ minutes)
- Proof terms that are megabytes in size

## Solution: Reflective Verification

Instead of building an expression tree, we:
1. Define a computable function that loops and accumulates interval bounds
2. Run this function via `native_decide` (O(N) computation, O(1) proof term)
3. Prove correctness once, apply everywhere

## Main definitions

* `bklnwTermDyadic` - Interval for a single term x^(1/k - 1/3)
* `bklnwSumDyadic` - Accumulator for the BKLNW sum
* `checkBKLNWSumUpperBound` - Certificate checker for upper bounds

## Usage

```lean
-- Old approach (O(N) proof size, 30+ min compile):
theorem a2_300_old : f (exp 300) ≤ bound := by
  finsum_expand
  interval_decide

-- New approach (O(1) proof size, instant):
theorem a2_300_new : f (exp 300) ≤ bound := by
  have h := checkBKLNWSumUpperBound_correct (exp 300) 432 bound ...
  native_decide
```
-/

namespace LeanCert.Engine

open LeanCert.Core

/-! ### BKLNW Sum Configuration -/

/-- Configuration for BKLNW sum computation -/
structure BKLNWSumConfig where
  /-- Dyadic precision (e.g., -80 for ~24 decimal digits) -/
  precision : Int := -80
  /-- Taylor depth for exp/log -/
  taylorDepth : Nat := 15
  deriving Repr, DecidableEq

/-- Default high-precision configuration for BKLNW sums -/
def BKLNWSumConfig.default : BKLNWSumConfig := {}

/-- Fast configuration: lower precision for quick checks (sufficient for loose bounds) -/
def BKLNWSumConfig.fast : BKLNWSumConfig := { precision := -60, taylorDepth := 12 }

/-- High-precision configuration for tight bounds -/
def BKLNWSumConfig.highPrecision : BKLNWSumConfig := { precision := -100, taylorDepth := 18 }

/-- Convert to DyadicConfig -/
def BKLNWSumConfig.toDyadicConfig (cfg : BKLNWSumConfig) : DyadicConfig :=
  { precision := cfg.precision, taylorDepth := cfg.taylorDepth }

/-! ### Single Term Computation -/

/-- Compute interval bound for a single BKLNW term: x^(1/k - 1/3).

    For the BKLNW sum f(x) = Σ_{k=3}^{N} x^(1/k - 1/3), each term is x raised
    to the power (1/k - 1/3). For k > 3, this exponent is negative, so terms
    decay as k increases.

    Note: Requires x > 0 (base of rpow must be positive). -/
def bklnwTermDyadic (x : IntervalDyadic) (k : Nat) (cfg : BKLNWSumConfig := {}) : IntervalDyadic :=
  let p : ℚ := (1 : ℚ) / k - 1 / 3
  rpowIntervalDyadic x p cfg.toDyadicConfig

/-- Wrap bklnwTermDyadic as a witness evaluator for use with witnessSumDyadic.
    The DyadicConfig parameter is ignored — precision comes from BKLNWSumConfig. -/
def bklnwEvalTerm (x : IntervalDyadic) (cfg : BKLNWSumConfig)
    (k : Nat) (_dyadicCfg : DyadicConfig) : IntervalDyadic :=
  bklnwTermDyadic x k cfg

/-! ### Accumulator-Based Sum -/

/-- Zero interval for accumulator initialization -/
def zeroDyadic : IntervalDyadic := IntervalDyadic.singleton Core.Dyadic.zero

/-- Compute interval bound for f(x) = Σ_{k=3}^{N} x^(1/k - 1/3).

    Delegates to the generic witnessSumDyadic accumulator via bklnwEvalTerm wrapper.
    The sum starts at k=3 (matching the BKLNW definition where the k=3 term is 1). -/
def bklnwSumDyadic (x : IntervalDyadic) (limit : Nat) (cfg : BKLNWSumConfig := {}) : IntervalDyadic :=
  witnessSumDyadic (bklnwEvalTerm x cfg) 3 limit cfg.toDyadicConfig

/-! ### Optimized Sum Computation

The optimized version:
1. Precomputes log(x) once (expensive operation)
2. Handles k=3 term specially (exponent is 0, so term is exactly 1)
3. Uses batched rounding (rounds every N iterations instead of every iteration)

This gives ~2-3x speedup for large sums. -/

/-- One interval for the k=3 term (x^0 = 1) -/
def oneDyadic : IntervalDyadic := IntervalDyadic.singleton (Core.Dyadic.ofInt 1)

/-- Compute x^(1/k - 1/3) using precomputed log(x).
    Formula: x^p = exp(p * log(x)) -/
def bklnwTermFromLog (logX : IntervalDyadic) (k : Nat) (cfg : BKLNWSumConfig) : IntervalDyadic :=
  let p : ℚ := (1 : ℚ) / k - 1 / 3
  let pInterval := IntervalDyadic.ofIntervalRat (IntervalRat.singleton p) cfg.precision
  let pLogX := (IntervalDyadic.mul pInterval logX).roundOut cfg.precision
  expIntervalDyadic pLogX cfg.toDyadicConfig

/-- Optimized accumulator that uses precomputed log(x) and batched rounding.
    - logX: precomputed log(x) interval
    - roundEvery: round the accumulator every N iterations (0 = every iteration) -/
def bklnwSumAuxOpt (logX : IntervalDyadic) (current limit : Nat)
    (acc : IntervalDyadic) (cfg : BKLNWSumConfig) (roundEvery : Nat := 0) : IntervalDyadic :=
  if h : current > limit then
    acc.roundOut cfg.precision  -- Final round at the end
  else
    let term := bklnwTermFromLog logX current cfg
    let newAcc := IntervalDyadic.add acc term
    -- Batched rounding: only round every N iterations (or always if roundEvery = 0)
    let roundedAcc := if roundEvery = 0 || current % roundEvery = 0
                      then newAcc.roundOut cfg.precision
                      else newAcc
    bklnwSumAuxOpt logX (current + 1) limit roundedAcc cfg roundEvery
  termination_by limit + 1 - current

/-- Optimized BKLNW sum that precomputes log(x) once.
    - roundEvery: round accumulator every N iterations (default 8 for good balance) -/
def bklnwSumDyadicOpt (x : IntervalDyadic) (limit : Nat) (cfg : BKLNWSumConfig := {})
    (roundEvery : Nat := 8) : IntervalDyadic :=
  if limit < 3 then zeroDyadic
  else
    -- Precompute log(x) once (expensive)
    let logX := logIntervalDyadic x cfg.toDyadicConfig
    -- k=3 term: x^(1/3 - 1/3) = x^0 = 1
    let acc0 := oneDyadic
    -- Continue from k=4
    if limit < 4 then acc0
    else bklnwSumAuxOpt logX 4 limit acc0 cfg roundEvery

/-! ### Certified Cached-Log Sum

This variant precomputes `log(x)` once while preserving the exact rounding
schedule and recursion shape of `bklnwSumDyadic`, making equivalence proofs
straightforward. -/

/-- Cached-log accumulator with the same rounding schedule as `bklnwSumAux`. -/
def bklnwSumAuxCached (logX : IntervalDyadic) (current limit : Nat)
    (acc : IntervalDyadic) (cfg : BKLNWSumConfig) : IntervalDyadic :=
  if h : current > limit then
    acc
  else
    let term := bklnwTermFromLog logX current cfg
    let newAcc := (IntervalDyadic.add acc term).roundOut cfg.precision
    bklnwSumAuxCached logX (current + 1) limit newAcc cfg
  termination_by limit + 1 - current

/-- Cached-log sum for `f(x)` equivalent to `bklnwSumDyadic`. -/
def bklnwSumDyadicCached (x : IntervalDyadic) (limit : Nat) (cfg : BKLNWSumConfig := {}) :
    IntervalDyadic :=
  let logX := logIntervalDyadic x cfg.toDyadicConfig
  bklnwSumAuxCached logX 3 limit zeroDyadic cfg

/-! ### Certificate Checkers -/

/-- Check if the BKLNW sum at a specific point is bounded above.

    This is the main certificate checker. Given:
    - x_rat: The rational value of the input (e.g., exp(b) represented as interval)
    - limit: Upper bound on sum index (⌊log(x)/log(2)⌋)
    - target: The claimed upper bound

    Returns true if the computed interval upper bound is ≤ target.

    Usage: `native_decide` will evaluate this efficiently. -/
def checkBKLNWSumUpperBound (x_lo x_hi : ℚ) (hle : x_lo ≤ x_hi)
    (limit : Nat) (target : ℚ) (cfg : BKLNWSumConfig := {}) : Bool :=
  let x := IntervalDyadic.ofIntervalRat ⟨x_lo, x_hi, hle⟩ cfg.precision
  let result := bklnwSumDyadic x limit cfg
  result.upperBoundedBy target

/-- Check if the BKLNW sum at a specific point is bounded below. -/
def checkBKLNWSumLowerBound (x_lo x_hi : ℚ) (hle : x_lo ≤ x_hi)
    (limit : Nat) (target : ℚ) (cfg : BKLNWSumConfig := {}) : Bool :=
  let x := IntervalDyadic.ofIntervalRat ⟨x_lo, x_hi, hle⟩ cfg.precision
  let result := bklnwSumDyadic x limit cfg
  result.lowerBoundedBy target

/-- Check if the BKLNW sum is in an interval [lo, hi]. -/
def checkBKLNWSumBounds (x_lo x_hi : ℚ) (hle : x_lo ≤ x_hi)
    (limit : Nat) (target_lo target_hi : ℚ) (cfg : BKLNWSumConfig := {}) : Bool :=
  checkBKLNWSumLowerBound x_lo x_hi hle limit target_lo cfg &&
  checkBKLNWSumUpperBound x_lo x_hi hle limit target_hi cfg

/-! ### Convenience Functions for Common Cases -/

/-- BKLNW sum for f(exp(b)) where b is a natural number.

    For BKLNW bounds, we need f(exp(b)) where b is typically 20, 25, ..., 300.
    This function computes an interval bound for exp(b), then evaluates the sum.

    Parameters:
    - b: The exponent (e.g., 300 for f(exp(300)))
    - limit: Should be ⌊b/log(2)⌋ (the floor of b divided by log 2) -/
def bklnwSumExpDyadic (b : Nat) (limit : Nat) (cfg : BKLNWSumConfig := {}) : IntervalDyadic :=
  -- First compute exp(b) as an interval
  let bInterval := IntervalDyadic.ofIntervalRat (IntervalRat.singleton b) cfg.precision
  let expB := expIntervalDyadic bInterval cfg.toDyadicConfig
  -- Then compute the sum
  bklnwSumDyadic expB limit cfg

/-- Optimized BKLNW sum for f(exp(b)).
    Uses precomputed log and batched rounding for ~2-3x speedup. -/
def bklnwSumExpDyadicOpt (b : Nat) (limit : Nat) (cfg : BKLNWSumConfig := {})
    (roundEvery : Nat := 8) : IntervalDyadic :=
  let bInterval := IntervalDyadic.ofIntervalRat (IntervalRat.singleton b) cfg.precision
  let expB := expIntervalDyadic bInterval cfg.toDyadicConfig
  bklnwSumDyadicOpt expB limit cfg roundEvery

/-- Check upper bound for f(exp(b)). -/
def checkBKLNWExpUpperBound (b : Nat) (limit : Nat) (target : ℚ)
    (cfg : BKLNWSumConfig := {}) : Bool :=
  let result := bklnwSumExpDyadic b limit cfg
  result.upperBoundedBy target

/-- Check lower bound for f(exp(b)). -/
def checkBKLNWExpLowerBound (b : Nat) (limit : Nat) (target : ℚ)
    (cfg : BKLNWSumConfig := {}) : Bool :=
  let result := bklnwSumExpDyadic b limit cfg
  result.lowerBoundedBy target

/-- Optimized check upper bound for f(exp(b)). Uses optimized sum with precomputed log. -/
def checkBKLNWExpUpperBoundOpt (b : Nat) (limit : Nat) (target : ℚ)
    (cfg : BKLNWSumConfig := {}) (roundEvery : Nat := 8) : Bool :=
  let result := bklnwSumExpDyadicOpt b limit cfg roundEvery
  result.upperBoundedBy target

/-- Optimized check lower bound for f(exp(b)). Uses optimized sum with precomputed log. -/
def checkBKLNWExpLowerBoundOpt (b : Nat) (limit : Nat) (target : ℚ)
    (cfg : BKLNWSumConfig := {}) (roundEvery : Nat := 8) : Bool :=
  let result := bklnwSumExpDyadicOpt b limit cfg roundEvery
  result.lowerBoundedBy target

/-! ### Correctness Theorems -/

/-! #### Helper Lemmas -/

/-- Zero is contained in the zero interval -/
theorem mem_zeroDyadic : (0 : ℝ) ∈ zeroDyadic := by
  simp only [zeroDyadic, IntervalDyadic.singleton, IntervalDyadic.mem_def]
  have hz : Core.Dyadic.zero.toRat = 0 := Core.Dyadic.toRat_zero
  simp only [hz, Rat.cast_zero, le_refl, and_self]

/-- Membership in ofIntervalRat from Set.Icc membership -/
theorem IntervalDyadic.mem_ofIntervalRat_of_Icc {x : ℝ} {lo hi : ℚ} (hle : lo ≤ hi)
    (hx : x ∈ Set.Icc (lo : ℝ) hi) (prec : Int) (hprec : prec ≤ 0 := by norm_num) :
    x ∈ IntervalDyadic.ofIntervalRat ⟨lo, hi, hle⟩ prec := by
  apply IntervalDyadic.mem_ofIntervalRat _ prec hprec
  simp only [IntervalRat.mem_def]
  exact hx


/-- The BKLNW function f(x) = Σ_{k=3}^{N} x^(1/k - 1/3) -/
noncomputable def bklnwF (x : ℝ) (N : Nat) : ℝ :=
  ∑ k ∈ Finset.Icc 3 N, x ^ ((1 : ℝ) / k - 1 / 3)

/-! #### Symbolic Head-Tail Helpers for `f(exp b)` -/

/-- Closed-form term for `f(exp b)` at index `k`. -/
private noncomputable def bklnwExpTerm (b k : Nat) : ℝ :=
  Real.exp ((b : ℝ) * ((1 : ℝ) / (k : ℝ) - (1 / 3 : ℝ)))

/-- `bklnwExpTerm` decreases with `k` for `k ≥ 1`. -/
private lemma bklnwExpTerm_antitone (b : Nat) {k m : Nat} (hk : 1 ≤ k) (hkm : k ≤ m) :
    bklnwExpTerm b m ≤ bklnwExpTerm b k := by
  unfold bklnwExpTerm
  have hk_pos_nat : 0 < k := by omega
  have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk_pos_nat
  have hkmR : (k : ℝ) ≤ (m : ℝ) := by exact_mod_cast hkm
  have hdiv : (1 : ℝ) / (m : ℝ) ≤ (1 : ℝ) / (k : ℝ) :=
    one_div_le_one_div_of_le hk_pos hkmR
  have hsub : (1 : ℝ) / (m : ℝ) - (1 / 3 : ℝ) ≤ (1 : ℝ) / (k : ℝ) - (1 / 3 : ℝ) := by
    linarith
  have hb_nonneg : (0 : ℝ) ≤ (b : ℝ) := by positivity
  have hmul :
      (b : ℝ) * ((1 : ℝ) / (m : ℝ) - (1 / 3 : ℝ)) ≤
        (b : ℝ) * ((1 : ℝ) / (k : ℝ) - (1 / 3 : ℝ)) :=
    mul_le_mul_of_nonneg_left hsub hb_nonneg
  exact (Real.exp_le_exp).2 hmul

/-- Tail sum of `f(exp b)` is bounded by `card * firstTailTerm`. -/
private theorem bklnwF_exp_tail_sum_le_card_mul_head (b limit headLimit : Nat)
    (_hhead : 3 ≤ headLimit) (_hle : headLimit ≤ limit) :
    ((Finset.Icc (headLimit + 1) limit).sum (fun k => bklnwExpTerm b k)) ≤
      (((limit - headLimit : Nat) : ℝ) * bklnwExpTerm b (headLimit + 1)) := by
  have hsumN :
      ((Finset.Icc (headLimit + 1) limit).sum (fun k => bklnwExpTerm b k)) ≤
      (Finset.Icc (headLimit + 1) limit).card • bklnwExpTerm b (headLimit + 1) := by
    refine Finset.sum_le_card_nsmul (Finset.Icc (headLimit + 1) limit)
      (fun k => bklnwExpTerm b k) (bklnwExpTerm b (headLimit + 1)) ?_
    intro k hk
    have hk_ge : headLimit + 1 ≤ k := (Finset.mem_Icc.mp hk).1
    exact bklnwExpTerm_antitone b (by omega) hk_ge
  have hsum :
      ((Finset.Icc (headLimit + 1) limit).sum (fun k => bklnwExpTerm b k)) ≤
      (((Finset.Icc (headLimit + 1) limit).card : ℝ) * bklnwExpTerm b (headLimit + 1)) := by
    simpa [nsmul_eq_mul] using hsumN
  have hcard : (Finset.Icc (headLimit + 1) limit).card = limit - headLimit := by
    rw [Nat.card_Icc]
    omega
  calc
    ((Finset.Icc (headLimit + 1) limit).sum (fun k => bklnwExpTerm b k))
        ≤ (((Finset.Icc (headLimit + 1) limit).card : ℝ) * bklnwExpTerm b (headLimit + 1)) := hsum
    _ = (((limit - headLimit : Nat) : ℝ) * bklnwExpTerm b (headLimit + 1)) := by
      rw [hcard]

/-- Split `f(exp b)` into head and tail at `headLimit`. -/
private theorem bklnwF_exp_split (b limit headLimit : Nat)
    (_hhead : 3 ≤ headLimit) (hle : headLimit ≤ limit) :
    bklnwF (Real.exp (b : ℝ)) limit =
      bklnwF (Real.exp (b : ℝ)) headLimit +
      ((Finset.Icc (headLimit + 1) limit).sum
        (fun k => (Real.exp (b : ℝ)) ^ ((1 : ℝ) / (k : ℝ) - (1 / 3 : ℝ)))) := by
  unfold bklnwF
  have hunion :
      Finset.Icc 3 limit =
        Finset.Icc 3 headLimit ∪ Finset.Icc (headLimit + 1) limit := by
    ext k
    constructor
    · intro hk
      rcases Finset.mem_Icc.mp hk with ⟨hk3, hkL⟩
      by_cases hkh : k ≤ headLimit
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_Icc.mpr ⟨hk3, hkh⟩))
      · have hkgt : headLimit < k := lt_of_not_ge hkh
        exact Finset.mem_union.mpr
          (Or.inr (Finset.mem_Icc.mpr ⟨Nat.succ_le_of_lt hkgt, hkL⟩))
    · intro hk
      rcases Finset.mem_union.mp hk with hkHead | hkTail
      · rcases Finset.mem_Icc.mp hkHead with ⟨hk3, hkH⟩
        exact Finset.mem_Icc.mpr ⟨hk3, le_trans hkH hle⟩
      · rcases Finset.mem_Icc.mp hkTail with ⟨_hkH1, hkL⟩
        exact Finset.mem_Icc.mpr (by omega)
  have hdisj : Disjoint (Finset.Icc 3 headLimit) (Finset.Icc (headLimit + 1) limit) := by
    rw [Finset.disjoint_left]
    intro k hk1 hk2
    exact (Nat.not_lt_of_ge (Finset.mem_Icc.mp hk1).2) (Finset.mem_Icc.mp hk2).1
  rw [hunion, Finset.sum_union hdisj]

/-- Tail upper bound for `f(exp b)` by first-tail-term majorization. -/
private theorem bklnwF_exp_tail_upper (b limit headLimit : Nat)
    (hhead : 3 ≤ headLimit) (hle : headLimit ≤ limit) :
    bklnwF (Real.exp (b : ℝ)) limit ≤
      bklnwF (Real.exp (b : ℝ)) headLimit +
      (((limit - headLimit : Nat) : ℝ) * bklnwExpTerm b (headLimit + 1)) := by
  have hsplit := bklnwF_exp_split b limit headLimit hhead hle
  rw [hsplit]
  have htail_rewrite :
      ((Finset.Icc (headLimit + 1) limit).sum
        (fun k => (Real.exp (b : ℝ)) ^ ((1 : ℝ) / (k : ℝ) - (1 / 3 : ℝ)))) =
      ((Finset.Icc (headLimit + 1) limit).sum (fun k => bklnwExpTerm b k)) := by
    apply Finset.sum_congr rfl
    intro k _hk
    simp [bklnwExpTerm, Real.exp_mul]
  rw [htail_rewrite]
  gcongr
  exact bklnwF_exp_tail_sum_le_card_mul_head b limit headLimit hhead hle

/-- Monotonicity of truncated sums: head sum is a lower bound for full sum. -/
private theorem bklnwF_exp_head_lower (b limit headLimit : Nat)
    (hhead : 3 ≤ headLimit) (hle : headLimit ≤ limit) :
    bklnwF (Real.exp (b : ℝ)) headLimit ≤ bklnwF (Real.exp (b : ℝ)) limit := by
  have hsplit := bklnwF_exp_split b limit headLimit hhead hle
  rw [hsplit]
  have htail_nonneg :
      0 ≤ ((Finset.Icc (headLimit + 1) limit).sum
        (fun k => (Real.exp (b : ℝ)) ^ ((1 : ℝ) / (k : ℝ) - (1 / 3 : ℝ)))) := by
    refine Finset.sum_nonneg ?_
    intro k _hk
    positivity
  linarith

/-- Correctness of single term computation -/
theorem mem_bklnwTermDyadic {x : ℝ} {I : IntervalDyadic} (hx : x ∈ I)
    (hpos : I.toIntervalRat.lo > 0) (k : Nat) (_hk : k ≥ 3) (cfg : BKLNWSumConfig)
    (hprec : cfg.precision ≤ 0 := by norm_num) :
    x ^ ((1 : ℝ) / k - 1 / 3) ∈ bklnwTermDyadic I k cfg := by
  simp only [bklnwTermDyadic]
  let p : ℚ := (1 : ℚ) / k - 1 / 3
  have hp : (p : ℝ) = (1 : ℝ) / k - 1 / 3 := by
    simp only [p, Rat.cast_sub, Rat.cast_div, Rat.cast_one, Rat.cast_natCast]
    norm_num
  rw [← hp]
  exact mem_rpowIntervalDyadic hx hpos p cfg.toDyadicConfig hprec

/-- Main correctness theorem: the reflective sum correctly bounds the mathematical sum.
    Now proved via the generic mem_witnessSumDyadic from WitnessSum. -/
theorem mem_bklnwSumDyadic {x : ℝ} {I : IntervalDyadic} (hx : x ∈ I)
    (hpos : I.toIntervalRat.lo > 0) (limit : Nat)
    (cfg : BKLNWSumConfig := {})
    (hprec : cfg.precision ≤ 0 := by norm_num) :
    bklnwF x limit ∈ bklnwSumDyadic I limit cfg := by
  unfold bklnwF bklnwSumDyadic
  apply mem_witnessSumDyadic
    (fun k => x ^ ((1 : ℝ) / k - 1 / 3))
    (bklnwEvalTerm I cfg) 3 limit cfg.toDyadicConfig
  intro k hk1 _hk2
  exact mem_bklnwTermDyadic hx hpos k (by omega) cfg hprec

/-- Technical lemma: roundDown of a sufficiently large positive rational stays positive.

    For BKLNW bounds, we work with exp(b) for b ≥ 1 and precision ≤ -80. Since exp(1) > 2.7 ≥ 1,
    the condition lo ≥ 1 is always satisfied.

    The key insight: for prec ≤ 0, we have 2^(-prec) ≥ 1, so lo * 2^(-prec) ≥ lo ≥ 1,
    meaning floor(lo * 2^(-prec)) ≥ 1 > 0. -/
theorem IntervalDyadic.ofIntervalRat_lo_pos {lo hi : ℚ} (hle : lo ≤ hi)
    (hpos : lo ≥ 1) (prec : Int) (hprec : prec ≤ 0) :
    (IntervalDyadic.ofIntervalRat ⟨lo, hi, hle⟩ prec).toIntervalRat.lo > 0 := by
  simp only [IntervalDyadic.toIntervalRat, IntervalDyadic.ofIntervalRat]
  -- Need to show: (Dyadic.ofInt ⌊lo * 2^n⌋).scale2(prec).toRat > 0
  -- where n = (-prec).toNat
  rw [Core.Dyadic.toRat_scale2, Core.Dyadic.toRat_ofInt]
  -- Goal: ⌊lo * 2^n⌋ * 2^prec > 0
  -- Since prec ≤ 0, 2^prec > 0
  have h2prec_pos : (0 : ℚ) < (2 : ℚ) ^ prec := zpow_pos (by norm_num : (0 : ℚ) < 2) prec
  -- Since lo ≥ 1 and 2^n ≥ 1 (for n ≥ 0), lo * 2^n ≥ 1
  have hn_def : (-prec).toNat = (-prec : ℤ).toNat := rfl
  have hn_eq : ((-prec : ℤ).toNat : ℤ) = -prec := by omega
  have h2n_pos : (0 : ℚ) < (2 : ℚ) ^ (-prec).toNat := pow_pos (by norm_num : (0 : ℚ) < 2) _
  have h2n_ge1 : (1 : ℚ) ≤ (2 : ℚ) ^ (-prec).toNat := by
    have h2ge1 : (1 : ℚ) ≤ 2 := by norm_num
    calc (1 : ℚ) = 2 ^ 0 := by simp
      _ ≤ 2 ^ (-prec).toNat := pow_le_pow_right₀ h2ge1 (by omega : 0 ≤ (-prec).toNat)
  have hprod_ge1 : lo * (2 : ℚ) ^ (-prec).toNat ≥ 1 := by
    calc lo * (2 : ℚ) ^ (-prec).toNat ≥ 1 * 1 := mul_le_mul hpos h2n_ge1 (by norm_num) (by linarith)
      _ = 1 := by ring
  have hfloor_pos : 0 < ⌊lo * (2 : ℚ) ^ (-prec).toNat⌋ := by
    rw [Int.floor_pos]
    exact hprod_ge1
  calc (⌊lo * (2 : ℚ) ^ (-prec).toNat⌋ : ℚ) * (2 : ℚ) ^ prec
      > 0 * (2 : ℚ) ^ prec := by
        apply mul_lt_mul_of_pos_right _ h2prec_pos
        exact_mod_cast hfloor_pos
    _ = 0 := by ring

/-- Certificate correctness: if checkBKLNWSumUpperBound returns true,
    then the actual sum is bounded.

    This theorem connects native_decide verification to mathematical truth.
    Requires x_lo ≥ 1 for positivity of the dyadic interval. -/
theorem checkBKLNWSumUpperBound_correct (x_lo x_hi : ℚ) (hle : x_lo ≤ x_hi)
    (hpos : x_lo ≥ 1) (limit : Nat) (target : ℚ)
    (cfg : BKLNWSumConfig := {})
    (hprec : cfg.precision ≤ 0 := by norm_num)
    (h_check : checkBKLNWSumUpperBound x_lo x_hi hle limit target cfg = true) :
    ∀ x : ℝ, x ∈ Set.Icc (x_lo : ℝ) x_hi → bklnwF x limit ≤ target := by
  intro x hx
  -- Construct the interval
  let I := IntervalDyadic.ofIntervalRat ⟨x_lo, x_hi, hle⟩ cfg.precision
  -- Show x ∈ I
  have hxI : x ∈ I := IntervalDyadic.mem_ofIntervalRat_of_Icc hle hx cfg.precision hprec
  -- Positivity of lo
  have hposI : I.toIntervalRat.lo > 0 := IntervalDyadic.ofIntervalRat_lo_pos hle hpos cfg.precision hprec
  -- Apply main correctness theorem
  have hmem := mem_bklnwSumDyadic hxI hposI limit cfg hprec
  -- Extract upper bound
  have hhi := IntervalDyadic.le_hi_of_mem hmem
  -- h_check says result.upperBoundedBy target = true
  simp only [checkBKLNWSumUpperBound] at h_check
  have hbound := IntervalDyadic.upperBoundedBy_spec h_check
  exact le_trans hhi hbound

/-- Certificate correctness for lower bounds.
    Requires x_lo ≥ 1 for positivity of the dyadic interval. -/
theorem checkBKLNWSumLowerBound_correct (x_lo x_hi : ℚ) (hle : x_lo ≤ x_hi)
    (hpos : x_lo ≥ 1) (limit : Nat) (target : ℚ)
    (cfg : BKLNWSumConfig := {})
    (hprec : cfg.precision ≤ 0 := by norm_num)
    (h_check : checkBKLNWSumLowerBound x_lo x_hi hle limit target cfg = true) :
    ∀ x : ℝ, x ∈ Set.Icc (x_lo : ℝ) x_hi → target ≤ bklnwF x limit := by
  intro x hx
  -- Construct the interval
  let I := IntervalDyadic.ofIntervalRat ⟨x_lo, x_hi, hle⟩ cfg.precision
  -- Show x ∈ I
  have hxI : x ∈ I := IntervalDyadic.mem_ofIntervalRat_of_Icc hle hx cfg.precision hprec
  -- Positivity of lo
  have hposI : I.toIntervalRat.lo > 0 := IntervalDyadic.ofIntervalRat_lo_pos hle hpos cfg.precision hprec
  -- Apply main correctness theorem
  have hmem := mem_bklnwSumDyadic hxI hposI limit cfg hprec
  -- Extract lower bound
  have hlo := IntervalDyadic.lo_le_of_mem hmem
  -- h_check says result.lowerBoundedBy target = true
  simp only [checkBKLNWSumLowerBound] at h_check
  have hbound := IntervalDyadic.lowerBoundedBy_spec h_check
  exact le_trans hbound hlo

/-! ### Bridge Theorems for exp(b) Case -/

/-- Membership in singleton interval -/
theorem IntervalRat.mem_singleton_nat (n : Nat) : (n : ℝ) ∈ IntervalRat.singleton n := by
  simp only [IntervalRat.singleton, IntervalRat.mem_def]
  constructor <;> simp

/-- exp correctness for dyadic intervals -/
theorem mem_expIntervalDyadic {x : ℝ} {I : IntervalDyadic} (hx : x ∈ I)
    (cfg : DyadicConfig)
    (hprec : cfg.precision ≤ 0 := by norm_num) :
    Real.exp x ∈ expIntervalDyadic I cfg := by
  simp only [expIntervalDyadic]
  have hrat := IntervalDyadic.mem_toIntervalRat.mp hx
  have hexp := IntervalRat.mem_expComputable hrat cfg.taylorDepth
  exact IntervalDyadic.mem_ofIntervalRat hexp cfg.precision hprec

/-- Natural number b as real is in the singleton interval -/
theorem mem_bInterval_nat (b : Nat) (prec : Int) (hprec : prec ≤ 0 := by norm_num) :
    (b : ℝ) ∈ IntervalDyadic.ofIntervalRat (IntervalRat.singleton b) prec := by
  apply IntervalDyadic.mem_ofIntervalRat _ prec hprec
  exact IntervalRat.mem_singleton_nat b

/-- exp(b) is contained in the dyadic interval computed by bklnwSumExpDyadic -/
theorem mem_expB_of_nat (b : Nat) (cfg : BKLNWSumConfig)
    (hprec : cfg.precision ≤ 0 := by norm_num) :
    let bInterval := IntervalDyadic.ofIntervalRat (IntervalRat.singleton b) cfg.precision
    let expB := expIntervalDyadic bInterval cfg.toDyadicConfig
    Real.exp (b : ℝ) ∈ expB := by
  simp only
  have hb := mem_bInterval_nat b cfg.precision hprec
  exact mem_expIntervalDyadic hb cfg.toDyadicConfig hprec

/-- Check if expComputable produces a positive lower bound.
    This is decidable and can be verified by native_decide. -/
def checkExpComputableLoPos (I : IntervalRat) (taylorDepth : Nat) : Bool :=
  (IntervalRat.expComputable I taylorDepth).lo > 0

/-- Helper: checkExpComputableLoPos correctness -/
theorem checkExpComputableLoPos_spec {I : IntervalRat} {n : Nat}
    (h : checkExpComputableLoPos I n = true) :
    (IntervalRat.expComputable I n).lo > 0 := by
  simp only [checkExpComputableLoPos, decide_eq_true_eq] at h
  exact h

/-- Check that the exp computation on a singleton b produces lo ≥ 1.
    This is decidable and holds for b ≥ 1 with reasonable taylorDepth. -/
def checkExpBLoGe1 (b : Nat) (prec : Int) (taylorDepth : Nat) : Bool :=
  let bInterval := IntervalDyadic.ofIntervalRat (IntervalRat.singleton b) prec
  let expResult := IntervalRat.expComputable bInterval.toIntervalRat taylorDepth
  expResult.lo ≥ 1

/-- If checkExpBLoGe1 passes, then the exp interval's lo is ≥ 1 -/
theorem checkExpBLoGe1_spec {b : Nat} {prec : Int} {taylorDepth : Nat}
    (h : checkExpBLoGe1 b prec taylorDepth = true) :
    let bInterval := IntervalDyadic.ofIntervalRat (IntervalRat.singleton b) prec
    (IntervalRat.expComputable bInterval.toIntervalRat taylorDepth).lo ≥ 1 := by
  simp only [checkExpBLoGe1, decide_eq_true_eq] at h
  exact h

/-- For natural number b ≥ 1, exp(b) interval has positive lower bound.

    The proof uses that:
    1. For b ≥ 1 and reasonable taylorDepth, expComputable gives lo ≥ 1
    2. With lo ≥ 1 and prec ≤ 0, the ofIntervalRat conversion preserves lo > 0

    The first fact follows from exp(b) ≥ e > 2.7 and the Taylor series being accurate.
    This can be verified computationally for specific configs via checkExpBLoGe1. -/
theorem expB_lo_pos (b : Nat) (_hb : b ≥ 1) (cfg : BKLNWSumConfig)
    (hprec : cfg.precision ≤ 0 := by norm_num)
    (hcheck : checkExpBLoGe1 b cfg.precision cfg.taylorDepth = true := by decide) :
    let bInterval := IntervalDyadic.ofIntervalRat (IntervalRat.singleton b) cfg.precision
    let expB := expIntervalDyadic bInterval cfg.toDyadicConfig
    expB.toIntervalRat.lo > 0 := by
  simp only
  -- Get the lo ≥ 1 fact from the check
  have hlo_ge1 := checkExpBLoGe1_spec hcheck
  -- Now use ofIntervalRat_lo_pos with lo ≥ 1
  simp only [expIntervalDyadic, BKLNWSumConfig.toDyadicConfig]
  let expResult := IntervalRat.expComputable
    (IntervalDyadic.ofIntervalRat (IntervalRat.singleton ↑b) cfg.precision).toIntervalRat
    cfg.taylorDepth
  have hle : expResult.lo ≤ expResult.hi := expResult.le
  exact IntervalDyadic.ofIntervalRat_lo_pos hle hlo_ge1 cfg.precision hprec

/-- Main bridge theorem: if checkBKLNWExpUpperBound returns true, the sum is bounded.

    This is the key theorem that connects `native_decide` verification to mathematical truth
    for the BKLNW sum f(exp(b)).

    The `hexppos` argument verifies that the exp interval has positive lo (always true for
    b ≥ 1 with reasonable config).

    Usage:
    ```lean
    theorem my_bound : bklnwF (Real.exp 300) 432 ≤ 1.001 :=
      verify_bklnwF_exp_upper 300 432 (1001/1000) proofConfig
        (by decide) (by norm_num) (by decide) (by native_decide)
    ```
-/
theorem verify_bklnwF_exp_upper (b : Nat) (limit : Nat) (target : ℚ)
    (cfg : BKLNWSumConfig := {})
    (hprec : cfg.precision ≤ 0 := by norm_num)
    (hb : b ≥ 1 := by norm_num)
    (hexppos : checkExpBLoGe1 b cfg.precision cfg.taylorDepth = true)
    (h_check : checkBKLNWExpUpperBound b limit target cfg = true) :
    bklnwF (Real.exp (b : ℝ)) limit ≤ target := by
  -- Get expB interval
  let bInterval := IntervalDyadic.ofIntervalRat (IntervalRat.singleton b) cfg.precision
  let expB := expIntervalDyadic bInterval cfg.toDyadicConfig
  -- Show exp(b) ∈ expB
  have hexp : Real.exp (b : ℝ) ∈ expB := mem_expB_of_nat b cfg hprec
  -- Positivity
  have hpos : expB.toIntervalRat.lo > 0 := expB_lo_pos b hb cfg hprec hexppos
  -- Apply main correctness theorem
  have hmem := mem_bklnwSumDyadic hexp hpos limit cfg hprec
  -- Extract upper bound
  have hhi := IntervalDyadic.le_hi_of_mem hmem
  -- h_check gives us the upper bound
  simp only [checkBKLNWExpUpperBound, bklnwSumExpDyadic] at h_check
  have hbound := IntervalDyadic.upperBoundedBy_spec h_check
  exact le_trans hhi hbound

/-- Bridge theorem for lower bounds. -/
theorem verify_bklnwF_exp_lower (b : Nat) (limit : Nat) (target : ℚ)
    (cfg : BKLNWSumConfig := {})
    (hprec : cfg.precision ≤ 0 := by norm_num)
    (hb : b ≥ 1 := by norm_num)
    (hexppos : checkExpBLoGe1 b cfg.precision cfg.taylorDepth = true)
    (h_check : checkBKLNWExpLowerBound b limit target cfg = true) :
    target ≤ bklnwF (Real.exp (b : ℝ)) limit := by
  -- Get expB interval
  let bInterval := IntervalDyadic.ofIntervalRat (IntervalRat.singleton b) cfg.precision
  let expB := expIntervalDyadic bInterval cfg.toDyadicConfig
  -- Show exp(b) ∈ expB
  have hexp : Real.exp (b : ℝ) ∈ expB := mem_expB_of_nat b cfg hprec
  -- Positivity
  have hpos : expB.toIntervalRat.lo > 0 := expB_lo_pos b hb cfg hprec hexppos
  -- Apply main correctness theorem
  have hmem := mem_bklnwSumDyadic hexp hpos limit cfg hprec
  -- Extract lower bound
  have hlo := IntervalDyadic.lo_le_of_mem hmem
  -- h_check gives us the lower bound
  simp only [checkBKLNWExpLowerBound, bklnwSumExpDyadic] at h_check
  have hbound := IntervalDyadic.lowerBoundedBy_spec h_check
  exact le_trans hbound hlo

/-! ### Correctness Theorems for Optimized Version

The optimized version computes the same mathematical sum but more efficiently.
We prove correctness by showing each optimized function contains the true value. -/

/-- One is in the one interval -/
theorem mem_oneDyadic : (1 : ℝ) ∈ oneDyadic := by
  simp only [oneDyadic, IntervalDyadic.singleton, IntervalDyadic.mem_def]
  have h1 : Core.Dyadic.ofInt 1 = ⟨1, 0⟩ := rfl
  simp only [h1, Core.Dyadic.toRat, Core.Dyadic.pow2Nat]
  norm_num

/-- Cached-log term equals the standard term when `logX = logIntervalDyadic x`. -/
private theorem bklnwTermFromLog_eq_bklnwTermDyadic
    (x : IntervalDyadic) (k : Nat) (cfg : BKLNWSumConfig) :
    bklnwTermFromLog (logIntervalDyadic x cfg.toDyadicConfig) k cfg =
      bklnwTermDyadic x k cfg := by
  simp only [bklnwTermFromLog, bklnwTermDyadic, rpowIntervalDyadic,
    BKLNWSumConfig.toDyadicConfig]

/-- Cached-log accumulator is definitionally equivalent to the standard accumulator. -/
theorem bklnwSumAuxCached_eq_bklnwSumAux (x : IntervalDyadic)
    (current limit : Nat) (acc : IntervalDyadic) (cfg : BKLNWSumConfig) :
    bklnwSumAuxCached (logIntervalDyadic x cfg.toDyadicConfig) current limit acc cfg =
      bklnwSumAux x current limit acc cfg := by
  generalize hm : limit + 1 - current = m
  induction m using Nat.strongRecOn generalizing current acc with
  | ind m ih =>
      unfold bklnwSumAuxCached bklnwSumAux
      by_cases hcur : current > limit
      · simp [hcur]
      · simp only [hcur, bklnwTermFromLog_eq_bklnwTermDyadic]
        have hm' : limit + 1 - (current + 1) < m := by
          omega
        exact ih (limit + 1 - (current + 1)) hm' (current + 1)
          ((IntervalDyadic.add acc (bklnwTermDyadic x current cfg)).roundOut cfg.precision) rfl

/-- Cached-log sum equals the standard reflective sum. -/
theorem bklnwSumDyadicCached_eq (x : IntervalDyadic) (limit : Nat) (cfg : BKLNWSumConfig := {}) :
    bklnwSumDyadicCached x limit cfg = bklnwSumDyadic x limit cfg := by
  unfold bklnwSumDyadicCached bklnwSumDyadic
  simpa using bklnwSumAuxCached_eq_bklnwSumAux x 3 limit zeroDyadic cfg

/-- Cached-log exp sum, equivalent to `bklnwSumExpDyadic` but faster to evaluate. -/
def bklnwSumExpDyadicCached (b : Nat) (limit : Nat) (cfg : BKLNWSumConfig := {}) : IntervalDyadic :=
  let bInterval := IntervalDyadic.ofIntervalRat (IntervalRat.singleton b) cfg.precision
  let expB := expIntervalDyadic bInterval cfg.toDyadicConfig
  bklnwSumDyadicCached expB limit cfg

/-- Cached-log exp sum equals the standard exp sum. -/
theorem bklnwSumExpDyadicCached_eq (b : Nat) (limit : Nat) (cfg : BKLNWSumConfig := {}) :
    bklnwSumExpDyadicCached b limit cfg = bklnwSumExpDyadic b limit cfg := by
  unfold bklnwSumExpDyadicCached bklnwSumExpDyadic
  simp only [bklnwSumDyadicCached_eq]

/-! ### Alpha-scaled BKLNW bounds

For PNT+ compatibility, checkers that include the (1+α) factor
where α = 193571378/10^16 (the margin from BKLNW Table 8). -/

/-- The PNT+ alpha constant: α = 193571378/10^16 -/
def bklnwAlpha : ℚ := 193571378 / 10^16

/-- Compute (1+α) * bklnwF(exp b, limit) as a dyadic interval -/
def bklnwAlphaSumExpDyadic (b : Nat) (limit : Nat) (cfg : BKLNWSumConfig := {}) : IntervalDyadic :=
  let result := bklnwSumExpDyadic b limit cfg
  let one_plus_alpha := IntervalDyadic.ofIntervalRat
    (IntervalRat.singleton (1 + bklnwAlpha)) cfg.precision
  (IntervalDyadic.mul one_plus_alpha result).roundOut cfg.precision

/-- Check (1+α) * bklnwF(exp b, limit) ≤ target -/
def checkBKLNWAlphaExpUpperBound (b : Nat) (limit : Nat) (target : ℚ)
    (cfg : BKLNWSumConfig := {}) : Bool :=
  (bklnwAlphaSumExpDyadic b limit cfg).upperBoundedBy target

/-- Check target ≤ (1+α) * bklnwF(exp b, limit) -/
def checkBKLNWAlphaExpLowerBound (b : Nat) (limit : Nat) (target : ℚ)
    (cfg : BKLNWSumConfig := {}) : Bool :=
  (bklnwAlphaSumExpDyadic b limit cfg).lowerBoundedBy target

/-- Compute (1+α) * bklnwF(exp b, limit) using cached-log sum evaluation. -/
def bklnwAlphaSumExpDyadicCached (b : Nat) (limit : Nat) (cfg : BKLNWSumConfig := {}) :
    IntervalDyadic :=
  let result := bklnwSumExpDyadicCached b limit cfg
  let one_plus_alpha := IntervalDyadic.ofIntervalRat
    (IntervalRat.singleton (1 + bklnwAlpha)) cfg.precision
  (IntervalDyadic.mul one_plus_alpha result).roundOut cfg.precision

/-- Cached-log alpha upper-bound checker. -/
def checkBKLNWAlphaExpUpperBoundCached (b : Nat) (limit : Nat) (target : ℚ)
    (cfg : BKLNWSumConfig := {}) : Bool :=
  (bklnwAlphaSumExpDyadicCached b limit cfg).upperBoundedBy target

/-- Cached-log alpha lower-bound checker. -/
def checkBKLNWAlphaExpLowerBoundCached (b : Nat) (limit : Nat) (target : ℚ)
    (cfg : BKLNWSumConfig := {}) : Bool :=
  (bklnwAlphaSumExpDyadicCached b limit cfg).lowerBoundedBy target

/-- Cached-log two-sided checker. -/
def checkBKLNWAlphaExpBoundsCached (b : Nat) (limit : Nat) (targetLo targetHi : ℚ)
    (cfg : BKLNWSumConfig := {}) : Bool :=
  let result := bklnwAlphaSumExpDyadicCached b limit cfg
  result.lowerBoundedBy targetLo && result.upperBoundedBy targetHi

/-- Cached-log alpha interval equals the standard alpha interval. -/
theorem bklnwAlphaSumExpDyadicCached_eq (b : Nat) (limit : Nat) (cfg : BKLNWSumConfig := {}) :
    bklnwAlphaSumExpDyadicCached b limit cfg = bklnwAlphaSumExpDyadic b limit cfg := by
  unfold bklnwAlphaSumExpDyadicCached bklnwAlphaSumExpDyadic
  simp only [bklnwSumExpDyadicCached_eq]

/-- Cached-log upper-bound checker is equivalent to the standard checker. -/
theorem checkBKLNWAlphaExpUpperBoundCached_eq (b : Nat) (limit : Nat) (target : ℚ)
    (cfg : BKLNWSumConfig := {}) :
    checkBKLNWAlphaExpUpperBoundCached b limit target cfg =
      checkBKLNWAlphaExpUpperBound b limit target cfg := by
  simp only [checkBKLNWAlphaExpUpperBoundCached, checkBKLNWAlphaExpUpperBound,
    bklnwAlphaSumExpDyadicCached_eq]

/-- Cached-log lower-bound checker is equivalent to the standard checker. -/
theorem checkBKLNWAlphaExpLowerBoundCached_eq (b : Nat) (limit : Nat) (target : ℚ)
    (cfg : BKLNWSumConfig := {}) :
    checkBKLNWAlphaExpLowerBoundCached b limit target cfg =
      checkBKLNWAlphaExpLowerBound b limit target cfg := by
  simp only [checkBKLNWAlphaExpLowerBoundCached, checkBKLNWAlphaExpLowerBound,
    bklnwAlphaSumExpDyadicCached_eq]

/-- Check target_lo ≤ (1+α) * bklnwF(exp b, limit) ≤ target_hi in one pass. -/
def checkBKLNWAlphaExpBounds (b : Nat) (limit : Nat) (targetLo targetHi : ℚ)
    (cfg : BKLNWSumConfig := {}) : Bool :=
  let result := bklnwAlphaSumExpDyadic b limit cfg
  result.lowerBoundedBy targetLo && result.upperBoundedBy targetHi

/-- Extract the lower-bound checker from a successful two-sided check. -/
theorem checkBKLNWAlphaExpBounds_spec_lower (b : Nat) (limit : Nat)
    (targetLo targetHi : ℚ) (cfg : BKLNWSumConfig := {})
    (h : checkBKLNWAlphaExpBounds b limit targetLo targetHi cfg = true) :
    checkBKLNWAlphaExpLowerBound b limit targetLo cfg = true := by
  simp only [checkBKLNWAlphaExpBounds, Bool.and_eq_true] at h
  exact h.1

/-- Extract the upper-bound checker from a successful two-sided check. -/
theorem checkBKLNWAlphaExpBounds_spec_upper (b : Nat) (limit : Nat)
    (targetLo targetHi : ℚ) (cfg : BKLNWSumConfig := {})
    (h : checkBKLNWAlphaExpBounds b limit targetLo targetHi cfg = true) :
    checkBKLNWAlphaExpUpperBound b limit targetHi cfg = true := by
  simp only [checkBKLNWAlphaExpBounds, Bool.and_eq_true] at h
  exact h.2

/-- Cached-log two-sided checker is equivalent to the standard checker. -/
theorem checkBKLNWAlphaExpBoundsCached_eq (b : Nat) (limit : Nat) (targetLo targetHi : ℚ)
    (cfg : BKLNWSumConfig := {}) :
    checkBKLNWAlphaExpBoundsCached b limit targetLo targetHi cfg =
      checkBKLNWAlphaExpBounds b limit targetLo targetHi cfg := by
  simp only [checkBKLNWAlphaExpBoundsCached, checkBKLNWAlphaExpBounds,
    bklnwAlphaSumExpDyadicCached_eq]

/-! ### Symbolic Head-Tail Alpha Bounds for `f(exp b)`

For large `b`, most terms are negligible. These checkers compute a short head
sum reflectively and bound the tail symbolically by
`(limit - headLimit) * term(headLimit + 1)`. -/

/-- Dyadic interval for the closed-form tail term `exp(b * (1/k - 1/3))`. -/
private def expTermIntervalDyadic (b k : Nat) (cfg : BKLNWSumConfig := {}) : IntervalDyadic :=
  let q : ℚ := (b : ℚ) * ((1 : ℚ) / k - 1 / 3)
  let qInterval := IntervalDyadic.ofIntervalRat (IntervalRat.singleton q) cfg.precision
  expIntervalDyadic qInterval cfg.toDyadicConfig

/-- Correctness of `expTermIntervalDyadic`. -/
private theorem mem_expTermIntervalDyadic (b k : Nat) (cfg : BKLNWSumConfig)
    (hprec : cfg.precision ≤ 0 := by norm_num) :
    bklnwExpTerm b k ∈ expTermIntervalDyadic b k cfg := by
  let q : ℚ := (b : ℚ) * ((1 : ℚ) / k - 1 / 3)
  have hq_mem : (q : ℝ) ∈
      IntervalDyadic.ofIntervalRat (IntervalRat.singleton q) cfg.precision := by
    apply IntervalDyadic.mem_ofIntervalRat
    · exact IntervalRat.mem_singleton q
    · exact hprec
  have hq_mem_rat : (q : ℝ) ∈
      (IntervalDyadic.ofIntervalRat (IntervalRat.singleton q) cfg.precision).toIntervalRat :=
    IntervalDyadic.mem_toIntervalRat.mp hq_mem
  have hexp_rat : Real.exp (q : ℝ) ∈
      IntervalRat.expComputable
        ((IntervalDyadic.ofIntervalRat (IntervalRat.singleton q) cfg.precision).toIntervalRat)
        cfg.taylorDepth := IntervalRat.mem_expComputable hq_mem_rat cfg.taylorDepth
  have hexp_dyad : Real.exp (q : ℝ) ∈
      expIntervalDyadic (IntervalDyadic.ofIntervalRat (IntervalRat.singleton q) cfg.precision)
        cfg.toDyadicConfig := by
    simp [expIntervalDyadic]
    exact IntervalDyadic.mem_ofIntervalRat hexp_rat cfg.precision hprec
  simpa [expTermIntervalDyadic, bklnwExpTerm, q]
    using hexp_dyad

/-- Symbolic upper checker: α-scaled head interval + symbolic tail majorant. -/
def checkBKLNWAlphaExpUpperBoundHeadTail (b limit headLimit : Nat) (target : ℚ)
    (cfg : BKLNWSumConfig := {}) : Bool :=
  let head := bklnwSumExpDyadicCached b headLimit cfg
  let tailTerm := expTermIntervalDyadic b (headLimit + 1) cfg
  let upperQ : ℚ :=
    (1 + bklnwAlpha) * (head.hi.toRat + ((limit - headLimit : Nat) : ℚ) * tailTerm.hi.toRat)
  upperQ ≤ target

/-- Symbolic lower checker: α-scaled head interval lower endpoint only. -/
def checkBKLNWAlphaExpLowerBoundHeadTail (b _limit headLimit : Nat) (target : ℚ)
    (cfg : BKLNWSumConfig := {}) : Bool :=
  let head := bklnwSumExpDyadicCached b headLimit cfg
  let lowerQ : ℚ := (1 + bklnwAlpha) * head.lo.toRat
  target ≤ lowerQ

/-- Symbolic two-sided checker. -/
def checkBKLNWAlphaExpBoundsHeadTail (b limit headLimit : Nat) (targetLo targetHi : ℚ)
    (cfg : BKLNWSumConfig := {}) : Bool :=
  checkBKLNWAlphaExpLowerBoundHeadTail b limit headLimit targetLo cfg &&
  checkBKLNWAlphaExpUpperBoundHeadTail b limit headLimit targetHi cfg

/-- Extract lower checker from symbolic two-sided checker. -/
theorem checkBKLNWAlphaExpBoundsHeadTail_spec_lower (b limit headLimit : Nat)
    (targetLo targetHi : ℚ) (cfg : BKLNWSumConfig := {})
    (h : checkBKLNWAlphaExpBoundsHeadTail b limit headLimit targetLo targetHi cfg = true) :
    checkBKLNWAlphaExpLowerBoundHeadTail b limit headLimit targetLo cfg = true := by
  simp only [checkBKLNWAlphaExpBoundsHeadTail, Bool.and_eq_true] at h
  exact h.1

/-- Extract upper checker from symbolic two-sided checker. -/
theorem checkBKLNWAlphaExpBoundsHeadTail_spec_upper (b limit headLimit : Nat)
    (targetLo targetHi : ℚ) (cfg : BKLNWSumConfig := {})
    (h : checkBKLNWAlphaExpBoundsHeadTail b limit headLimit targetLo targetHi cfg = true) :
    checkBKLNWAlphaExpUpperBoundHeadTail b limit headLimit targetHi cfg = true := by
  simp only [checkBKLNWAlphaExpBoundsHeadTail, Bool.and_eq_true] at h
  exact h.2

/-- Bridge theorem for symbolic head-tail upper bounds. -/
theorem verify_bklnwAlpha_exp_upper_headTail (b limit headLimit : Nat) (target : ℚ)
    (cfg : BKLNWSumConfig := {})
    (hprec : cfg.precision ≤ 0 := by norm_num)
    (hb : b ≥ 1 := by norm_num)
    (hhead : 3 ≤ headLimit)
    (hle : headLimit ≤ limit)
    (hexppos : checkExpBLoGe1 b cfg.precision cfg.taylorDepth = true)
    (h_check : checkBKLNWAlphaExpUpperBoundHeadTail b limit headLimit target cfg = true) :
    (1 + bklnwAlpha : ℝ) * bklnwF (Real.exp (b : ℝ)) limit ≤ target := by
  let bInterval := IntervalDyadic.ofIntervalRat (IntervalRat.singleton b) cfg.precision
  let expB := expIntervalDyadic bInterval cfg.toDyadicConfig
  have hexp : Real.exp (b : ℝ) ∈ expB := mem_expB_of_nat b cfg hprec
  have hpos : expB.toIntervalRat.lo > 0 := expB_lo_pos b hb cfg hprec hexppos
  have hhead_mem_std : bklnwF (Real.exp (b : ℝ)) headLimit ∈ bklnwSumExpDyadic b headLimit cfg := by
    unfold bklnwSumExpDyadic
    simpa [bInterval, expB] using mem_bklnwSumDyadic hexp hpos headLimit cfg hprec
  have hhead_mem_cached : bklnwF (Real.exp (b : ℝ)) headLimit ∈ bklnwSumExpDyadicCached b headLimit cfg := by
    rw [bklnwSumExpDyadicCached_eq b headLimit cfg]
    exact hhead_mem_std
  have hhead_hi :
      bklnwF (Real.exp (b : ℝ)) headLimit ≤ (bklnwSumExpDyadicCached b headLimit cfg).hi.toRat :=
    IntervalDyadic.le_hi_of_mem hhead_mem_cached
  have htail_mem : bklnwExpTerm b (headLimit + 1) ∈ expTermIntervalDyadic b (headLimit + 1) cfg :=
    mem_expTermIntervalDyadic b (headLimit + 1) cfg hprec
  have htail_hi :
      bklnwExpTerm b (headLimit + 1) ≤ (expTermIntervalDyadic b (headLimit + 1) cfg).hi.toRat :=
    IntervalDyadic.le_hi_of_mem htail_mem
  have hsum_upper :
      bklnwF (Real.exp (b : ℝ)) limit ≤
        (bklnwSumExpDyadicCached b headLimit cfg).hi.toRat +
          (((limit - headLimit : Nat) : ℝ) * (expTermIntervalDyadic b (headLimit + 1) cfg).hi.toRat) := by
    calc
      bklnwF (Real.exp (b : ℝ)) limit
          ≤ bklnwF (Real.exp (b : ℝ)) headLimit +
              (((limit - headLimit : Nat) : ℝ) * bklnwExpTerm b (headLimit + 1)) :=
            bklnwF_exp_tail_upper b limit headLimit hhead hle
      _ ≤ (bklnwSumExpDyadicCached b headLimit cfg).hi.toRat +
            (((limit - headLimit : Nat) : ℝ) * bklnwExpTerm b (headLimit + 1)) := by
          gcongr
      _ ≤ (bklnwSumExpDyadicCached b headLimit cfg).hi.toRat +
            (((limit - headLimit : Nat) : ℝ) * (expTermIntervalDyadic b (headLimit + 1) cfg).hi.toRat) := by
          gcongr
  have halpha_nonneg : (0 : ℝ) ≤ (1 + bklnwAlpha : ℝ) := by
    norm_num [bklnwAlpha]
  have hscaled :
      (1 + bklnwAlpha : ℝ) * bklnwF (Real.exp (b : ℝ)) limit ≤
        (1 + bklnwAlpha : ℝ) *
          ((bklnwSumExpDyadicCached b headLimit cfg).hi.toRat +
            (((limit - headLimit : Nat) : ℝ) * (expTermIntervalDyadic b (headLimit + 1) cfg).hi.toRat)) :=
    mul_le_mul_of_nonneg_left hsum_upper halpha_nonneg
  have hcheck_q :
      (1 + bklnwAlpha) *
          ((bklnwSumExpDyadicCached b headLimit cfg).hi.toRat +
            ((limit - headLimit : Nat) : ℚ) * (expTermIntervalDyadic b (headLimit + 1) cfg).hi.toRat)
        ≤ target := by
    simpa [checkBKLNWAlphaExpUpperBoundHeadTail] using h_check
  have hcheck_r :
      (1 + bklnwAlpha : ℝ) *
          (((bklnwSumExpDyadicCached b headLimit cfg).hi.toRat : ℝ) +
            (((limit - headLimit : Nat) : ℚ) : ℝ) *
              ((expTermIntervalDyadic b (headLimit + 1) cfg).hi.toRat : ℝ))
        ≤ target := by
    exact_mod_cast hcheck_q
  have hcheck_r' :
      (1 + bklnwAlpha : ℝ) *
          ((bklnwSumExpDyadicCached b headLimit cfg).hi.toRat +
            (((limit - headLimit : Nat) : ℝ) * (expTermIntervalDyadic b (headLimit + 1) cfg).hi.toRat))
        ≤ target := by
    simpa using hcheck_r
  exact le_trans hscaled hcheck_r'

/-- Bridge theorem for symbolic head-tail lower bounds. -/
theorem verify_bklnwAlpha_exp_lower_headTail (b limit headLimit : Nat) (target : ℚ)
    (cfg : BKLNWSumConfig := {})
    (hprec : cfg.precision ≤ 0 := by norm_num)
    (hb : b ≥ 1 := by norm_num)
    (hhead : 3 ≤ headLimit)
    (hle : headLimit ≤ limit)
    (hexppos : checkExpBLoGe1 b cfg.precision cfg.taylorDepth = true)
    (h_check : checkBKLNWAlphaExpLowerBoundHeadTail b limit headLimit target cfg = true) :
    target ≤ (1 + bklnwAlpha : ℝ) * bklnwF (Real.exp (b : ℝ)) limit := by
  let bInterval := IntervalDyadic.ofIntervalRat (IntervalRat.singleton b) cfg.precision
  let expB := expIntervalDyadic bInterval cfg.toDyadicConfig
  have hexp : Real.exp (b : ℝ) ∈ expB := mem_expB_of_nat b cfg hprec
  have hpos : expB.toIntervalRat.lo > 0 := expB_lo_pos b hb cfg hprec hexppos
  have hhead_mem_std : bklnwF (Real.exp (b : ℝ)) headLimit ∈ bklnwSumExpDyadic b headLimit cfg := by
    unfold bklnwSumExpDyadic
    simpa [bInterval, expB] using mem_bklnwSumDyadic hexp hpos headLimit cfg hprec
  have hhead_mem_cached : bklnwF (Real.exp (b : ℝ)) headLimit ∈ bklnwSumExpDyadicCached b headLimit cfg := by
    rw [bklnwSumExpDyadicCached_eq b headLimit cfg]
    exact hhead_mem_std
  have hhead_lo :
      (bklnwSumExpDyadicCached b headLimit cfg).lo.toRat ≤ bklnwF (Real.exp (b : ℝ)) headLimit :=
    IntervalDyadic.lo_le_of_mem hhead_mem_cached
  have hhead_le_limit :
      bklnwF (Real.exp (b : ℝ)) headLimit ≤ bklnwF (Real.exp (b : ℝ)) limit :=
    bklnwF_exp_head_lower b limit headLimit hhead hle
  have hsum_lower :
      (bklnwSumExpDyadicCached b headLimit cfg).lo.toRat ≤ bklnwF (Real.exp (b : ℝ)) limit :=
    le_trans hhead_lo hhead_le_limit
  have halpha_nonneg : (0 : ℝ) ≤ (1 + bklnwAlpha : ℝ) := by
    norm_num [bklnwAlpha]
  have hscaled :
      (1 + bklnwAlpha : ℝ) * (bklnwSumExpDyadicCached b headLimit cfg).lo.toRat ≤
        (1 + bklnwAlpha : ℝ) * bklnwF (Real.exp (b : ℝ)) limit :=
    mul_le_mul_of_nonneg_left hsum_lower halpha_nonneg
  have hcheck_q :
      target ≤ (1 + bklnwAlpha) * (bklnwSumExpDyadicCached b headLimit cfg).lo.toRat := by
    simpa [checkBKLNWAlphaExpLowerBoundHeadTail] using h_check
  have hcheck_r :
      target ≤ (1 + bklnwAlpha : ℝ) * (bklnwSumExpDyadicCached b headLimit cfg).lo.toRat := by
    exact_mod_cast hcheck_q
  exact le_trans hcheck_r hscaled

/-- Bridge theorem: if checkBKLNWAlphaExpUpperBound passes,
    then (1+α) * bklnwF(exp b, limit) ≤ target. -/
theorem verify_bklnwAlpha_exp_upper (b : Nat) (limit : Nat) (target : ℚ)
    (cfg : BKLNWSumConfig := {})
    (hprec : cfg.precision ≤ 0 := by norm_num)
    (hb : b ≥ 1 := by norm_num)
    (hexppos : checkExpBLoGe1 b cfg.precision cfg.taylorDepth = true)
    (h_check : checkBKLNWAlphaExpUpperBound b limit target cfg = true) :
    (1 + bklnwAlpha : ℝ) * bklnwF (Real.exp (b : ℝ)) limit ≤ target := by
  -- Get bklnwF membership
  let bInterval := IntervalDyadic.ofIntervalRat (IntervalRat.singleton b) cfg.precision
  let expB := expIntervalDyadic bInterval cfg.toDyadicConfig
  have hexp : Real.exp (b : ℝ) ∈ expB := mem_expB_of_nat b cfg hprec
  have hpos : expB.toIntervalRat.lo > 0 := expB_lo_pos b hb cfg hprec hexppos
  have hmem_bklnw := mem_bklnwSumDyadic hexp hpos limit cfg hprec
  -- Get (1+α) membership
  have hmem_alpha : (1 + bklnwAlpha : ℝ) ∈
      IntervalDyadic.ofIntervalRat (IntervalRat.singleton (1 + bklnwAlpha)) cfg.precision := by
    exact_mod_cast IntervalDyadic.mem_ofIntervalRat (IntervalRat.mem_singleton (1 + bklnwAlpha)) cfg.precision hprec
  -- Product membership
  have hmem_prod := IntervalDyadic.mem_mul hmem_alpha hmem_bklnw
  -- Round preserves
  have hmem_round := IntervalDyadic.roundOut_contains hmem_prod cfg.precision
  -- Extract upper bound
  have hhi := IntervalDyadic.le_hi_of_mem hmem_round
  -- Check gives bound
  simp only [checkBKLNWAlphaExpUpperBound, bklnwAlphaSumExpDyadic, bklnwSumExpDyadic] at h_check
  have hbound := IntervalDyadic.upperBoundedBy_spec h_check
  exact le_trans hhi hbound

/-- Bridge theorem: if checkBKLNWAlphaExpLowerBound passes,
    then target ≤ (1+α) * bklnwF(exp b, limit). -/
theorem verify_bklnwAlpha_exp_lower (b : Nat) (limit : Nat) (target : ℚ)
    (cfg : BKLNWSumConfig := {})
    (hprec : cfg.precision ≤ 0 := by norm_num)
    (hb : b ≥ 1 := by norm_num)
    (hexppos : checkExpBLoGe1 b cfg.precision cfg.taylorDepth = true)
    (h_check : checkBKLNWAlphaExpLowerBound b limit target cfg = true) :
    target ≤ (1 + bklnwAlpha : ℝ) * bklnwF (Real.exp (b : ℝ)) limit := by
  -- Get bklnwF membership
  let bInterval := IntervalDyadic.ofIntervalRat (IntervalRat.singleton b) cfg.precision
  let expB := expIntervalDyadic bInterval cfg.toDyadicConfig
  have hexp : Real.exp (b : ℝ) ∈ expB := mem_expB_of_nat b cfg hprec
  have hpos : expB.toIntervalRat.lo > 0 := expB_lo_pos b hb cfg hprec hexppos
  have hmem_bklnw := mem_bklnwSumDyadic hexp hpos limit cfg hprec
  -- Get (1+α) membership
  have hmem_alpha : (1 + bklnwAlpha : ℝ) ∈
      IntervalDyadic.ofIntervalRat (IntervalRat.singleton (1 + bklnwAlpha)) cfg.precision := by
    exact_mod_cast IntervalDyadic.mem_ofIntervalRat (IntervalRat.mem_singleton (1 + bklnwAlpha)) cfg.precision hprec
  -- Product membership
  have hmem_prod := IntervalDyadic.mem_mul hmem_alpha hmem_bklnw
  -- Round preserves
  have hmem_round := IntervalDyadic.roundOut_contains hmem_prod cfg.precision
  -- Extract lower bound
  have hlo := IntervalDyadic.lo_le_of_mem hmem_round
  -- Check gives bound
  simp only [checkBKLNWAlphaExpLowerBound, bklnwAlphaSumExpDyadic, bklnwSumExpDyadic] at h_check
  have hbound := IntervalDyadic.lowerBoundedBy_spec h_check
  exact le_trans hbound hlo

/-! ### Convenience Functions for 2^M (Power-of-Two) Case

For BKLNW bounds on f(2^M), where 2^M is exactly representable as a rational.
No Taylor series for exp needed — just direct interval arithmetic on the sum. -/

/-- Compute (1+α) * bklnwF(2^M, M) as a dyadic interval -/
def bklnwAlphaSumPowDyadic (M : Nat) (cfg : BKLNWSumConfig := {}) : IntervalDyadic :=
  let pow2M := IntervalDyadic.ofIntervalRat (IntervalRat.singleton (2^M : ℚ)) cfg.precision
  let result := bklnwSumDyadic pow2M M cfg
  let one_plus_alpha := IntervalDyadic.ofIntervalRat
    (IntervalRat.singleton (1 + bklnwAlpha)) cfg.precision
  (IntervalDyadic.mul one_plus_alpha result).roundOut cfg.precision

/-- Check (1+α) * bklnwF(2^M, M) ≤ target -/
def checkBKLNWAlphaPowUpperBound (M : Nat) (target : ℚ)
    (cfg : BKLNWSumConfig := {}) : Bool :=
  (bklnwAlphaSumPowDyadic M cfg).upperBoundedBy target

/-- Bridge theorem: if checkBKLNWAlphaPowUpperBound passes,
    then (1+α) * bklnwF(2^M, M) ≤ target. -/
theorem verify_bklnwAlpha_pow_upper (M : Nat) (target : ℚ)
    (cfg : BKLNWSumConfig := {})
    (hprec : cfg.precision ≤ 0 := by norm_num)
    (h_check : checkBKLNWAlphaPowUpperBound M target cfg = true) :
    (1 + bklnwAlpha : ℝ) * bklnwF ((2:ℝ)^M) M ≤ target := by
  -- 2^M is rational, construct its interval
  let pow2M := IntervalDyadic.ofIntervalRat (IntervalRat.singleton (2^M : ℚ)) cfg.precision
  -- Show (2:ℝ)^M ∈ pow2M
  have hpow_mem : (2:ℝ)^M ∈ pow2M := by
    show (2:ℝ)^M ∈ IntervalDyadic.ofIntervalRat (IntervalRat.singleton (2^M : ℚ)) cfg.precision
    have : ((2^M : ℚ) : ℝ) = (2:ℝ)^M := by push_cast; ring
    rw [← this]
    exact_mod_cast IntervalDyadic.mem_ofIntervalRat (IntervalRat.mem_singleton (2^M : ℚ)) cfg.precision hprec
  -- Positivity: 2^M ≥ 1
  have hpos : pow2M.toIntervalRat.lo > 0 := by
    have h1 : (1 : ℚ) ≤ 2^M := by
      have : (1 : ℚ) ≤ 2 := by norm_num
      exact one_le_pow₀ this
    exact IntervalDyadic.ofIntervalRat_lo_pos (le_refl _) h1 cfg.precision hprec
  -- bklnwF membership
  have hmem_bklnw := mem_bklnwSumDyadic hpow_mem hpos M cfg hprec
  -- (1+α) membership
  have hmem_alpha : (1 + bklnwAlpha : ℝ) ∈
      IntervalDyadic.ofIntervalRat (IntervalRat.singleton (1 + bklnwAlpha)) cfg.precision := by
    exact_mod_cast IntervalDyadic.mem_ofIntervalRat (IntervalRat.mem_singleton (1 + bklnwAlpha)) cfg.precision hprec
  -- Product and round
  have hmem_prod := IntervalDyadic.mem_mul hmem_alpha hmem_bklnw
  have hmem_round := IntervalDyadic.roundOut_contains hmem_prod cfg.precision
  -- Extract upper bound
  have hhi := IntervalDyadic.le_hi_of_mem hmem_round
  simp only [checkBKLNWAlphaPowUpperBound, bklnwAlphaSumPowDyadic, bklnwSumDyadic] at h_check
  have hbound := IntervalDyadic.upperBoundedBy_spec h_check
  exact le_trans hhi hbound

end LeanCert.Engine
