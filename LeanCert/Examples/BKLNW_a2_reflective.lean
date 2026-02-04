/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Engine.ReflectiveSum
import LeanCert.Examples.BKLNW_a2_pow2
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# BKLNW a₂ Certificates via Reflective Sum Evaluator

This module provides O(1) proof term BKLNW bounds using reflective verification.
It can replace the slow proofs in BKLNW_a2_exp.lean.

## Performance comparison

| b value | Old (finsum_expand) | New (reflective) |
|---------|---------------------|------------------|
| 100     | ~5 min              | <1 sec           |
| 150     | ~10 min             | <1 sec           |
| 200     | ~15 min             | <1 sec           |
| 250     | ~20 min             | <1 sec           |
| 300     | ~30 min             | <1 sec           |

## How it works

1. `bklnwSumExpDyadic b limit` computes an interval containing f(exp(b))
2. `checkBKLNWExpUpperBound b limit target` verifies upper bound via native computation
3. `native_decide` creates O(1) proof term by running the computation
4. Correctness theorems connect this to the mathematical statement
-/

namespace LeanCert.Examples.BKLNW_a2_reflective

open Real
open LeanCert.Engine
open LeanCert.Core

/-! ### Computational Tests

These `#eval` commands verify that the reflective evaluator computes correct bounds.
No proof terms are created - this is pure computation. -/

-- Test: compute f(exp(20)) bound with limit=28
#eval
  let cfg : BKLNWSumConfig := { precision := -80, taylorDepth := 15 }
  let result := bklnwSumExpDyadic 20 28 cfg
  let lo := result.toIntervalRat.lo
  let hi := result.toIntervalRat.hi
  s!"f(exp(20)) ∈ [{lo}, {hi}]"

-- Test: compute f(exp(100)) bound with limit=144
#eval
  let cfg : BKLNWSumConfig := { precision := -80, taylorDepth := 15 }
  let result := bklnwSumExpDyadic 100 144 cfg
  let lo := result.toIntervalRat.lo
  let hi := result.toIntervalRat.hi
  s!"f(exp(100)) ∈ [{lo}, {hi}]"

-- Test: compute f(exp(300)) bound with limit=432
-- This is the expensive case that previously took 30+ minutes!
#eval
  let cfg : BKLNWSumConfig := { precision := -80, taylorDepth := 15 }
  let result := bklnwSumExpDyadic 300 432 cfg
  let lo := result.toIntervalRat.lo
  let hi := result.toIntervalRat.hi
  s!"f(exp(300)) ∈ [{lo}, {hi}]"

/-! ### Certificate Checks

These verify the bounds via native computation (no proof term expansion). -/

-- Verify b=100 upper bound check passes
#eval checkBKLNWExpUpperBound 100 144 (1001 / 1000) { precision := -80 }

-- Verify b=300 upper bound check passes
#eval checkBKLNWExpUpperBound 300 432 (1001 / 1000) { precision := -80 }

/-! ### Connecting to PNT+ Definition

The PNT+ definition is f(x) = Σ_{k=3}^{⌊log(x)/log(2)⌋} x^(1/k - 1/3).
For x = exp(b), we have log(exp(b))/log(2) = b/log(2), so the limit is ⌊b/log(2)⌋.

Our bklnwF takes the limit as an explicit parameter:
  bklnwF (exp b) N = Σ_{k=3}^{N} (exp b)^(1/k - 1/3)

So f(exp(b)) = bklnwF (exp b) ⌊b/log(2)⌋ when the floors match. -/

-- For b=20: ⌊20/log(2)⌋ = ⌊28.85...⌋ = 28
-- For b=100: ⌊100/log(2)⌋ = ⌊144.26...⌋ = 144
-- For b=300: ⌊300/log(2)⌋ = ⌊432.80...⌋ = 432

/-! ### Verified Bounds via native_decide

These examples demonstrate that the certificate checks pass.
The proofs are O(1) size regardless of the sum length! -/

-- High-precision config for proofs
def proofConfig : BKLNWSumConfig := { precision := -100, taylorDepth := 18 }

-- b = 100: instant proof (previously ~5 min)
example : checkBKLNWExpUpperBound 100 144 (10003/10000) proofConfig = true := by native_decide
example : checkBKLNWExpLowerBound 100 144 (10002/10000) proofConfig = true := by native_decide

-- b = 150: instant proof (previously ~10 min)
example : checkBKLNWExpUpperBound 150 216 (100001/100000) proofConfig = true := by native_decide
example : checkBKLNWExpLowerBound 150 216 (1) proofConfig = true := by native_decide

-- b = 200: instant proof (previously ~15 min)
example : checkBKLNWExpUpperBound 200 288 (100001/100000) proofConfig = true := by native_decide
example : checkBKLNWExpLowerBound 200 288 (1) proofConfig = true := by native_decide

-- b = 250: instant proof (previously ~20 min)
example : checkBKLNWExpUpperBound 250 360 (100001/100000) proofConfig = true := by native_decide
example : checkBKLNWExpLowerBound 250 360 (1) proofConfig = true := by native_decide

-- b = 300: instant proof (previously ~30 min!)
example : checkBKLNWExpUpperBound 300 432 (100001/100000) proofConfig = true := by native_decide
example : checkBKLNWExpLowerBound 300 432 (1) proofConfig = true := by native_decide

/-! ### Floor lemmas for connecting to PNT+ definition -/

private lemma floor_100 : ⌊(100 : ℝ) / log 2⌋₊ = 144 := by
  rw [Nat.floor_eq_iff (by positivity : (0:ℝ) ≤ 100 / log 2)]
  constructor
  · rw [le_div_iff₀ (log_pos one_lt_two)]; interval_decide
  · rw [div_lt_iff₀ (log_pos one_lt_two)]; interval_decide

private lemma floor_150 : ⌊(150 : ℝ) / log 2⌋₊ = 216 := by
  rw [Nat.floor_eq_iff (by positivity : (0:ℝ) ≤ 150 / log 2)]
  constructor
  · rw [le_div_iff₀ (log_pos one_lt_two)]; interval_decide
  · rw [div_lt_iff₀ (log_pos one_lt_two)]; interval_decide

private lemma floor_200 : ⌊(200 : ℝ) / log 2⌋₊ = 288 := by
  rw [Nat.floor_eq_iff (by positivity : (0:ℝ) ≤ 200 / log 2)]
  constructor
  · rw [le_div_iff₀ (log_pos one_lt_two)]; interval_decide
  · rw [div_lt_iff₀ (log_pos one_lt_two)]; interval_decide

private lemma floor_250 : ⌊(250 : ℝ) / log 2⌋₊ = 360 := by
  rw [Nat.floor_eq_iff (by positivity : (0:ℝ) ≤ 250 / log 2)]
  constructor
  · rw [le_div_iff₀ (log_pos one_lt_two)]; interval_decide
  · rw [div_lt_iff₀ (log_pos one_lt_two)]; interval_decide

private lemma floor_300 : ⌊(300 : ℝ) / log 2⌋₊ = 432 := by
  rw [Nat.floor_eq_iff (by positivity : (0:ℝ) ≤ 300 / log 2)]
  constructor
  · rw [le_div_iff₀ (log_pos one_lt_two)]; interval_decide
  · rw [div_lt_iff₀ (log_pos one_lt_two)]; interval_decide

/-! ### Connection to PNT+ f definition

The PNT+ definition is:
  f(x) = Σ_{k=3}^{⌊log(x)/log(2)⌋} x^(1/k - 1/3)

Our bklnwF is the same but with explicit limit parameter:
  bklnwF x N = Σ_{k=3}^{N} x^(1/k - 1/3)

So: f(exp b) = bklnwF (exp b) ⌊b/log(2)⌋
-/

open LeanCert.Examples.BKLNW_a2_pow2 (f) in
theorem f_eq_bklnwF_exp (b : ℕ) :
    f (exp b) = bklnwF (exp b) ⌊(b : ℝ) / log 2⌋₊ := by
  unfold f bklnwF
  congr 1
  simp only [log_exp]

/-! ### Full theorem statements via bridge theorems

These theorems use `verify_bklnwF_exp_upper` and `verify_bklnwF_exp_lower` to produce
actual mathematical bounds on `bklnwF (exp b) limit`.

The pattern is:
1. The bridge theorem (e.g. `verify_bklnwF_exp_upper`) takes a proof that the certificate
   check returns true (proved by `native_decide`)
2. It produces a mathematical statement: `bklnwF (Real.exp b) limit ≤ target`
3. The proof term is O(1) size regardless of the sum length!

Note: These require the `expB_lo_pos` sorry to be filled in for complete soundness.
-/

-- b = 100: f(exp(100)) ≤ 1.0003 (instant proof)
theorem bklnwF_exp_100_upper :
    bklnwF (Real.exp 100) 144 ≤ (10003 / 10000 : ℚ) :=
  verify_bklnwF_exp_upper 100 144 (10003/10000) proofConfig (by decide) (by norm_num) (by native_decide)

-- b = 100: 1.0002 ≤ f(exp(100)) (instant proof)
theorem bklnwF_exp_100_lower :
    (10002 / 10000 : ℚ) ≤ bklnwF (Real.exp 100) 144 :=
  verify_bklnwF_exp_lower 100 144 (10002/10000) proofConfig (by decide) (by norm_num) (by native_decide)

-- b = 200: f(exp(200)) ≤ 1.00001 (instant proof)
theorem bklnwF_exp_200_upper :
    bklnwF (Real.exp 200) 288 ≤ (100001 / 100000 : ℚ) :=
  verify_bklnwF_exp_upper 200 288 (100001/100000) proofConfig (by decide) (by norm_num) (by native_decide)

-- b = 300: f(exp(300)) ≤ 1.00001 (instant proof - previously ~30 min!)
theorem bklnwF_exp_300_upper :
    bklnwF (Real.exp 300) 432 ≤ (100001 / 100000 : ℚ) :=
  verify_bklnwF_exp_upper 300 432 (100001/100000) proofConfig (by decide) (by norm_num) (by native_decide)

-- b = 300: 1 ≤ f(exp(300)) (instant proof)
theorem bklnwF_exp_300_lower :
    (1 : ℚ) ≤ bklnwF (Real.exp 300) 432 :=
  verify_bklnwF_exp_lower 300 432 1 proofConfig (by decide) (by norm_num) (by native_decide)

/-! ### Computational verification -/

-- Computational verification of the exact bounds from BKLNW_a2_exp.lean:
-- b=100: f(exp 100) ≈ 1.0002420
#eval
  let cfg := proofConfig
  let r := bklnwSumExpDyadic 100 144 cfg
  (r.toIntervalRat.lo, r.toIntervalRat.hi)

-- b=300: f(exp 300) ≈ 1.00000001937
#eval
  let cfg := proofConfig
  let r := bklnwSumExpDyadic 300 432 cfg
  (r.toIntervalRat.lo, r.toIntervalRat.hi)

end LeanCert.Examples.BKLNW_a2_reflective
