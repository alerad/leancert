module

/-
Test file for Phase 3 features:
1. Symbolic pre-pass with monotonicity
2. Epsilon-argmax interface
3. Range reduction for trig functions
-/
public import LeanCert.Engine.Optimization.BoundVerify
public import LeanCert.Tactic.IntervalAuto

public section

open LeanCert.Core
open LeanCert.Engine.Optimization
open Real Set

/-!
## Range Reduction Tests (Phase 2)

These tests verify that range reduction works for intervals far from 0.
Without range reduction, sin/cos on [10, 11] would have huge Taylor remainder bounds.
-/

-- sin bound on interval far from 0 - benefits from range reduction
example : ∀ x ∈ Icc (10 : ℝ) 11, sin x ≤ 1 := by
  interval_bound_adaptive

example : ∀ x ∈ Icc (10 : ℝ) 11, -1 ≤ sin x := by
  interval_bound_adaptive

-- cos bound on interval far from 0
example : ∀ x ∈ Icc (10 : ℝ) 11, cos x ≤ 1 := by
  interval_bound_adaptive

example : ∀ x ∈ Icc (10 : ℝ) 11, -1 ≤ cos x := by
  interval_bound_adaptive

-- Test on [100, 101] - even larger interval
example : ∀ x ∈ Icc (100 : ℝ) 101, sin x ≤ 1 := by
  interval_bound_adaptive

example : ∀ x ∈ Icc (100 : ℝ) 101, -1 ≤ sin x := by
  interval_bound_adaptive

/-!
## Monotonicity Pre-pass Tests (Phase 3)

These tests verify the monotonicity-based pruning is working.
-/

-- x^2 is monotone increasing on [0, 1], decreasing on [-1, 0]
-- With monotonicity enabled, the optimizer should find the minimum at x=0 quickly
#eval
  let e := Expr.mul (Expr.var 0) (Expr.var 0)  -- x^2
  let I : IntervalRat := ⟨0, 1, by norm_num⟩
  let cfg : BoundVerifyConfig := { useMonotonicity := true }
  let result := findMin1WithWitness e I cfg
  s!"x^2 on [0,1]: min={result.computedBound}, witness={result.witness.coords}, ε={result.epsilon}, iters={result.iterations}"

-- exp(x) is strictly increasing - with monotonicity, should converge fast
#eval
  let e := Expr.exp (Expr.var 0)
  let I : IntervalRat := ⟨-1, 1, by norm_num⟩
  let cfgWithMono : BoundVerifyConfig := { useMonotonicity := true }
  let cfgNoMono : BoundVerifyConfig := { useMonotonicity := false }
  let r1 := findMin1WithWitness e I cfgWithMono
  let r2 := findMin1WithWitness e I cfgNoMono
  s!"exp(x) min: with_mono={r1.iterations} iters, no_mono={r2.iterations} iters"

/-!
## Epsilon-Argmax Tests (Phase 3)

These tests verify the witness extraction functionality.
-/

-- Find argmax of sin(x) on [0, π] - should be near π/2
#eval
  let e := Expr.sin (Expr.var 0)
  let I : IntervalRat := ⟨0, 32/10, by norm_num⟩  -- [0, 3.2] approx [0, π]
  let cfg : BoundVerifyConfig := { tolerance := 1/100 }
  let result := findMax1WithWitness e I cfg
  s!"sin max on [0,3.2]: argmax≈{result.witness.coords}, max={result.computedBound}, ε={result.epsilon}"

-- Find argmin of x^2 + x on [-1, 1] - should be at x = -1/2
#eval
  let x := Expr.var 0
  let e := Expr.add (Expr.mul x x) x  -- x^2 + x
  let I : IntervalRat := ⟨-1, 1, by norm_num⟩
  let cfg : BoundVerifyConfig := { tolerance := 1/100 }
  let result := findMin1WithWitness e I cfg
  s!"x^2+x min on [-1,1]: argmin≈{result.witness.coords}, min={result.computedBound}, ε={result.epsilon}"

-- Multi-variable: find argmin of x^2 + y^2 on [-1,1]^2 - should be at (0, 0)
#eval
  let x := Expr.var 0
  let y := Expr.var 1
  let e := Expr.add (Expr.mul x x) (Expr.mul y y)  -- x^2 + y^2
  let B : Box := [⟨-1, 1, by norm_num⟩, ⟨-1, 1, by norm_num⟩]
  let cfg : BoundVerifyConfig := { tolerance := 1/100 }
  let result := findMinWithWitness e B cfg
  s!"x^2+y^2 min on [-1,1]^2: argmin≈{result.witness.coords}, min={result.computedBound}, ε={result.epsilon}"

/-!
## Verification with Witness Tests

These demonstrate verifying bounds and getting witness points.
-/

-- Verify sin(x) ≤ 1 and get the argmax
#eval
  let e := Expr.sin (Expr.var 0)
  let I : IntervalRat := ⟨0, 2, by norm_num⟩
  let result := verifyUpperBound1WithWitness e I 1
  s!"sin(x) ≤ 1 on [0,2]: verified={result.verified}, max_found={result.computedBound}, argmax≈{result.witness.coords}"

-- Verify exp(x) ≥ 1 for x ≥ 0 and get the argmin
#eval
  let e := Expr.exp (Expr.var 0)
  let I : IntervalRat := ⟨0, 1, by norm_num⟩
  let result := verifyLowerBound1WithWitness e I 1
  s!"exp(x) ≥ 1 on [0,1]: verified={result.verified}, min_found={result.computedBound}, argmin≈{result.witness.coords}"
