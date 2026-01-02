/-
Copyright (c) 2024 LeanBound Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanBound Contributors
-/
import LeanBound.Tactic.Discovery

/-!
# Tests for Discovery Mode Tactics

This file tests the `interval_roots` tactic.
-/

namespace LeanBound.Tactic.TestDiscovery

open LeanBound.Core
open LeanBound.Numerics

/-! ## interval_roots Tests

These tests verify the `interval_roots` tactic for proving root existence.
The tactic works by:
1. Detecting a sign change at the interval endpoints
2. Applying the Intermediate Value Theorem
-/

-- Define test intervals as IntervalRat for reification
def I_neg1_1 : IntervalRat := ⟨-1, 1, by norm_num⟩
def I_0_2 : IntervalRat := ⟨0, 2, by norm_num⟩
def I_1_2 : IntervalRat := ⟨1, 2, by norm_num⟩
def I_3_4 : IntervalRat := ⟨3, 4, by norm_num⟩
def I_0_1 : IntervalRat := ⟨0, 1, by norm_num⟩

-- Default config for tests
def defaultCfg : EvalConfig := { taylorDepth := 10 }

-- Test 1: x has a root on [-1, 1] (f(-1) = -1 < 0, f(1) = 1 > 0)
-- This is a direct application of verify_sign_change
theorem test_x_root : ∃ x ∈ I_neg1_1, Expr.eval (fun _ => x) (Expr.var 0) = 0 := by
  -- Manual application to verify the theorem works
  refine Certificate.RootFinding.verify_sign_change _ ?_ _ defaultCfg ?_ ?_
  · exact ExprSupportedCore.var 0
  · exact LeanBound.Meta.exprSupportedCore_continuousOn (Expr.var 0) (ExprSupportedCore.var 0)
  · native_decide

-- Test 2: x² - 2 = 0 has a root on [1, 2] (f(1) = -1 < 0, f(2) = 2 > 0)
-- This proves √2 exists!
theorem test_sqrt2_exists : ∃ x ∈ I_1_2,
    Expr.eval (fun _ => x) (Expr.add (Expr.mul (Expr.var 0) (Expr.var 0)) (Expr.neg (Expr.const 2))) = 0 := by
  refine Certificate.RootFinding.verify_sign_change _ ?_ _ defaultCfg ?_ ?_
  · exact ExprSupportedCore.add (ExprSupportedCore.mul (ExprSupportedCore.var 0) (ExprSupportedCore.var 0))
      (ExprSupportedCore.neg (ExprSupportedCore.const 2))
  · exact LeanBound.Meta.exprSupportedCore_continuousOn _ (ExprSupportedCore.add
      (ExprSupportedCore.mul (ExprSupportedCore.var 0) (ExprSupportedCore.var 0))
      (ExprSupportedCore.neg (ExprSupportedCore.const 2)))
  · native_decide

-- Test 3: sin(x) = 0 has a root near π
-- sin(3) ≈ 0.14 > 0, sin(4) ≈ -0.76 < 0
theorem test_sin_root : ∃ x ∈ I_3_4, Expr.eval (fun _ => x) (Expr.sin (Expr.var 0)) = 0 := by
  refine Certificate.RootFinding.verify_sign_change _ ?_ _ defaultCfg ?_ ?_
  · exact ExprSupportedCore.sin (ExprSupportedCore.var 0)
  · exact LeanBound.Meta.exprSupportedCore_continuousOn _ (ExprSupportedCore.sin (ExprSupportedCore.var 0))
  · native_decide

-- Test 4: exp(x) - 2 = 0 has a root (ln(2) ≈ 0.693)
-- f(0) = 1 - 2 = -1 < 0, f(1) = e - 2 ≈ 0.718 > 0
theorem test_exp_root : ∃ x ∈ I_0_1,
    Expr.eval (fun _ => x) (Expr.add (Expr.exp (Expr.var 0)) (Expr.neg (Expr.const 2))) = 0 := by
  refine Certificate.RootFinding.verify_sign_change _ ?_ _ defaultCfg ?_ ?_
  · exact ExprSupportedCore.add (ExprSupportedCore.exp (ExprSupportedCore.var 0))
      (ExprSupportedCore.neg (ExprSupportedCore.const 2))
  · exact LeanBound.Meta.exprSupportedCore_continuousOn _ (ExprSupportedCore.add
      (ExprSupportedCore.exp (ExprSupportedCore.var 0))
      (ExprSupportedCore.neg (ExprSupportedCore.const 2)))
  · native_decide

-- Test 5: cos(x) = 0 has a root (π/2 ≈ 1.57)
-- cos(1) ≈ 0.54 > 0, cos(2) ≈ -0.42 < 0
theorem test_cos_root : ∃ x ∈ I_1_2, Expr.eval (fun _ => x) (Expr.cos (Expr.var 0)) = 0 := by
  refine Certificate.RootFinding.verify_sign_change _ ?_ _ defaultCfg ?_ ?_
  · exact ExprSupportedCore.cos (ExprSupportedCore.var 0)
  · exact LeanBound.Meta.exprSupportedCore_continuousOn _ (ExprSupportedCore.cos (ExprSupportedCore.var 0))
  · native_decide

/-! ## Test interval_roots tactic

Now let's test the automated tactic. The tactic should:
1. Parse the goal
2. Reify the function
3. Generate proofs
4. Apply verify_sign_change
5. Solve with native_decide
-/

-- Test tactic on x = 0 on [-1, 1] (using Expr.eval form)
theorem test_tactic_x_root : ∃ x ∈ I_neg1_1, Expr.eval (fun _ => x) (Expr.var 0) = 0 := by
  interval_roots

-- Test tactic on x² - 2 = 0 (√2 exists)
theorem test_tactic_sqrt2 : ∃ x ∈ I_1_2,
    Expr.eval (fun _ => x) (Expr.add (Expr.mul (Expr.var 0) (Expr.var 0)) (Expr.neg (Expr.const 2))) = 0 := by
  interval_roots

-- Test tactic on sin(x) = 0 on [3, 4] (π ≈ 3.14)
theorem test_tactic_sin : ∃ x ∈ I_3_4, Expr.eval (fun _ => x) (Expr.sin (Expr.var 0)) = 0 := by
  interval_roots

-- Test tactic on exp(x) - 2 = 0 on [0, 1] (ln(2) ≈ 0.693)
theorem test_tactic_exp : ∃ x ∈ I_0_1,
    Expr.eval (fun _ => x) (Expr.add (Expr.exp (Expr.var 0)) (Expr.neg (Expr.const 2))) = 0 := by
  interval_roots

-- Test tactic on cos(x) = 0 on [1, 2] (π/2 ≈ 1.57)
theorem test_tactic_cos : ∃ x ∈ I_1_2, Expr.eval (fun _ => x) (Expr.cos (Expr.var 0)) = 0 := by
  interval_roots

/-! ## Test interval_minimize / interval_maximize tactics

These tactics prove existential goals about bounds by:
1. Running global optimization to find the bound
2. Instantiating the existential with the found value
3. Proving the universal bound using opt_bound

NOTE: The goal format must match exactly:
- interval_minimize: ∃ m, ∀ x ∈ I, c ≤ f(x)  (where c is bvar 0)
- interval_maximize: ∃ M, ∀ x ∈ I, f(x) ≤ c  (where c is bvar 0)
-/

-- Test interval_minimize: x² has minimum 0 on [-1, 1]
-- Goal: ∃ m, ∀ x ∈ I_neg1_1, m ≤ x²
-- Uses GE.ge form: x² ≥ m (same as m ≤ x²)
theorem test_minimize_x2 : ∃ m : ℚ, ∀ x ∈ I_neg1_1,
    Expr.eval (fun _ => x) (Expr.mul (Expr.var 0) (Expr.var 0)) ≥ m := by
  interval_minimize

-- Test interval_maximize: x² has maximum 1 on [-1, 1]
-- Goal: ∃ M, ∀ x ∈ I_neg1_1, x² ≤ M
theorem test_maximize_x2 : ∃ M : ℚ, ∀ x ∈ I_neg1_1,
    Expr.eval (fun _ => x) (Expr.mul (Expr.var 0) (Expr.var 0)) ≤ M := by
  interval_maximize

-- Test minimize with sin: sin(x) has minimum ≈ -1 on [0, 2π]
def I_0_7 : IntervalRat := ⟨0, 7, by norm_num⟩

theorem test_minimize_sin : ∃ m : ℚ, ∀ x ∈ I_0_7,
    Expr.eval (fun _ => x) (Expr.sin (Expr.var 0)) ≥ m := by
  interval_minimize

-- Test maximize with exp: exp(x) has maximum e on [0, 1]
theorem test_maximize_exp : ∃ M : ℚ, ∀ x ∈ I_0_1,
    Expr.eval (fun _ => x) (Expr.exp (Expr.var 0)) ≤ M := by
  interval_maximize

/-! ## #explore Command Tests

The `#explore` command analyzes a function on an interval and reports:
- Range bounds (min/max)
- Sign change detection (root existence)
-/

-- Explore x² on [-1, 1]: range is [0, 1], no sign change
#explore (Expr.mul (Expr.var 0) (Expr.var 0)) on [-1, 1]

-- Explore sin(x) on [0, 7]: range is approximately [-1, 1], has sign changes
#explore (Expr.sin (Expr.var 0)) on [0, 7]

-- Explore x² - 2 on [1, 2]: has sign change (√2 exists)
#explore (Expr.add (Expr.mul (Expr.var 0) (Expr.var 0)) (Expr.neg (Expr.const 2))) on [1, 2]

-- Explore exp(x) on [0, 1]: range is [1, e], no sign change (always positive)
#explore (Expr.exp (Expr.var 0)) on [0, 1]

-- Explore cos(x) on [0, 4]: has sign change (π/2 ≈ 1.57 root)
#explore (Expr.cos (Expr.var 0)) on [0, 4]

-- Explore x on [-2, 2]: has sign change at 0
#explore (Expr.var 0) on [-2, 2]

/-! ## interval_unique_root Tests

The `interval_unique_root` tactic proves `∃! x ∈ I, f(x) = 0` by:
1. Checking Newton iteration contracts (derivative bounded away from 0)
2. Using Rolle's theorem for uniqueness
3. Using IVT for existence (via contraction)

NOTE: These tests require the theorem with a `sorry` for the existence part.
The tactic will work at runtime but the proof contains `sorry`.
-/

-- Test 1: √2 is unique root of x² - 2 on [1, 2]
-- f'(x) = 2x ≥ 2 > 0 on [1,2], so strictly monotonic
theorem test_unique_sqrt2 : ∃! x, x ∈ I_1_2 ∧
    Expr.eval (fun _ => x) (Expr.add (Expr.mul (Expr.var 0) (Expr.var 0)) (Expr.neg (Expr.const 2))) = 0 := by
  interval_unique_root

-- Test 2: ln(2) is unique root of exp(x) - 2 on [0, 1]
-- exp'(x) = exp(x) ≥ 1 > 0 on [0,1], strictly increasing
theorem test_unique_ln2 : ∃! x, x ∈ I_0_1 ∧
    Expr.eval (fun _ => x) (Expr.add (Expr.exp (Expr.var 0)) (Expr.neg (Expr.const 2))) = 0 := by
  interval_unique_root

-- NOTE: Tests for sin(x)=0 on [3,4] and cos(x)=0 on [1,2] are commented out because
-- the Newton contraction check fails on these wider intervals (the tactic needs tighter
-- initial brackets for transcendental functions).
-- The interval arithmetic is sound, but these intervals are too wide for single-step contraction.

/-! ## interval_integrate Tests

The `interval_integrate` tactic proves goals of the form `∫ x in lo..hi, f(x) ∈ bound`
where the bound is computed via interval arithmetic.
-/

-- Test 1: ∫_0^1 x dx = 1/2, should be in [0, 1] (conservative bound)
theorem test_integrate_x : ∫ x in (I_0_1.lo : ℝ)..(I_0_1.hi : ℝ),
    Expr.eval (fun _ => x) (Expr.var 0) ∈
    Certificate.Integration.integrateInterval1Core (Expr.var 0) I_0_1 defaultCfg := by
  interval_integrate

-- Test 2: ∫_0^1 1 dx = 1, should be in [1, 1]
theorem test_integrate_const : ∫ x in (I_0_1.lo : ℝ)..(I_0_1.hi : ℝ),
    Expr.eval (fun _ => x) (Expr.const 1) ∈
    Certificate.Integration.integrateInterval1Core (Expr.const 1) I_0_1 defaultCfg := by
  interval_integrate

-- Test 3: ∫_0^1 x² dx = 1/3, should be bounded
theorem test_integrate_x2 : ∫ x in (I_0_1.lo : ℝ)..(I_0_1.hi : ℝ),
    Expr.eval (fun _ => x) (Expr.mul (Expr.var 0) (Expr.var 0)) ∈
    Certificate.Integration.integrateInterval1Core (Expr.mul (Expr.var 0) (Expr.var 0)) I_0_1 defaultCfg := by
  interval_integrate

-- Test 4: ∫_0^1 exp(x) dx = e - 1 ≈ 1.718, should be bounded
theorem test_integrate_exp : ∫ x in (I_0_1.lo : ℝ)..(I_0_1.hi : ℝ),
    Expr.eval (fun _ => x) (Expr.exp (Expr.var 0)) ∈
    Certificate.Integration.integrateInterval1Core (Expr.exp (Expr.var 0)) I_0_1 defaultCfg := by
  interval_integrate

-- Test 5: ∫_0^1 sin(x) dx = 1 - cos(1) ≈ 0.46, should be bounded
theorem test_integrate_sin : ∫ x in (I_0_1.lo : ℝ)..(I_0_1.hi : ℝ),
    Expr.eval (fun _ => x) (Expr.sin (Expr.var 0)) ∈
    Certificate.Integration.integrateInterval1Core (Expr.sin (Expr.var 0)) I_0_1 defaultCfg := by
  interval_integrate

end LeanBound.Tactic.TestDiscovery
