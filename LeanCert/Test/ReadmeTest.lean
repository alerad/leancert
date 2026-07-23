-- All imports at the very beginning
import LeanCert.Tactic.IntervalAuto
import LeanCert.Tactic.Discovery
import LeanCert.Validity.Bounds
import LeanCert.Discovery
import LeanCert.ML.Network
import LeanCert.Engine.IntervalEvalDyadic

/-
Copyright (c) 2024 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/

/-!
# README Examples Test

This file tests all code examples from the README to ensure they work.
-/

-- ============================================================================
-- Section: Tactics (README lines 34-55)
-- ============================================================================

open LeanCert.Core

-- Prove bounds on transcendentals using natural Set.Icc syntax
example : ∀ x ∈ Set.Icc (0 : ℝ) 1, Real.exp x ≤ 3 := by certify_bound 15
example : ∀ x ∈ Set.Icc (0 : ℝ) 1, Real.sin x ≤ 1 := by certify_bound
example : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ Real.exp x := by certify_bound

-- Or with explicit IntervalRat for more control
def I01 : IntervalRat := ⟨0, 1, by norm_num⟩
def I12 : IntervalRat := ⟨1, 2, by norm_num⟩

example : ∀ x ∈ I01, Real.exp x ≤ (3 : ℚ) := by certify_bound 15

-- Prove root existence (√2) via sign change
example : ∃ x ∈ I12, Expr.eval (fun _ => x)
    (Expr.add (Expr.mul (Expr.var 0) (Expr.var 0)) (Expr.neg (Expr.const 2))) = 0 := by
  interval_roots

-- ============================================================================
-- Section: Direct API (README lines 59-72)
-- ============================================================================

open LeanCert.Engine LeanCert.Validity

def I01' : IntervalRat := ⟨0, 1, by norm_num⟩
def exprExp : Expr := Expr.exp (Expr.var 0)
def exprExp_core : ExprSupportedCore exprExp :=
  ExprSupportedCore.exp (ExprSupportedCore.var 0)

-- Using the certificate API directly
theorem exp_bounded : ∀ x ∈ I01', Expr.eval (fun _ => x) exprExp ≤ (3 : ℚ) :=
  verify_upper_bound exprExp exprExp_core I01' 3 { taylorDepth := 10 } (by native_decide)

-- ============================================================================
-- Section: Discovery Commands (README lines 78-86)
-- ============================================================================

-- Find global minimum (interactive command - just test it compiles)
#find_min (fun x => x^2 + Real.sin x) on [-2, 2]

-- Explore function behavior (interactive command)
#explore (Expr.cos (Expr.var 0)) on [0, 4]

-- ============================================================================
-- Section: Neural Network (README lines 198-211)
-- ============================================================================

open LeanCert.ML

-- Define a 2-layer network
def net : TwoLayerNet := {
  layer1 := { weights := [[1, -1], [0, 1]], bias := [0, 0] }
  layer2 := { weights := [[1, 1]], bias := [0] }
}

-- Test that forwardInterval exists
#check TwoLayerNet.forwardInterval

-- ============================================================================
-- Section: Dyadic Backend (README lines 271-284)
-- ============================================================================

-- Define a test expression
def testExpr : Expr := Expr.exp (Expr.var 0)
def testEnv : IntervalDyadicEnv := fun _ => IntervalDyadic.ofIntervalRat I01' (-53)

-- Standard precision (53 bits, like IEEE double)
def result := LeanCert.Internal.Dyadic.evalUnchecked testExpr testEnv {}

-- Fast mode (30 bits, ~3x faster)
def fast := LeanCert.Internal.Dyadic.evalUnchecked testExpr testEnv DyadicConfig.fast

-- High precision (100 bits, tighter bounds)
def precise := LeanCert.Internal.Dyadic.evalUnchecked testExpr testEnv DyadicConfig.highPrecision

#check result
#check fast
#check precise

-- ============================================================================
-- All tests passed if this file compiles!
-- ============================================================================

#check "README examples all work!"
