/-
Copyright (c) 2024 LeanBound Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanBound Contributors
-/
import LeanBound

/-!
# Tests for Native Sqrt Support

This file tests the native sqrt implementation added to LeanBound v1.1.
It verifies:
1. Dyadic sqrt operations (intSqrt, sqrtDown, sqrtUp)
2. IntervalDyadic.sqrt with soundness
3. Expression evaluation with sqrt
4. Interval evaluation via the Dyadic backend
-/

namespace LeanBound.Test.SqrtTest

open LeanBound.Core
open LeanBound.Numerics

/-! ## Test 1: Integer Square Root -/

-- Test intSqrtNat basic values
#guard Dyadic.intSqrtNat 0 = 0
#guard Dyadic.intSqrtNat 1 = 1
#guard Dyadic.intSqrtNat 4 = 2
#guard Dyadic.intSqrtNat 9 = 3
#guard Dyadic.intSqrtNat 16 = 4
#guard Dyadic.intSqrtNat 100 = 10

-- Test floor behavior: sqrt(8) = 2 (since 2^2 = 4 ≤ 8 < 9 = 3^2)
#guard Dyadic.intSqrtNat 8 = 2
#guard Dyadic.intSqrtNat 15 = 3
#guard Dyadic.intSqrtNat 99 = 9

-- Test intSqrt for integers
#guard Dyadic.intSqrt 0 = 0
#guard Dyadic.intSqrt 4 = 2
#guard Dyadic.intSqrt 9 = 3
#guard Dyadic.intSqrt (-1) = 0  -- Negative returns 0

/-! ## Test 2: Dyadic sqrtDown and sqrtUp -/

-- For d = 4 (mantissa=4, exponent=0), sqrt = 2
-- sqrtDown(4, 0) should give mantissa close to 2
#guard (Dyadic.sqrtDown ⟨4, 0⟩ 0).mantissa ≥ 0
#guard (Dyadic.sqrtUp ⟨4, 0⟩ 0).mantissa ≥ 0

-- sqrtDown ≤ sqrtUp (monotonicity)
#guard (Dyadic.sqrtDown ⟨4, 0⟩ (-10)).toRat ≤ (Dyadic.sqrtUp ⟨4, 0⟩ (-10)).toRat
#guard (Dyadic.sqrtDown ⟨9, 0⟩ (-10)).toRat ≤ (Dyadic.sqrtUp ⟨9, 0⟩ (-10)).toRat
#guard (Dyadic.sqrtDown ⟨100, 0⟩ (-10)).toRat ≤ (Dyadic.sqrtUp ⟨100, 0⟩ (-10)).toRat

-- Negative mantissa returns zero
#guard (Dyadic.sqrtDown ⟨-4, 0⟩ 0).mantissa = 0
#guard (Dyadic.sqrtUp ⟨-4, 0⟩ 0).mantissa = 0

/-! ## Test 3: IntervalDyadic.sqrt -/

-- sqrt of [0, 4] should contain [0, 2] but we use conservative [0, max(4, 1)] = [0, 4]
def testInterval1 : IntervalDyadic :=
  ⟨⟨0, 0⟩, ⟨4, 0⟩, by native_decide⟩

def sqrtResult1 := IntervalDyadic.sqrt testInterval1

#guard sqrtResult1.lo.toRat = 0  -- Lower bound is 0
#guard sqrtResult1.hi.toRat ≥ 1  -- Upper bound is max(hi, 1) ≥ 1

-- sqrt of [1, 9] should give conservative bounds
def testInterval2 : IntervalDyadic :=
  ⟨⟨1, 0⟩, ⟨9, 0⟩, by native_decide⟩

def sqrtResult2 := IntervalDyadic.sqrt testInterval2

#guard sqrtResult2.lo.toRat = 0  -- Conservative lower bound
#guard sqrtResult2.hi.toRat = 9  -- max(9, 1) = 9

-- sqrt of interval with small values [0, 1/2]
def testInterval3 : IntervalDyadic :=
  ⟨⟨0, 0⟩, ⟨1, -1⟩, by native_decide⟩  -- [0, 0.5]

def sqrtResult3 := IntervalDyadic.sqrt testInterval3

#guard sqrtResult3.lo.toRat = 0
#guard sqrtResult3.hi.toRat = 1  -- max(0.5, 1) = 1

/-! ## Test 4: Expr.sqrt constructor and evaluation -/

-- sqrt is now a native constructor
def sqrtExpr : Expr := Expr.sqrt (Expr.const 4)
def sqrtExpr2 : Expr := Expr.sqrt (Expr.var 0)

-- freeVars works correctly
#guard sqrtExpr.freeVars = ∅
#guard sqrtExpr2.freeVars = {0}

-- usesOnlyVar0 works correctly
#guard sqrtExpr.usesOnlyVar0 = true
#guard sqrtExpr2.usesOnlyVar0 = true

-- Nested sqrt expressions
def nestedSqrt : Expr := Expr.sqrt (Expr.sqrt (Expr.const 16))
#guard nestedSqrt.freeVars = ∅

/-! ## Test 5: abs derived from sqrt -/

-- abs(x) = sqrt(x^2) is still a derived operation
def absExpr : Expr := Expr.abs (Expr.var 0)

-- Check it expands to sqrt(mul(var 0, var 0))
#guard (match absExpr with
  | Expr.sqrt (Expr.mul (Expr.var 0) (Expr.var 0)) => true
  | _ => false)

/-! ## Test 6: Interval evaluation with sqrt via Dyadic backend -/

-- Create a simple sqrt expression and evaluate it
def sqrtVarExpr : Expr := Expr.sqrt (Expr.var 0)

-- Interval [1, 4] for variable 0
def inputInterval : IntervalDyadic :=
  ⟨⟨1, 0⟩, ⟨4, 0⟩, by native_decide⟩

-- Convert to IntervalDyadicEnv
def testEnv : IntervalDyadicEnv := fun _ => inputInterval

-- Evaluate sqrt(x) on [1, 4]
def sqrtEvalResult := evalIntervalDyadic sqrtVarExpr testEnv

-- The result should be a valid interval (lo ≤ hi)
#guard sqrtEvalResult.lo.toRat ≤ sqrtEvalResult.hi.toRat

-- Lower bound should be 0 (conservative)
#guard sqrtEvalResult.lo.toRat = 0

-- Upper bound should be max(4, 1) = 4 (conservative)
#guard sqrtEvalResult.hi.toRat = 4

/-! ## Test 7: Composed expressions with sqrt -/

-- sqrt(x + 1) on [0, 3] should give bounds containing [1, 2]
def sqrtPlusOne : Expr := Expr.sqrt (Expr.add (Expr.var 0) (Expr.const 1))
def inputInterval2 : IntervalDyadic :=
  ⟨⟨0, 0⟩, ⟨3, 0⟩, by native_decide⟩
def testEnv2 : IntervalDyadicEnv := fun _ => inputInterval2

def composedResult := evalIntervalDyadic sqrtPlusOne testEnv2

-- Result should be a valid interval
#guard composedResult.lo.toRat ≤ composedResult.hi.toRat

/-! ## Test 8: Log interval evaluation -/

-- log is now hooked into the Dyadic evaluator with conservative bounds
def logExpr : Expr := Expr.log (Expr.var 0)

-- Interval [1, 10] for variable 0 (strictly positive)
def positiveInterval : IntervalDyadic :=
  ⟨⟨1, 0⟩, ⟨10, 0⟩, by native_decide⟩
def testEnv3 : IntervalDyadicEnv := fun _ => positiveInterval

def logEvalResult := evalIntervalDyadic logExpr testEnv3

-- Result should be a valid interval with conservative bounds [-100, 100]
#guard logEvalResult.lo.toRat ≤ logEvalResult.hi.toRat

/-! ## Test 9: Expression with both sqrt and other operations -/

-- f(x) = sqrt(x) * sin(x) on [1, 4]
def mixedExpr : Expr := Expr.mul (Expr.sqrt (Expr.var 0)) (Expr.sin (Expr.var 0))
def mixedResult := evalIntervalDyadic mixedExpr testEnv

-- Result should be valid
#guard mixedResult.lo.toRat ≤ mixedResult.hi.toRat

/-! ## Test 10: Soundness theorem availability -/

-- Verify that the soundness theorem is available (won't #guard, just type-check)
#check @IntervalDyadic.mem_sqrt

-- Verify eval_sqrt simp lemma exists
#check @Expr.eval_sqrt

-- Verify eval_abs theorem exists
#check @Expr.eval_abs

end LeanBound.Test.SqrtTest
