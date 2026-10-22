/-
Copyright (c) 2024 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert

/-!
# Tests for Native Sqrt Support

This file tests the native sqrt implementation added to LeanCert v1.1.
It verifies:
1. Dyadic sqrt operations (intSqrt, sqrtDown, sqrtUp)
2. IntervalDyadic.sqrt with soundness
3. Expression evaluation with sqrt
4. Interval evaluation via the Dyadic backend
-/

namespace LeanCert.Test.SqrtTest

open LeanCert.Core
open LeanCert.Engine

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

-- Exact square endpoints: sqrt([0, 4]) = [0, 2]
def testInterval1 : IntervalDyadic :=
  ⟨⟨0, 0⟩, ⟨4, 0⟩, by native_decide⟩

def sqrtResult1 := IntervalDyadic.sqrt testInterval1

#guard sqrtResult1.lo.toRat = 0  -- Lower bound is 0
#guard sqrtResult1.hi.toRat = 2

-- Positive lower endpoints survive at sufficient precision
def testInterval2 : IntervalDyadic :=
  ⟨⟨1, 0⟩, ⟨9, 0⟩, by native_decide⟩

def sqrtResult2 := IntervalDyadic.sqrt testInterval2

#guard sqrtResult2.lo.toRat = 1
#guard sqrtResult2.hi.toRat = 3

-- sqrt of interval with small values [0, 1/2]
def testInterval3 : IntervalDyadic :=
  ⟨⟨0, 0⟩, ⟨1, -1⟩, by native_decide⟩  -- [0, 0.5]

def sqrtResult3 := IntervalDyadic.sqrt testInterval3

#guard sqrtResult3.lo.toRat = 0
#guard sqrtResult3.hi.toRat < 71 / 100

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
def sqrtEvalResult := LeanCert.Internal.Dyadic.evalUnchecked sqrtVarExpr testEnv

-- The result should be a valid interval (lo ≤ hi)
#guard sqrtEvalResult.lo.toRat ≤ sqrtEvalResult.hi.toRat

-- The evaluator consumes the tighter primitive
#guard sqrtEvalResult.lo.toRat = 1

#guard sqrtEvalResult.hi.toRat = 2

/-! ## Test 7: Composed expressions with sqrt -/

-- sqrt(x + 1) on [0, 3] should give bounds containing [1, 2]
def sqrtPlusOne : Expr := Expr.sqrt (Expr.add (Expr.var 0) (Expr.const 1))
def inputInterval2 : IntervalDyadic :=
  ⟨⟨0, 0⟩, ⟨3, 0⟩, by native_decide⟩
def testEnv2 : IntervalDyadicEnv := fun _ => inputInterval2

def composedResult := LeanCert.Internal.Dyadic.evalUnchecked sqrtPlusOne testEnv2

-- Result should be a valid interval
#guard composedResult.lo.toRat ≤ composedResult.hi.toRat

/-! ## Test 8: Log interval evaluation -/

-- log is now hooked into the Dyadic evaluator with conservative bounds
def logExpr : Expr := Expr.log (Expr.var 0)

-- Interval [1, 10] for variable 0 (strictly positive)
def positiveInterval : IntervalDyadic :=
  ⟨⟨1, 0⟩, ⟨10, 0⟩, by native_decide⟩
def testEnv3 : IntervalDyadicEnv := fun _ => positiveInterval

def logEvalResult := LeanCert.Internal.Dyadic.evalUnchecked logExpr testEnv3

-- Result should be a valid interval with conservative bounds [-100, 100]
#guard logEvalResult.lo.toRat ≤ logEvalResult.hi.toRat

/-! ## Test 9: Expression with both sqrt and other operations -/

-- f(x) = sqrt(x) * sin(x) on [1, 4]
def mixedExpr : Expr := Expr.mul (Expr.sqrt (Expr.var 0)) (Expr.sin (Expr.var 0))
def mixedResult := LeanCert.Internal.Dyadic.evalUnchecked mixedExpr testEnv

-- Result should be valid
#guard mixedResult.lo.toRat ≤ mixedResult.hi.toRat

/-! ## Test 10: Soundness theorem availability -/

-- Verify that the soundness theorem is available (won't #guard, just type-check)
#check @IntervalDyadic.mem_sqrt

-- Verify eval_sqrt simp lemma exists
#check @Expr.eval_sqrt

-- Verify eval_abs theorem exists
#check @Expr.eval_abs

/-! ## Test 11: Domain boundaries and precision

These `#guard` checks exercise executable endpoints. Generic real membership
and the production caller contracts are separately pinned in the trust manifest.
-/

private def ratInterval (lo hi : ℚ) (h : lo ≤ hi := by norm_num) : IntervalRat :=
  ⟨lo, hi, h⟩

#guard (IntervalRat.sqrtIntervalTightPrec (ratInterval (1/4) (1/4))).lo = 1/2
#guard (IntervalRat.sqrtIntervalTightPrec (ratInterval (1/4) (1/4))).hi = 1/2
#guard (IntervalRat.sqrtIntervalTightPrec (ratInterval (-4) (-1))).lo = 0
#guard (IntervalRat.sqrtIntervalTightPrec (ratInterval (-4) (-1))).hi = 0
#guard (IntervalRat.sqrtIntervalTightPrec (ratInterval (-1) 4)).lo = 0
#guard (IntervalRat.sqrtIntervalTightPrec (ratInterval (-1) 4)).hi = 2
#guard (IntervalRat.sqrtIntervalTightPrec (ratInterval 0 0)).hi = 0

private def ratTwo := ratInterval 2 2
#guard (IntervalRat.sqrtIntervalTightPrec ratTwo 16).hi -
    (IntervalRat.sqrtIntervalTightPrec ratTwo 16).lo <
  (IntervalRat.sqrtIntervalTightPrec ratTwo 8).hi -
    (IntervalRat.sqrtIntervalTightPrec ratTwo 8).lo

private def dyadicTwo := IntervalDyadic.singleton (LeanCert.Core.Dyadic.ofInt 2)
#guard (IntervalDyadic.sqrt dyadicTwo (-16)).hi.toRat -
    (IntervalDyadic.sqrt dyadicTwo (-16)).lo.toRat <
  (IntervalDyadic.sqrt dyadicTwo (-8)).hi.toRat -
    (IntervalDyadic.sqrt dyadicTwo (-8)).lo.toRat

private def dyadicQuarter := IntervalDyadic.singleton ⟨1, -2⟩
#guard (IntervalDyadic.sqrt dyadicQuarter (-16)).lo.toRat = 1/2
#guard (IntervalDyadic.sqrt dyadicQuarter (-16)).hi.toRat = 1/2
#guard (IntervalDyadic.sqrt (IntervalDyadic.singleton (LeanCert.Core.Dyadic.ofInt (-4)))).hi.toRat = 0
#guard (IntervalDyadic.sqrt (IntervalDyadic.singleton LeanCert.Core.Dyadic.zero)).hi.toRat = 0

-- Positive precision is handled by outward rounding to a coarser lattice.
#guard (IntervalDyadic.sqrt testInterval2 2).lo.toRat = 0
#guard (IntervalDyadic.sqrt testInterval2 2).hi.toRat = 4

-- Very small positive values can round down to zero at coarse precision.
private def tiny := IntervalDyadic.singleton ⟨1, -80⟩
#guard (IntervalDyadic.sqrt tiny (-53)).lo.toRat > 0
#guard (IntervalDyadic.sqrt tiny (-10)).lo.toRat = 0

-- The unrestricted real-membership contract is preserved, including prec > 0.
example {x : ℝ} {I : IntervalDyadic} (hx : x ∈ I) (prec : Int) :
    Real.sqrt x ∈ IntervalDyadic.sqrt I prec := IntervalDyadic.mem_sqrt' hx prec

/-! ## Test 12: The checked public evaluators return the tighter enclosure -/

private def checkedQuarter (backend : LeanCert.BackendChoice) : Bool :=
  match LeanCert.evalInterval (.sqrt (.var 0)) [ratInterval (1/4) (1/4)] { backend } with
  | .ok outcome => decide (outcome.interval.lo = 1/2 ∧ outcome.interval.hi = 1/2)
  | .error _ => false

#guard checkedQuarter .rational
#guard checkedQuarter .dyadic

end LeanCert.Test.SqrtTest
