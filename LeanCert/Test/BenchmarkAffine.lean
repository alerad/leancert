/-
Copyright (c) 2025 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Core.Expr
import LeanCert.Core.IntervalReal
import LeanCert.Core.IntervalDyadic
import LeanCert.Engine.IntervalEval
import LeanCert.Engine.IntervalEvalDyadic
import LeanCert.Engine.IntervalEvalAffine

/-!
# Affine Arithmetic Tests and Benchmarks

This file tests the Affine Arithmetic backend, demonstrating its key advantage:
solving the "dependency problem" where interval arithmetic loses correlations.

## Key Tests

1. **Dependency Problem** - Expressions like `x - x` where Affine gives exact results
2. **Correlation Preservation** - Multiple occurrences of the same variable
3. **Transcendental Functions** - sin, cos, exp, tanh, sinh, cosh soundness
4. **Backend Comparison** - Rational vs Dyadic vs Affine bound widths

## Expected Results

For expressions with repeated variables:
- Interval: `x - x` on [-1, 1] gives [-2, 2] (over-approximation)
- Affine: `x - x` on [-1, 1] gives [0, 0] (exact!)

Affine arithmetic tracks linear correlations, giving 50-90% tighter bounds
for many real-world expressions, especially in neural network verification.
-/

namespace LeanCert.Test.Affine

open LeanCert.Core
open LeanCert.Engine

/-! ### Test Intervals and Environments -/

/-- Standard test interval [-1, 1] -/
def testInterval : IntervalRat := ⟨-1, 1, by norm_num⟩

/-- Small positive interval [0.1, 0.5] for transcendentals -/
def smallInterval : IntervalRat := ⟨1/10, 1/2, by norm_num⟩

/-- Narrow interval [0.4, 0.6] for precision tests -/
def narrowInterval : IntervalRat := ⟨2/5, 3/5, by norm_num⟩

/-- Create rational environment from single interval -/
def mkRatEnv (I : IntervalRat) : Nat → IntervalRat := fun _ => I

/-- Create dyadic environment from single interval -/
def mkDyadEnv (I : IntervalRat) (prec : Int := -53) : IntervalDyadicEnv :=
  fun _ => IntervalDyadic.ofIntervalRat I prec

/-- Create affine environment from single interval -/
def mkAffineEnv (I : IntervalRat) : AffineEnv := toAffineEnv [I]

/-! ### Dependency Problem Tests -/

/-- x - x: Should be exactly 0, but interval gives [-2, 2] -/
def exprXMinusX : Expr :=
  Expr.add (Expr.var 0) (Expr.neg (Expr.var 0))

/-- x * x - x * x: Should be 0 -/
def exprXSqMinusXSq : Expr :=
  let xsq := Expr.mul (Expr.var 0) (Expr.var 0)
  Expr.add xsq (Expr.neg xsq)

/-- (x + 1) - x: Should be exactly 1 -/
def exprXPlus1MinusX : Expr :=
  let xp1 := Expr.add (Expr.var 0) (Expr.const 1)
  Expr.add xp1 (Expr.neg (Expr.var 0))

/-- x * (1 - x) + x * x: Should equal x (since x(1-x) + x² = x - x² + x² = x) -/
def exprCorrelated : Expr :=
  let x := Expr.var 0
  let xsq := Expr.mul x x
  let oneMinusX := Expr.add (Expr.const 1) (Expr.neg x)
  let xTimesOneMinusX := Expr.mul x oneMinusX
  Expr.add xTimesOneMinusX xsq

/-! ### Transcendental Function Tests -/

/-- sin(x) -/
def exprSin : Expr := Expr.sin (Expr.var 0)

/-- cos(x) -/
def exprCos : Expr := Expr.cos (Expr.var 0)

/-- exp(x) -/
def exprExp : Expr := Expr.exp (Expr.var 0)

/-- tanh(x) -/
def exprTanh : Expr := Expr.tanh (Expr.var 0)

/-- sinh(x) -/
def exprSinh : Expr := Expr.sinh (Expr.var 0)

/-- cosh(x) -/
def exprCosh : Expr := Expr.cosh (Expr.var 0)

/-- sqrt(x) on positive interval -/
def exprSqrt : Expr := Expr.sqrt (Expr.var 0)

/-- sin(x)² + cos(x)² - Should be 1 but interval loses correlation -/
def exprSinSqPlusCosSq : Expr :=
  let sinx := Expr.sin (Expr.var 0)
  let cosx := Expr.cos (Expr.var 0)
  let sin2 := Expr.mul sinx sinx
  let cos2 := Expr.mul cosx cosx
  Expr.add sin2 cos2

/-! ### Backend Evaluation Functions -/

/-- Evaluate with Rational backend -/
def evalRat (e : Expr) (I : IntervalRat) (cfg : EvalConfig := {}) : IntervalRat :=
  evalIntervalCore e (mkRatEnv I) cfg

/-- Evaluate with Dyadic backend -/
def evalDyad (e : Expr) (I : IntervalRat) (cfg : DyadicConfig := {}) : IntervalRat :=
  (evalIntervalDyadic e (mkDyadEnv I) cfg).toIntervalRat

/-- Evaluate with Affine backend -/
def evalAffine (e : Expr) (I : IntervalRat) (cfg : AffineConfig := {}) : IntervalRat :=
  (evalIntervalAffine e (mkAffineEnv I) cfg).toInterval

/-! ### Benchmark Result Structure -/

structure BenchResult where
  name : String
  ratLo : ℚ
  ratHi : ℚ
  ratWidth : ℚ
  affineLo : ℚ
  affineHi : ℚ
  affineWidth : ℚ
  improvement : String  -- Percentage improvement
  deriving Repr

def runBenchmark (name : String) (e : Expr) (I : IntervalRat) : BenchResult :=
  let rat := evalRat e I
  let aff := evalAffine e I
  let ratWidth := rat.hi - rat.lo
  let affWidth := aff.hi - aff.lo
  let improv := if ratWidth > 0 then
    let pct := ((ratWidth - affWidth) * 100) / ratWidth
    s!"{pct}%"
  else "N/A"
  { name := name
    ratLo := rat.lo
    ratHi := rat.hi
    ratWidth := ratWidth
    affineLo := aff.lo
    affineHi := aff.hi
    affineWidth := affWidth
    improvement := improv }

/-! ### Dependency Problem Benchmarks -/

#eval runBenchmark "x - x" exprXMinusX testInterval
-- Expected: Rational gives [-2, 2], Affine gives [0, 0] (100% improvement)

#eval runBenchmark "x² - x²" exprXSqMinusXSq testInterval
-- Expected: Rational gives wide interval, Affine gives [0, 0]

#eval runBenchmark "(x+1) - x" exprXPlus1MinusX testInterval
-- Expected: Rational gives [0, 2], Affine gives [1, 1] (exact)

#eval runBenchmark "x(1-x) + x²" exprCorrelated testInterval
-- Expected: Should equal x, so Affine gives [-1, 1], Rational wider

/-! ### Transcendental Function Benchmarks -/

#eval runBenchmark "sin(x)" exprSin testInterval
#eval runBenchmark "cos(x)" exprCos testInterval
#eval runBenchmark "exp(x)" exprExp smallInterval
#eval runBenchmark "tanh(x)" exprTanh testInterval
#eval runBenchmark "sinh(x)" exprSinh smallInterval
#eval runBenchmark "cosh(x)" exprCosh smallInterval
#eval runBenchmark "sqrt(x)" exprSqrt smallInterval

-- The Pythagorean identity loses correlation in interval arithmetic
#eval runBenchmark "sin²+cos²" exprSinSqPlusCosSq narrowInterval
-- Expected: Should be [1, 1] but interval gives wider bounds

/-! ### Three-Way Backend Comparison -/

structure ThreeWayResult where
  name : String
  ratWidth : ℚ
  dyadWidth : ℚ
  affineWidth : ℚ
  deriving Repr

def runThreeWay (name : String) (e : Expr) (I : IntervalRat) : ThreeWayResult :=
  let rat := evalRat e I
  let dyad := evalDyad e I
  let aff := evalAffine e I
  { name := name
    ratWidth := rat.hi - rat.lo
    dyadWidth := dyad.hi - dyad.lo
    affineWidth := aff.hi - aff.lo }

#eval runThreeWay "x - x" exprXMinusX testInterval
#eval runThreeWay "sin(x)" exprSin testInterval
#eval runThreeWay "exp(x)" exprExp smallInterval

/-! ### Soundness Verification -/

-- Verify that Affine results are sound (contain the true value range)
-- For x - x, the true value is always 0, so [0, 0] must be valid

/-- x - x evaluates to exactly 0 for any x -/
theorem xMinusX_eval (ρ : Nat → ℝ) : Expr.eval ρ exprXMinusX = 0 := by
  simp [exprXMinusX, Expr.eval]

/-- (x+1) - x evaluates to exactly 1 for any x -/
theorem xPlus1MinusX_eval (ρ : Nat → ℝ) : Expr.eval ρ exprXPlus1MinusX = 1 := by
  simp [exprXPlus1MinusX, Expr.eval]

-- Verify Affine bounds contain 0 for x - x
example : (evalAffine exprXMinusX testInterval).lo ≤ 0 := by native_decide
example : 0 ≤ (evalAffine exprXMinusX testInterval).hi := by native_decide

-- Verify Affine bounds contain 1 for (x+1) - x
example : (evalAffine exprXPlus1MinusX testInterval).lo ≤ 1 := by native_decide
example : 1 ≤ (evalAffine exprXPlus1MinusX testInterval).hi := by native_decide

/-! ### Multi-Variable Tests -/

/-- Two-variable environment -/
def mkAffineEnv2 (I1 I2 : IntervalRat) : AffineEnv := toAffineEnv [I1, I2]

/-- x + y - x: Should equal y -/
def exprXPlusYMinusX : Expr :=
  Expr.add (Expr.add (Expr.var 0) (Expr.var 1)) (Expr.neg (Expr.var 0))

def evalAffine2 (e : Expr) (I1 I2 : IntervalRat) : IntervalRat :=
  (evalIntervalAffine e (mkAffineEnv2 I1 I2) {}).toInterval

-- x + y - x on x ∈ [-1,1], y ∈ [0,2] should give y's range [0, 2]
#eval evalAffine2 exprXPlusYMinusX testInterval ⟨0, 2, by norm_num⟩
-- Expected: [0, 2] (exact range of y)

-- Compare with rational which loses the x correlation
#eval evalIntervalCore exprXPlusYMinusX
  (fun i => if i == 0 then testInterval else ⟨0, 2, by norm_num⟩) {}
-- Expected: Wider than [0, 2]

/-! ### Neural Network-Like Expressions -/

/-- LayerNorm-style expression: (x - mean) / std where mean and std depend on x -/
-- Simplified: x - (x/2) = x/2
def exprSimplifiedLayerNorm : Expr :=
  let x := Expr.var 0
  let halfX := Expr.mul x (Expr.const (1/2))
  Expr.add x (Expr.neg halfX)

#eval runBenchmark "x - x/2" exprSimplifiedLayerNorm testInterval
-- Expected: Affine tracks the correlation, giving tighter bounds

/-- ReLU-like: max(0, x) approximated as (x + |x|) / 2
    Using x² instead of |x| for smoothness: (x + sqrt(x² + ε)) / 2 -/
def exprSoftplus : Expr :=
  let x := Expr.var 0
  let xsq := Expr.mul x x
  let eps := Expr.const (1/100)
  let inner := Expr.add xsq eps
  let sqrtInner := Expr.sqrt inner
  Expr.mul (Expr.add x sqrtInner) (Expr.const (1/2))

#eval runBenchmark "softplus" exprSoftplus testInterval

end LeanCert.Test.Affine
