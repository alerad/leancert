/-
Tests for dyadic interval evaluation of sinc, arsinh, and transcendental compositions.
Verifies that `evalIntervalDyadic` produces correct enclosures for these functions.
-/
import LeanCert.Engine.IntervalEvalDyadic

open LeanCert.Core
open LeanCert.Engine

/-! ### Test intervals -/

/-- [0.5, 1.5] -/
def testI : IntervalRat := ⟨1/2, 3/2, by norm_num⟩
/-- [-2, 2] -/
def wideI : IntervalRat := ⟨-2, 2, by norm_num⟩
/-- [-0.1, 0.1] near zero -/
def nearZeroI : IntervalRat := ⟨-1/10, 1/10, by norm_num⟩
/-- [0, 0] singleton -/
def zeroI : IntervalRat := ⟨0, 0, by norm_num⟩

def toDyadic (I : IntervalRat) : IntervalDyadic := IntervalDyadic.ofIntervalRat I (-53)

def env (I : IntervalRat) : IntervalDyadicEnv := fun _ => toDyadic I

def cfg : DyadicConfig := {}

/-! ### sinc tests -/

-- sinc(x) on [0.5, 1.5]: should be within [-1, 1]
#eval do
  let r := evalIntervalDyadic (Expr.sinc (Expr.var 0)) (env testI) cfg
  IO.println s!"sinc([0.5, 1.5]): [{r.lo.toRat}, {r.hi.toRat}]"

-- sinc(x) on [-0.1, 0.1]: near-zero region, sinc(0) = 1
#eval do
  let r := evalIntervalDyadic (Expr.sinc (Expr.var 0)) (env nearZeroI) cfg
  IO.println s!"sinc([-0.1, 0.1]): [{r.lo.toRat}, {r.hi.toRat}]"

-- sinc(x) on [-2, 2]: wide interval
#eval do
  let r := evalIntervalDyadic (Expr.sinc (Expr.var 0)) (env wideI) cfg
  IO.println s!"sinc([-2, 2]): [{r.lo.toRat}, {r.hi.toRat}]"

/-! ### arsinh tests -/

-- arsinh(x) on [0.5, 1.5]
#eval do
  let r := evalIntervalDyadic (Expr.arsinh (Expr.var 0)) (env testI) cfg
  IO.println s!"arsinh([0.5, 1.5]): [{r.lo.toRat}, {r.hi.toRat}]"

-- arsinh(x) on [-2, 2]
#eval do
  let r := evalIntervalDyadic (Expr.arsinh (Expr.var 0)) (env wideI) cfg
  IO.println s!"arsinh([-2, 2]): [{r.lo.toRat}, {r.hi.toRat}]"

-- arsinh(0) = 0, so on [0, 0] should contain 0
#eval do
  let r := evalIntervalDyadic (Expr.arsinh (Expr.var 0)) (env zeroI) cfg
  IO.println s!"arsinh([0, 0]): [{r.lo.toRat}, {r.hi.toRat}]"

/-! ### Composition tests: sinc and arsinh with other functions -/

-- sin(arsinh(x)) on [0.5, 1.5]
#eval do
  let e := Expr.sin (Expr.arsinh (Expr.var 0))
  let r := evalIntervalDyadic e (env testI) cfg
  IO.println s!"sin(arsinh([0.5, 1.5])): [{r.lo.toRat}, {r.hi.toRat}]"

-- exp(sinc(x)) on [-2, 2]: sinc ∈ [-1,1] so exp(sinc) ∈ [1/e, e]
#eval do
  let e := Expr.exp (Expr.sinc (Expr.var 0))
  let r := evalIntervalDyadic e (env wideI) cfg
  IO.println s!"exp(sinc([-2, 2])): [{r.lo.toRat}, {r.hi.toRat}]"

-- arsinh(sin(x)) on [-2, 2]
#eval do
  let e := Expr.arsinh (Expr.sin (Expr.var 0))
  let r := evalIntervalDyadic e (env wideI) cfg
  IO.println s!"arsinh(sin([-2, 2])): [{r.lo.toRat}, {r.hi.toRat}]"

-- sinc(x) * arsinh(x) + cos(x) on [0.5, 1.5]
#eval do
  let e := Expr.add
    (Expr.mul (Expr.sinc (Expr.var 0)) (Expr.arsinh (Expr.var 0)))
    (Expr.cos (Expr.var 0))
  let r := evalIntervalDyadic e (env testI) cfg
  IO.println s!"sinc(x)*arsinh(x)+cos(x) on [0.5, 1.5]: [{r.lo.toRat}, {r.hi.toRat}]"
