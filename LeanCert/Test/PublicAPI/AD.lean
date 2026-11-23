/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.API.AD

namespace LeanCert.Test.PublicAPI.AD

open LeanCert LeanCert.Core

private def unit : IntervalRat := ⟨0, 1, by norm_num⟩
private def crossesZero : IntervalRat := ⟨-1, 1, by norm_num⟩
private def identity : Expr := .var 0
private def nonlinear : Expr := .exp identity

private def derivativeBackend (expected : ConcreteBackend)
    (result : EvalResult DerivativeOutcome) : Bool :=
  match result with
  | .ok outcome => outcome.backend == expected
  | .error _ => false

private def gradientBackend (expected : ConcreteBackend)
    (result : EvalResult GradientOutcome) : Bool :=
  match result with
  | .ok outcome => outcome.backend == expected
  | .error _ => false

private def failed {α : Type} (result : EvalResult α) : Bool :=
  match result with
  | .ok _ => false
  | .error _ => true

#guard derivativeBackend .rational (evalWithDerivative identity [unit] 0)
#guard derivativeBackend .dyadic (evalWithDerivative nonlinear [unit] 0)
#guard derivativeBackend .rational
  (evalWithDerivative identity [unit] 0 { backend := .rational })
#guard derivativeBackend .dyadic
  (evalWithDerivative identity [unit] 0 { backend := .dyadic })
#guard derivativeBackend .rational
  (evalWithDerivative identity [unit] 0 { dyadicPrecision := -80 })
#guard gradientBackend .rational (evalGradient identity [unit])
#guard gradientBackend .dyadic (evalGradient nonlinear [unit])
#guard failed (evalWithDerivative identity [unit] 0 { backend := .affine })
#guard failed (evalWithDerivative (.inv identity) [crossesZero] 0)
#guard failed (evalGradient (.log identity) [crossesZero])
#guard failed (evalWithDerivative identity [unit] 0 {
  backend := .dyadic, dyadicPrecision := 1 })

#check evalWithDerivative_correct
#check evalGradient_correct

/-! Square-root support checks both the mathematical domain and rounded denominator. -/
private def positive : IntervalRat := ⟨1, 4, by norm_num⟩
private def root : Expr := .sqrt (.var 0)
private def quarter : IntervalRat := IntervalRat.singleton (1 / 4)
private def tiny : IntervalRat := IntervalRat.singleton (1 / 100000000)
private def tinyDyadic : IntervalRat := IntervalRat.singleton (1 / 16777216)

private def derivativeContains (q : ℚ) (result : EvalResult DerivativeOutcome) : Bool :=
  match result with
  | .ok outcome => decide (outcome.derivative.lo ≤ q ∧ q ≤ outcome.derivative.hi)
  | .error _ => false

#guard derivativeBackend .rational (evalWithDerivative root [positive] 0 { backend := .rational })
#guard derivativeBackend .dyadic (evalWithDerivative root [positive] 0 { backend := .dyadic })
#guard derivativeBackend .dyadic (evalWithDerivative root [positive] 0)
#guard derivativeContains 1 (evalWithDerivative root [quarter] 0 { backend := .rational })
#guard derivativeContains 1 (evalWithDerivative root [quarter] 0 { backend := .dyadic })
-- The true derivative 5000 exceeds the old unchecked placeholder coefficient 100.
#guard derivativeContains 5000 (evalWithDerivative root [tiny] 0 { backend := .rational })
#guard derivativeContains 5000 (evalWithDerivative root [tiny] 0 { backend := .dyadic })
#guard derivativeContains 2048 (evalWithDerivative root [tinyDyadic] 0
  { backend := .dyadic, dyadicPrecision := -40 })
#guard failed (evalWithDerivative root [unit] 0 { backend := .rational })
#guard failed (evalWithDerivative root [crossesZero] 0 { backend := .dyadic })
#guard failed (evalWithDerivative root [IntervalRat.singleton (-1)] 0)
#guard failed (evalWithDerivative root [tinyDyadic] 0
  { backend := .dyadic, dyadicPrecision := -4 })
-- Keep a precise input while coarsening the root output, isolating denominator rounding.
#guard (match LeanCert.Engine.evalWithDerivDyadicChecked root
    (fun _ => IntervalDyadic.ofIntervalRat tinyDyadic (-40)) 0
    { precision := -4 } with
  | .error (.sqrtLowerBoundZero _) => true
  | _ => false)
#guard (match evalWithDerivative (.log root) [crossesZero] 0 { backend := .rational } with
  | .error (.nestedFailure "logarithm operand" (.sqrtNonpositive _)) => true
  | _ => false)
#guard derivativeBackend .rational
  (evalWithDerivative (.sqrt (.inv (.add (.var 0) (.const 1)))) [positive] 0
    { backend := .rational })
#guard derivativeBackend .dyadic
  (evalWithDerivative (.sqrt (.inv (.add (.var 0) (.const 1)))) [positive] 0
    { backend := .dyadic })
#guard gradientBackend .rational
  (evalGradient (.sqrt (.add (.var 0) (.var 1))) [positive, positive] { backend := .rational })
#guard gradientBackend .dyadic
  (evalGradient (.sqrt (.add (.var 0) (.var 1))) [positive, positive] { backend := .dyadic })
#guard failed (evalWithDerivative root [positive] 0 { backend := .affine })

end LeanCert.Test.PublicAPI.AD
