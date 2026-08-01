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

end LeanCert.Test.PublicAPI.AD
