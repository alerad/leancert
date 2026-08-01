/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.API.Integration

namespace LeanCert.Test.PublicAPI.Integration

open LeanCert LeanCert.Core

private def unit : IntervalRat := ⟨0, 1, by norm_num⟩
private def crossesZero : IntervalRat := ⟨-1, 1, by norm_num⟩
private def identity : Expr := .var 0

private def usedBackend (expected : ConcreteBackend)
    (result : EvalResult IntegralOutcome) : Bool :=
  match result with
  | .ok outcome => outcome.backend == expected
  | .error _ => false

private def failed (result : EvalResult IntegralOutcome) : Bool :=
  match result with
  | .ok _ => false
  | .error _ => true

private def reciprocalDomainFailure (result : EvalResult IntegralOutcome) : Bool :=
  match result with
  | .error (.nestedFailure "integration partition cell" (.reciprocalContainsZero _)) => true
  | _ => false

#guard usedBackend .rational (integrateUniform identity unit 8)
#guard usedBackend .rational
  (integrateUniform identity unit 8 { backend := .rational })
#guard usedBackend .rational
  (integrateUniform identity unit 8 { dyadicPrecision := -80 })
#guard usedBackend .dyadic
  (integrateUniform identity unit 8 { backend := .dyadic })
#guard failed (integrateUniform identity unit 8 { backend := .affine })
#guard failed (integrateUniform identity unit 0)
#guard failed (integrateUniform (.inv identity) crossesZero 8)
#guard reciprocalDomainFailure (integrateUniform (.inv identity) crossesZero 8)
#guard failed (integrateUniform identity unit 8 {
  backend := .dyadic, dyadicPrecision := 1 })

#check integrateUniform_correct

end LeanCert.Test.PublicAPI.Integration
