/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Meta.ProveSupported
import LeanCert.Meta.ProveContinuous

/-!
# Support Proof Generator Tests

Smoke tests for automatic support and continuity proof generation.
-/

namespace LeanCert.Test.Support

open LeanCert.Core

#check_supported (fun x : ℝ => x * x + Real.sin x)
#check_supported_inv (fun x : ℝ => (1 : ℝ) / (x + 1))
#check_continuous (fun x : ℝ => x * x + Real.exp x) on 0, 1

/-! Regression coverage for the support-predicate capability boundaries.

`ExprSupportedWithInv` is the broad syntactic predicate used by strict interval
evaluators, so it should accept the constructors whose semantic side conditions
are checked later by evaluator/domain-validity code.
-/

#check_supported_inv (fun x : ℝ =>
  Real.sinh x + Real.cosh x + Real.tanh x + Real.log (x + 2) + 1 / (x + 3))

#check_supported_inv (fun x : ℝ =>
  Real.arctan x + Real.arsinh x + Real.atanh (x / 10) + Real.erf x + Real.sqrt (x + 1))

#check_supported_inv (fun x : ℝ => x + Real.pi + Real.eulerMascheroniConstant)

/- `ExprContinuousCore` is intentionally narrower than `ExprSupportedWithInv`:
it accepts constructors that are globally continuous, including named constants
and `erf`, but not partial-domain constructors such as `log` or `inv`. -/

#check_continuous (fun x : ℝ =>
  Real.sinh x + Real.cosh x + Real.tanh x + Real.erf x + Real.sqrt (x ^ 2)) on 0, 1

#check_continuous (fun x : ℝ => x + Real.pi + Real.eulerMascheroniConstant) on 0, 1

end LeanCert.Test.Support
