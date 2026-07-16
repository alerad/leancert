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
#check_continuous (fun x : ℝ => x * x + Real.exp x) on 0, 1

/- `ExprContinuousCore` is intentionally narrower than the full expression language:
it accepts constructors that are globally continuous, including named constants
and `erf`, but not partial-domain constructors such as `log` or `inv`. -/

#check_continuous (fun x : ℝ =>
  Real.sinh x + Real.cosh x + Real.tanh x + Real.erf x + Real.sqrt (x ^ 2)) on 0, 1

#check_continuous (fun x : ℝ => x + Real.pi + Real.eulerMascheroniConstant) on 0, 1

end LeanCert.Test.Support
