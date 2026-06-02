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

#check_supported (fun x : ℝ => x * x + Real.sin x)
#check_supported_inv (fun x : ℝ => (1 : ℝ) / (x + 1))
#check_continuous (fun x : ℝ => x * x + Real.exp x) on 0, 1

end LeanCert.Test.Support
