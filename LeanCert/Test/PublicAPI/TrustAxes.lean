/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.API.Bounds
import LeanCert.Tactic

/-!
# Evaluation-backend and verification-route independence

Both theorems use the same public Dyadic-backed Boolean checker. Only the
tactic-side verification route changes.
-/

namespace LeanCert.Test.PublicAPI.TrustAxes

open LeanCert LeanCert.Core

def positive : IntervalRat := ⟨1, 2, by norm_num⟩
def logarithm : Expr := .log (.var 0)

set_option leancert.trust "kernel" in
theorem dyadicCheckKernelVerified :
    ∀ x ∈ positive, Expr.eval (fun _ => x) logarithm ≤ (1 : ℚ) := by
  apply API.Bounds.verifyUpperBound (precision := {})
  leancert_verify_cert

set_option leancert.trust "native" in
theorem dyadicCheckNativeVerified :
    ∀ x ∈ positive, Expr.eval (fun _ => x) logarithm ≤ (1 : ℚ) := by
  apply API.Bounds.verifyUpperBound (precision := {})
  leancert_verify_cert

#assert_trust kernel dyadicCheckKernelVerified
#assert_trust native dyadicCheckNativeVerified

end LeanCert.Test.PublicAPI.TrustAxes
