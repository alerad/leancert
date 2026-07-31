/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Engine.Chebyshev.Psi
import LeanCert.Engine.Chebyshev.Theta

/-!
# Chebyshev Validity Exports

Stable Validity-layer import path for Chebyshev `ψ` and `θ` certificate bridge
theorems. Definitions remain in their engine modules.
-/

namespace LeanCert.Validity.Chebyshev

export LeanCert.Engine.Chebyshev.Psi
  ( verify_psi_le_mul
    verify_psi_le_mul_real
    verify_all_psi_le_mul
    verify_all_psi_le_mul_real )

export LeanCert.Engine.Chebyshev.Theta
  ( verify_theta_le_mul
    verify_theta_abs_error
    verify_theta_rel_error
    verify_theta_rel_error_real
    verify_all_theta_le_mul
    verify_all_theta_abs_error
    verify_all_theta_rel_error )

end LeanCert.Validity.Chebyshev
