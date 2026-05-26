/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/

import LeanCert.Engine.ChebyshevPsi
import LeanCert.Engine.ChebyshevTheta

/-!
# Chebyshev certificate examples
-/

open Chebyshev (psi theta)
open LeanCert.Engine.ChebyshevPsi
open LeanCert.Engine.ChebyshevTheta

namespace LeanCert.Examples.Chebyshev

example :
    psi (10 : ℝ) ≤ (3 : ℝ) * 10 := by
  exact verify_psi_le_mul 10 20 3 (by native_decide)

example :
    ∀ N : Nat, 0 < N → N ≤ 20 →
      psi (N : ℝ) ≤ (3 : ℝ) * N := by
  exact verify_all_psi_le_mul 20 20 3 (by native_decide)

example :
    theta (10 : ℝ) ≤ (3 : ℝ) * 10 := by
  exact verify_theta_le_mul 10 20 3 (by native_decide)

example :
    ∀ N : Nat, 0 < N → 2 ≤ N → N ≤ 20 →
      |theta (N : ℝ) - N| ≤ ((9 / 10 : ℚ) : ℝ) * N := by
  exact verify_all_theta_rel_error 2 20 20 (9 / 10) (by native_decide)

end LeanCert.Examples.Chebyshev
