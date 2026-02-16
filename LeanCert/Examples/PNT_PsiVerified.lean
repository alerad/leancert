/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Engine.ChebyshevPsi
import LeanCert.Examples.PNT_PsiBounds

/-!
# Certified psi(N) <= 1.11 * N - Heavy Numerical Verification

This file proves via `native_decide` that
`checkAllPsiLeMulWith 11723 (111 / 100) 20 = true`,
confirming that `psiUB(N) <= 1.11 * N` for all `N = 1, ..., 11723`.

This fills the single sorry in `PNT_PsiBounds.lean`.

Compile-time note: this module is intended for CI verification.
Downstream users should import `PNT_PsiBounds.lean`.
-/

open LeanCert.Engine.ChebyshevPsi
open Chebyshev (psi)

namespace LeanCert.Examples.PNT_PsiVerified

/-- The incremental checker confirms `psi(N) <= 1.11 * N` for all `N = 1, ..., 11723`. -/
theorem allChecks_11723_slope111_100 : checkAllPsiLeMulWith 11723 (111 / 100) 20 = true := by native_decide

/-- Verified endpoint theorem mirroring the interface-level bound. -/
theorem psi_le_mul_11723_verified (x : Real) (hx : 0 < x) (hxb : x <= 11723) :
    psi x <= 111 / 100 * x := by
  rw [Chebyshev.psi_eq_psi_coe_floor x]
  have hnn : (0 : Real) <= x := le_of_lt hx
  have hfloor_le : Nat.floor x <= 11723 := Nat.floor_le_of_le hxb
  cases Nat.eq_zero_or_pos (Nat.floor x) with
  | inl hf =>
      have hpsi0 : psi (Nat.floor x : Real) = 0 := by
        simpa [hf, Nat.cast_zero] using Chebyshev.psi_eq_zero_of_lt_two (by norm_num : (0 : Real) < 2)
      have hmul_nonneg : (0 : Real) <= 111 / 100 * x := by positivity
      simpa [hpsi0] using hmul_nonneg
  | inr hf =>
      have hcheck : checkPsiLeMulWith (Nat.floor x) (111 / 100) 20 = true :=
        checkAllPsiLeMulWith_implies_checkPsiLeMulWith 11723 (111 / 100) 20 allChecks_11723_slope111_100
          (Nat.floor x) hf hfloor_le
      have h1rat := psi_le_of_checkPsiLeMulWith (Nat.floor x) 20 (111 / 100) hcheck
      have hcast : ((111 / 100 : ℚ) : ℝ) = 111 / 100 := by norm_num
      have h1 : psi (Nat.floor x : Real) <= 111 / 100 * Nat.floor x := by
        simpa [hcast] using h1rat
      calc
        psi (Nat.floor x : Real) <= 111 / 100 * Nat.floor x := h1
        _ <= 111 / 100 * x := by gcongr; exact Nat.floor_le hnn

/-! ### Consistency checks with lightweight interface -/

example : checkAllPsiLeMulWith 11723 (111 / 100) 20 = true :=
  LeanCert.Examples.PNT_PsiBounds.allChecks_11723_slope111_100

example (x : Real) (hx : 0 < x) (hxb : x <= 11723) :
    psi x <= 111 / 100 * x :=
  LeanCert.Examples.PNT_PsiBounds.psi_le_mul_11723 x hx hxb

example (x : Real) (hx : 0 < x) (hxb : x <= 11723) :
    psi x <= 111 / 100 * x :=
  psi_le_mul_11723_verified x hx hxb

end LeanCert.Examples.PNT_PsiVerified

