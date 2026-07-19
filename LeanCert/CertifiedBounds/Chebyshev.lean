/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Engine.ChebyshevPsi
import LeanCert.Engine.ChebyshevTheta

/-!
# Certified Chebyshev checker bounds

Stable aliases for the checker-to-theorem APIs used by explicit-PNT projects.
The underlying verified implementations remain in `LeanCert.Engine`.
-/

namespace LeanCert.CertifiedBounds.Chebyshev

abbrev checkPsiLeMulWith (N : Nat) (slope : Rat) (depth : Nat := 20) : Bool :=
  LeanCert.Engine.ChebyshevPsi.checkPsiLeMulWith N slope depth
abbrev checkAllPsiLeMulWith (bound : Nat) (slope : Rat) (depth : Nat := 20) : Bool :=
  LeanCert.Engine.ChebyshevPsi.checkAllPsiLeMulWith bound slope depth
alias checkAllPsiLeMulWith_implies_checkPsiLeMulWith :=
  LeanCert.Engine.ChebyshevPsi.checkAllPsiLeMulWith_implies_checkPsiLeMulWith
alias psi_le_of_checkPsiLeMulWith :=
  LeanCert.Engine.ChebyshevPsi.psi_le_of_checkPsiLeMulWith

abbrev checkThetaRelError (N : Nat) (bound : Rat) (depth : Nat := 20) : Bool :=
  LeanCert.Engine.ChebyshevTheta.checkThetaRelError N bound depth
abbrev checkThetaRelErrorReal (N : Nat) (bound : Rat) (depth : Nat := 20) : Bool :=
  LeanCert.Engine.ChebyshevTheta.checkThetaRelErrorReal N bound depth
abbrev checkAllThetaRelErrorReal (start limit : Nat) (bound : Rat)
    (depth : Nat := 20) : Bool :=
  LeanCert.Engine.ChebyshevTheta.checkAllThetaRelErrorReal start limit bound depth
alias checkAllThetaRelErrorReal_implies :=
  LeanCert.Engine.ChebyshevTheta.checkAllThetaRelErrorReal_implies
alias abs_theta_sub_le_mul_of_checkThetaRelErrorReal :=
  LeanCert.Engine.ChebyshevTheta.abs_theta_sub_le_mul_of_checkThetaRelErrorReal

end LeanCert.CertifiedBounds.Chebyshev
