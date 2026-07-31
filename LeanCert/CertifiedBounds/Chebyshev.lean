/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Engine.Chebyshev.Psi
import LeanCert.Engine.Chebyshev.Theta

/-!
# Certified Chebyshev checker bounds

Stable aliases for the checker-to-theorem APIs used by explicit-PNT projects.
The underlying verified implementations remain in `LeanCert.Engine`.
-/

namespace LeanCert.CertifiedBounds.Chebyshev

abbrev checkPsiLeMulWith (N : Nat) (slope : Rat) (depth : Nat := 20) : Bool :=
  LeanCert.Engine.Chebyshev.Psi.checkPsiLeMulWith N slope depth
abbrev checkAllPsiLeMulWith (bound : Nat) (slope : Rat) (depth : Nat := 20) : Bool :=
  LeanCert.Engine.Chebyshev.Psi.checkAllPsiLeMulWith bound slope depth
alias checkAllPsiLeMulWith_implies_checkPsiLeMulWith :=
  LeanCert.Engine.Chebyshev.Psi.checkAllPsiLeMulWith_implies_checkPsiLeMulWith
alias psi_le_of_checkPsiLeMulWith :=
  LeanCert.Engine.Chebyshev.Psi.psi_le_of_checkPsiLeMulWith

abbrev checkThetaRelError (N : Nat) (bound : Rat) (depth : Nat := 20) : Bool :=
  LeanCert.Engine.Chebyshev.Theta.checkThetaRelError N bound depth
abbrev checkThetaRelErrorReal (N : Nat) (bound : Rat) (depth : Nat := 20) : Bool :=
  LeanCert.Engine.Chebyshev.Theta.checkThetaRelErrorReal N bound depth
abbrev checkAllThetaRelErrorReal (start limit : Nat) (bound : Rat)
    (depth : Nat := 20) : Bool :=
  LeanCert.Engine.Chebyshev.Theta.checkAllThetaRelErrorReal start limit bound depth
alias checkAllThetaRelErrorReal_implies :=
  LeanCert.Engine.Chebyshev.Theta.checkAllThetaRelErrorReal_implies
alias abs_theta_sub_le_mul_of_checkThetaRelErrorReal :=
  LeanCert.Engine.Chebyshev.Theta.abs_theta_sub_le_mul_of_checkThetaRelErrorReal

end LeanCert.CertifiedBounds.Chebyshev
