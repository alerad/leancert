/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Engine.ChebyshevPsi
import LeanCert.Engine.ChebyshevTheta

/-!
# PrimeNumberTheoremAnd Chebyshev checker patterns

Reduced versions of the checker-to-theorem flows in `IEANTN/Chebyshev.lean`
and `IEANTN/Ramanujan/Ramanujan.lean`. The small ranges keep this regression
target cheap while protecting the same APIs and elaboration shapes.
-/

namespace LeanCert.Test.DownstreamPatterns.Chebyshev

open LeanCert.Engine.ChebyshevPsi
open LeanCert.Engine.ChebyshevTheta

private theorem psiChecks : checkAllPsiLeMulWith 5 2 20 = true := by
  native_decide

/-- Incremental ψ checker result specialized and converted to a real bound. -/
example : Chebyshev.psi (3 : ℝ) ≤ (2 : ℝ) * 3 := by
  have hpoint := checkAllPsiLeMulWith_implies_checkPsiLeMulWith
    5 2 20 psiChecks 3 (by omega) (by omega)
  exact psi_le_of_checkPsiLeMulWith 3 20 2 hpoint

private theorem thetaChecks : checkAllThetaRelErrorReal 3 5 (9 / 10) 20 = true := by
  native_decide

/-- Incremental θ checker result specialized to a downstream real interval. -/
example (x : ℝ) (hxlo : (3 : ℝ) ≤ x) (hxhi : x < (3 : ℝ) + 1) :
    |Chebyshev.theta x - x| ≤ (((9 : ℚ) / 10 : ℚ) : ℝ) * x := by
  have hpoint := checkAllThetaRelErrorReal_implies
    3 5 (9 / 10) 20 thetaChecks 3 (by omega) (by omega) (by omega)
  rw [if_pos (by omega : 3 < 5)] at hpoint
  exact abs_theta_sub_le_mul_of_checkThetaRelErrorReal
    3 20 (9 / 10) (by norm_num) (by norm_num) hpoint x hxlo hxhi

end LeanCert.Test.DownstreamPatterns.Chebyshev
