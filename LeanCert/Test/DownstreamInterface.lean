/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Tactic.IntervalAuto
import LeanCert.CertifiedBounds.Chebyshev
import LeanCert.Engine.TaylorModel
import LeanCert.CertifiedBounds.Li2
import LeanCert.CertifiedBounds.BKLNW
import LeanCert.ANT.PNTCompilers
import LeanCert.ANT.Asymp.Pointwise
import LeanCert.ANT.Asymp.Inequality
import LeanCert.API.Eval
import LeanCert.API.Backend
import LeanCert.API.Optimization
import LeanCert.API.Bounds
import LeanCert.API.MatrixPositivity

/-!
# Downstream interface guard

This file pins both the declarations referenced by PrimeNumberTheoremAnd and
the declared stable programmatic API. Removing or renaming any of them is a
breaking change: this file must fail to build before such a change can merge.

Regenerate the list against a PrimeNumberTheoremAnd checkout with:

  git grep -h -o -E 'LeanCert\.[A-Za-z0-9_.]+' -- 'PrimeNumberTheoremAnd/' | sort -u

This inventory cannot see unqualified declarations brought into scope with
`open`; the behavioral pattern suite must cover those downstream call shapes.
-/

-- Stable checked programmatic API
#check @LeanCert.evalInterval
#check @LeanCert.evalInterval_correct
#check @LeanCert.evalInterval1
#check @LeanCert.evalInterval1_correct
#check @LeanCert.Backend.Rational.eval
#check @LeanCert.Backend.Dyadic.eval
#check @LeanCert.Backend.Affine.eval
#check @LeanCert.globalMinimize
#check @LeanCert.globalMinimize_correct
#check @LeanCert.globalMaximize
#check @LeanCert.globalMaximize_correct
#check @LeanCert.API.Bounds.checkUpperBound
#check @LeanCert.API.Bounds.checkLowerBound
#check @LeanCert.API.Bounds.checkBounds
#check @LeanCert.API.Bounds.verifyUpperBound
#check @LeanCert.API.Bounds.verifyLowerBound
#check @LeanCert.API.Bounds.verifyBounds
#check @LeanCert.API.Bounds.BoundCheckOutcome
#check @LeanCert.API.Bounds.checkUpperBoundBox
#check @LeanCert.API.Bounds.checkLowerBoundBox
#check @LeanCert.API.Bounds.verifyUpperBoundBox
#check @LeanCert.API.Bounds.verifyLowerBoundBox
#check @LeanCert.Engine.matrixPSDCheck
#check @LeanCert.Engine.matrixPosDefCheck
#check @LeanCert.Validity.verify_matrix_posSemidef
#check @LeanCert.Validity.verify_matrix_posDef
#check @LeanCert.gramMatrix_posSemidef
#check @LeanCert.regularizedGramMatrix_posDef

-- Canonical certified Chebyshev API
#check @LeanCert.CertifiedBounds.Chebyshev.abs_theta_sub_le_mul_of_checkThetaRelErrorReal
#check @LeanCert.CertifiedBounds.Chebyshev.checkAllThetaRelErrorReal_implies
#check @LeanCert.CertifiedBounds.Chebyshev.checkAllPsiLeMulWith
#check @LeanCert.CertifiedBounds.Chebyshev.checkAllPsiLeMulWith_implies_checkPsiLeMulWith
#check @LeanCert.CertifiedBounds.Chebyshev.psi_le_of_checkPsiLeMulWith

-- Engine.TaylorModel and the lightweight canonical Li2 interface
#check @LeanCert.Engine.TaylorModel.symmetricLogCombination
#check @Li2.li2
#check @Li2.g_pos
#check @Li2.g_le_two
#check @LeanCert.CertifiedBounds.Li2.lower
#check @LeanCert.CertifiedBounds.Li2.upper

-- Canonical BKLNW bounds
#check @LeanCert.CertifiedBounds.BKLNW.f
#check @LeanCert.CertifiedBounds.BKLNW.pow29_upper
#check @LeanCert.CertifiedBounds.BKLNW.pow37_upper
#check @LeanCert.CertifiedBounds.BKLNW.pow44_upper
#check @LeanCert.CertifiedBounds.BKLNW.pow51_upper
#check @LeanCert.CertifiedBounds.BKLNW.pow58_upper
#check @LeanCert.CertifiedBounds.BKLNW.pow63_upper
#check @LeanCert.CertifiedBounds.BKLNW.pow145_upper
#check @LeanCert.CertifiedBounds.BKLNW.pow217_upper
#check @LeanCert.CertifiedBounds.BKLNW.pow289_upper
#check @LeanCert.CertifiedBounds.BKLNW.pow361_upper
#check @LeanCert.CertifiedBounds.BKLNW.pow433_upper

#check @LeanCert.CertifiedBounds.BKLNW.a2_20_exp_lower
#check @LeanCert.CertifiedBounds.BKLNW.a2_20_exp_upper
#check @LeanCert.CertifiedBounds.BKLNW.a2_25_exp_lower
#check @LeanCert.CertifiedBounds.BKLNW.a2_25_exp_upper
#check @LeanCert.CertifiedBounds.BKLNW.a2_30_exp_lower
#check @LeanCert.CertifiedBounds.BKLNW.a2_30_exp_upper
#check @LeanCert.CertifiedBounds.BKLNW.a2_35_exp_lower
#check @LeanCert.CertifiedBounds.BKLNW.a2_35_exp_upper
#check @LeanCert.CertifiedBounds.BKLNW.a2_40_exp_lower
#check @LeanCert.CertifiedBounds.BKLNW.a2_40_exp_upper
#check @LeanCert.CertifiedBounds.BKLNW.a2_43_exp_lower
#check @LeanCert.CertifiedBounds.BKLNW.a2_43_exp_upper
#check @LeanCert.CertifiedBounds.BKLNW.a2_100_exp_lower
#check @LeanCert.CertifiedBounds.BKLNW.a2_100_exp_upper
#check @LeanCert.CertifiedBounds.BKLNW.a2_150_exp_lower
#check @LeanCert.CertifiedBounds.BKLNW.a2_150_exp_upper
#check @LeanCert.CertifiedBounds.BKLNW.a2_200_exp_lower
#check @LeanCert.CertifiedBounds.BKLNW.a2_200_exp_upper
#check @LeanCert.CertifiedBounds.BKLNW.a2_250_exp_lower
#check @LeanCert.CertifiedBounds.BKLNW.a2_250_exp_upper
#check @LeanCert.CertifiedBounds.BKLNW.a2_300_exp_lower
#check @LeanCert.CertifiedBounds.BKLNW.a2_300_exp_upper
