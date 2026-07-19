/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Tactic.IntervalAuto
import LeanCert.Engine.ChebyshevPsi
import LeanCert.Engine.ChebyshevTheta
import LeanCert.Engine.TaylorModel
import LeanCert.Examples.Li2Bounds
import LeanCert.Examples.BKLNW_a2_pow2
import LeanCert.Examples.BKLNW_a2_bounds
import LeanCert.ANT.PNTCompilers
import LeanCert.ANT.Asymp.Pointwise
import LeanCert.ANT.Asymp.Inequality

/-!
# Downstream interface guard

Every module imported here, and every declaration pinned below, is referenced
by name in PrimeNumberTheoremAnd. Removing or renaming any of them is a
breaking change for the pinned downstream release: this file must fail to
build before such a change can merge.

Regenerate the list against a PrimeNumberTheoremAnd checkout with:

  git grep -h -o -E 'LeanCert\.[A-Za-z0-9_.]+' -- 'PrimeNumberTheoremAnd/' | sort -u
-/

-- Engine.ChebyshevTheta
#check @LeanCert.Engine.ChebyshevTheta.abs_theta_sub_le_mul_of_checkThetaRelErrorReal
#check @LeanCert.Engine.ChebyshevTheta.checkAllThetaRelErrorReal_implies

-- Engine.ChebyshevPsi (used after opening the namespace downstream)
#check @LeanCert.Engine.ChebyshevPsi.checkAllPsiLeMulWith
#check @LeanCert.Engine.ChebyshevPsi.checkAllPsiLeMulWith_implies_checkPsiLeMulWith
#check @LeanCert.Engine.ChebyshevPsi.psi_le_of_checkPsiLeMulWith

-- Engine.TaylorModel and the lightweight Li2 interface
#check @LeanCert.Engine.TaylorModel.symmetricLogCombination
#check @Li2.li2
#check @Li2.g_pos
#check @Li2.g_le_two
#check @Li2.li2_lower
#check @Li2.li2_upper

-- Examples.BKLNW_a2_pow2
#check @LeanCert.Examples.BKLNW_a2_pow2.f
#check @LeanCert.Examples.BKLNW_a2_pow2.pow29_upper
#check @LeanCert.Examples.BKLNW_a2_pow2.pow37_upper
#check @LeanCert.Examples.BKLNW_a2_pow2.pow44_upper
#check @LeanCert.Examples.BKLNW_a2_pow2.pow51_upper
#check @LeanCert.Examples.BKLNW_a2_pow2.pow58_upper
#check @LeanCert.Examples.BKLNW_a2_pow2.pow63_upper
#check @LeanCert.Examples.BKLNW_a2_pow2.pow145_upper
#check @LeanCert.Examples.BKLNW_a2_pow2.pow217_upper
#check @LeanCert.Examples.BKLNW_a2_pow2.pow289_upper
#check @LeanCert.Examples.BKLNW_a2_pow2.pow361_upper
#check @LeanCert.Examples.BKLNW_a2_pow2.pow433_upper

-- Examples.BKLNW_a2_bounds
#check @LeanCert.Examples.BKLNW_a2_bounds.a2_20_exp_lower
#check @LeanCert.Examples.BKLNW_a2_bounds.a2_20_exp_upper
#check @LeanCert.Examples.BKLNW_a2_bounds.a2_25_exp_lower
#check @LeanCert.Examples.BKLNW_a2_bounds.a2_25_exp_upper
#check @LeanCert.Examples.BKLNW_a2_bounds.a2_30_exp_lower
#check @LeanCert.Examples.BKLNW_a2_bounds.a2_30_exp_upper
#check @LeanCert.Examples.BKLNW_a2_bounds.a2_35_exp_lower
#check @LeanCert.Examples.BKLNW_a2_bounds.a2_35_exp_upper
#check @LeanCert.Examples.BKLNW_a2_bounds.a2_40_exp_lower
#check @LeanCert.Examples.BKLNW_a2_bounds.a2_40_exp_upper
#check @LeanCert.Examples.BKLNW_a2_bounds.a2_43_exp_lower
#check @LeanCert.Examples.BKLNW_a2_bounds.a2_43_exp_upper
#check @LeanCert.Examples.BKLNW_a2_bounds.a2_100_exp_lower
#check @LeanCert.Examples.BKLNW_a2_bounds.a2_100_exp_upper
#check @LeanCert.Examples.BKLNW_a2_bounds.a2_150_exp_lower
#check @LeanCert.Examples.BKLNW_a2_bounds.a2_150_exp_upper
#check @LeanCert.Examples.BKLNW_a2_bounds.a2_200_exp_lower
#check @LeanCert.Examples.BKLNW_a2_bounds.a2_200_exp_upper
#check @LeanCert.Examples.BKLNW_a2_bounds.a2_250_exp_lower
#check @LeanCert.Examples.BKLNW_a2_bounds.a2_250_exp_upper
#check @LeanCert.Examples.BKLNW_a2_bounds.a2_300_exp_lower
#check @LeanCert.Examples.BKLNW_a2_bounds.a2_300_exp_upper
