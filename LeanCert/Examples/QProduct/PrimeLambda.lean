/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/

import LeanCert.QProduct

/-!
# Prime q-product examples
-/

open LeanCert.QProduct

example : primeFRat 3 = 7 / 12 := by
  native_decide

example : primeLambda ≤ ((7 / 12 : ℚ) : ℝ) := by
  exact verify_primeLambda_upper 3 (7 / 12) (by native_decide)

example : primeLambda ≤ ((133 / 240 : ℚ) : ℝ) := by
  exact verify_primeLambda_upper 7 (133 / 240) (by native_decide)

example : ((19 / 36 : ℚ) : ℝ) ≤ primeLambda := by
  exact primeLambda_lower_nineteen_thirtysix

example : (1 : ℝ) / 2 < primeLambda := by
  exact primeLambda_gt_half
