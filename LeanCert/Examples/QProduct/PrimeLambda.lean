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

example : primeSandwichErrorRat 3 5 = 1 / 18 := by
  exact primeSandwichErrorRat_three_five

example : primeSandwichLowerRat 3 5 = 19 / 36 := by
  exact primeSandwichLowerRat_three_five

example : (primeSandwichLowerRat 3 5 : ℝ) ≤ primeLambda := by
  exact primeSandwichLowerRat_three_five_le_lambda

example :
    ((primeFRat 3 : ℝ) - (primeSandwichErrorRat 3 5 : ℝ) ≤ primeLambda ∧
      primeLambda ≤ (primeFRat 3 : ℝ)) := by
  apply primeLambda_sandwich (N := 3) (m := 5) (by norm_num) (by decide)
  intro p hp_prime hp_gt
  have hp_ge4 : 4 ≤ p := Nat.succ_le_of_lt hp_gt
  rcases Nat.lt_or_eq_of_le hp_ge4 with hp4 | hp4
  · exact Nat.succ_le_of_lt hp4
  · exfalso
    rw [← hp4] at hp_prime
    exact (by native_decide : ¬ Nat.Prime 4) hp_prime

example : ((19 / 36 : ℚ) : ℝ) ≤ primeLambda := by
  exact primeLambda_lower_nineteen_thirtysix

example : (1 : ℝ) / 2 < primeLambda := by
  exact primeLambda_gt_half

/-- The same two-sided enclosure through the directed-limit certificate:
one boolean check at truncation index 1 (`approx 1 = primeFRat 3`,
`tail 1 = primeSandwichErrorRat 3 5`), no tail hypothesis at the use site. -/
example : ((19 / 36 : ℚ) : ℝ) ≤ primeLambda ∧ primeLambda ≤ ((7 / 12 : ℚ) : ℝ) :=
  LeanCert.Validity.verify_limit_interval
    primeLambda_le_shiftedTrunc
    shiftedTrunc_sub_tail_le_primeLambda
    1 (19 / 36) (7 / 12)
    (by native_decide)
