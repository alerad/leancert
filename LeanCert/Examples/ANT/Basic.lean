/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.ANT

/-!
# ANT certificate examples
-/

namespace LeanCert.Examples.ANT

open LeanCert.ANT

def toyStep : StepFn where
  value := fun n => (n : ℝ)
  lowerRat := fun n => (n : ℚ)
  upperRat := fun n => (n : ℚ)
  lower_correct := by intro n; norm_num
  upper_correct := by intro n; norm_num

example : ((6 : ℚ) : ℝ) ≤ stepSum toyStep 1 3 ∧ stepSum toyStep 1 3 ≤ ((6 : ℚ) : ℝ) := by
  exact verify_stepSum_interval toyStep 1 3 6 6 (by native_decide)

def toyA (n : Nat) : ℚ := if n = 1 then 2 else if n = 2 then 3 else 0
def toyF (n : Nat) : ℚ := n

example :
    ((8 : ℚ) : ℝ) ≤ (weightedSumRat toyA toyF 1 3 : ℝ) ∧
      (weightedSumRat toyA toyF 1 3 : ℝ) ≤ ((8 : ℚ) : ℝ) := by
  exact verify_abel_interval toyA toyF (by norm_num : 1 < 3) 8 8 (by native_decide)

example :
    ((1 / 4 : ℚ) : ℝ) ≤ finiteProduct ({2, 3} : Finset Nat) (fun n => (1 : ℝ) - 1 / n) ∧
      finiteProduct ({2, 3} : Finset Nat) (fun n => (1 : ℝ) - 1 / n) ≤
        ((1 / 3 : ℚ) : ℝ) := by
  apply verify_eulerProduct_interval
      ({2, 3} : Finset Nat) (fun n => (1 : ℝ) - 1 / n)
      (fun n => if n = 2 then (1 / 2 : ℚ) else if n = 3 then (2 / 3 : ℚ) else 0)
      (fun n => if n = 2 then (1 / 2 : ℚ) else if n = 3 then (2 / 3 : ℚ) else 1)
  · intro n hn
    fin_cases hn <;> norm_num
  · intro n hn
    fin_cases hn <;> norm_num
  · intro n hn
    fin_cases hn <;> norm_num
  · native_decide

example :
    ((0 : ℚ) : ℝ) ≤ mertensLogSum 5 ∧ mertensLogSum 5 ≤ ((3 : ℚ) : ℝ) := by
  exact verify_mertensLogSum_interval 5 20 0 3 (by native_decide)

end LeanCert.Examples.ANT
