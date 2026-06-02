/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.ANT.Asymp

/-!
# Tests for CAEE Stieltjes and hyperbola kernels
-/

namespace LeanCert.Test.AsympTransforms

open LeanCert.ANT
open LeanCert.ANT.Asymp
open LeanCert.Core

noncomputable def deltaOne : Nat → ℝ :=
  fun n => if n = 1 then 1 else 0

noncomputable def oneWeight : Nat → ℝ :=
  fun _ => 1

example :
    weightedPrefixSumReal deltaOne oneWeight 3 = 1 := by
  simp [weightedPrefixSumReal, deltaOne, oneWeight]

example :
    weightedPrefixSumReal deltaOne oneWeight 3 =
      abelTransformOfPrefixReal oneWeight (prefixSum deltaOne) 0 4 := by
  exact weightedPrefixSumReal_eq_abelTransformOfPrefixReal deltaOne oneWeight 3

example : (hyperbolaPairs 3).card = 5 := by
  native_decide

example :
    hyperbolaPairSum (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ)) 5 =
      hyperbolaLeft (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ)) 5 2 +
        hyperbolaBottom (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ)) 5 (5 / 2) -
          hyperbolaOverlap (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ)) 5 2 (5 / 2) := by
  exact hyperbolaPairSum_eq_left_add_bottom_sub_overlap
    (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ)) 5 2 (by norm_num)

example (F : Nat → ℝ) (N : Nat) :
    prefixSum (fun n => F n - if n = 0 then 0 else F (n - 1)) (N + 1) = F N := by
  exact prefixSum_discreteDerivative F N

end LeanCert.Test.AsympTransforms
