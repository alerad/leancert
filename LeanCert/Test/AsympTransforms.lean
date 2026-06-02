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

noncomputable def zeroEnvT : AsympEnv where
  seq := fun _ => 0
  cutoff := 0
  mainTerm := Expr.const 0
  errorTerm := Expr.const 0
  cert := by
    intro N _hN
    simp [prefixSum, evalAtNat]

noncomputable def deltaOneEnv : AsympEnv where
  seq := deltaOne
  cutoff := 1
  mainTerm := Expr.const 1
  errorTerm := Expr.const 0
  cert := by
    intro N hN
    have hmem : 1 ∈ Finset.range (N + 1) := by
      simp
      exact hN
    have hsum : prefixSum deltaOne (N + 1) = 1 := by
      unfold prefixSum
      rw [Finset.sum_eq_single 1]
      · simp [deltaOne]
      · intro b hb hb1
        simp [deltaOne, hb1]
      · intro hnot
        exact False.elim (hnot hmem)
    simp [hsum, evalAtNat]

example :
    weightedPrefixSumReal deltaOne oneWeight 3 = 1 := by
  simp [weightedPrefixSumReal, deltaOne, oneWeight]

example :
    weightedPrefixSumReal deltaOne oneWeight 3 =
      abelTransformOfPrefixReal oneWeight (prefixSum deltaOne) 0 4 := by
  exact weightedPrefixSumReal_eq_abelTransformOfPrefixReal deltaOne oneWeight 3

example :
    weightedPrefixSumReal deltaOne oneOverNWeight 3 =
      abelTransformOfPrefixReal oneOverNWeight (prefixSum deltaOne) 0 4 := by
  exact weightedPrefixSumReal_oneOverN_eq_abelTransformOfPrefixReal deltaOne 3

noncomputable def deltaOneOverNCert : OneOverNStieltjesCert deltaOneEnv where
  cutoff := 1
  mainTerm := Expr.const 1
  errorTerm := Expr.const 0
  cert := by
    intro N hN
    have hmem : 1 ∈ Finset.range (N + 1) := by
      simp
      exact hN
    have hsum : weightedPrefixSumReal deltaOneEnv.seq oneOverNWeight N = 1 := by
      unfold weightedPrefixSumReal
      rw [Finset.sum_eq_single 1]
      · simp [deltaOneEnv, deltaOne, oneOverNWeight]
      · intro b hb hb1
        simp [deltaOneEnv, deltaOne, hb1]
      · intro hnot
        exact False.elim (hnot hmem)
    simp [hsum, evalAtNat]

example (N : Nat) (hN : 1 ≤ N) :
    |(deltaOneOverNCert.toAsympEnv).summatory N -
        evalAtNat deltaOneOverNCert.mainTerm N| ≤
      evalAtNat deltaOneOverNCert.errorTerm N := by
  exact verify_one_over_n_stieltjes_envelope deltaOneOverNCert N hN

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

noncomputable def zeroHyperbolaCert : HyperbolaCert zeroEnvT zeroEnvT where
  cutoff := 0
  mainTerm := Expr.const 0
  errorTerm := Expr.const 0
  cert := by
    intro N _hN
    simp [hyperbolaPairSum, zeroEnvT, evalAtNat]

noncomputable def zeroConvolutionBridge :
    DirichletConvolutionBridge zeroEnvT zeroEnvT where
  convSeq := fun _ => 0
  summatory_eq_hyperbola := by
    intro N
    simp [prefixSum, hyperbolaPairSum, zeroEnvT]

example (N : Nat) :
    |(zeroConvolutionBridge.toAsympEnv zeroHyperbolaCert).summatory N -
        evalAtNat zeroHyperbolaCert.mainTerm N| ≤
      evalAtNat zeroHyperbolaCert.errorTerm N := by
  exact verify_dirichlet_convolution_envelope zeroConvolutionBridge zeroHyperbolaCert
    N (Nat.zero_le N)

end LeanCert.Test.AsympTransforms
