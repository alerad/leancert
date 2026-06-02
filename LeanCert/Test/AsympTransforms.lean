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
  error_nonneg := by
    intro N _hN
    simp [evalAtNat]

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
  error_nonneg := by
    intro N _hN
    simp [evalAtNat]

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
  cutoff_pos := by norm_num
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
  error_nonneg := by
    intro N _hN
    simp [evalAtNat]

example (N : Nat) (hN : 1 ≤ N) :
    |(deltaOneOverNCert.toAsympEnv).summatory N -
        evalAtNat deltaOneOverNCert.mainTerm N| ≤
      evalAtNat deltaOneOverNCert.errorTerm N := by
  exact verify_one_over_n_stieltjes_envelope deltaOneOverNCert N hN

noncomputable def deltaOneOverNAbelCert : OneOverNAbelCert deltaOneEnv where
  cutoff := 1
  cutoff_pos := by norm_num
  mainTerm := Expr.const 1
  errorTerm := Expr.const 0
  cert := by
    intro N hN
    rw [← weightedPrefixSumReal_oneOverN_eq_abelTransformOfPrefixReal deltaOneEnv.seq N]
    exact deltaOneOverNCert.cert N hN
  error_nonneg := by
    intro N _hN
    simp [evalAtNat]

example (N : Nat) (hN : 1 ≤ N) :
    |deltaOneOverNAbelCert.toAsympEnv.summatory N -
        evalAtNat deltaOneOverNAbelCert.mainTerm N| ≤
      evalAtNat deltaOneOverNAbelCert.errorTerm N := by
  exact verify_one_over_n_abel_envelope deltaOneOverNAbelCert N hN

def oneErr : Expr := Expr.const 1

def deltaOneAbelErrorLeOneDomination :
    ErrorDomination deltaOneOverNAbelCert.errorTerm oneErr where
  cutoff := 1
  cert := by
    intro N _hN
    simp [deltaOneOverNAbelCert, oneErr, evalAtNat]

example (N : Nat) (hN : 1 ≤ N) :
    |(deltaOneOverNAbelCert.toAsympEnvWithTargetError oneErr
        deltaOneAbelErrorLeOneDomination (Nat.le_refl 1)).summatory N -
        evalAtNat deltaOneOverNAbelCert.mainTerm N| ≤
      evalAtNat oneErr N := by
  exact verify_one_over_n_abel_envelope_with_target_error
    deltaOneOverNAbelCert oneErr deltaOneAbelErrorLeOneDomination
    (Nat.le_refl 1) N hN

def zeroErrLeOneSupport :
    ExprSupportedWithInv (Expr.sub deltaOneOverNCert.toStieltjesCert.errorTerm oneErr) := by
  unfold oneErr Expr.sub
  exact ExprSupportedWithInv.add
    (ExprSupportedWithInv.const 0)
    (ExprSupportedWithInv.neg (ExprSupportedWithInv.const 1))

def slab15 : IntervalRat := ⟨1, 5, by norm_num⟩

def deltaOneErrorSlabTail :
    SlabTailCert deltaOneOverNCert.toStieltjesCert.errorTerm oneErr where
  cutoff := 1
  tailStart := 5
  slabs := [slab15]
  coversSlabs := by
    intro N hcut htail
    refine ⟨slab15, by simp, ?_⟩
    simp [slab15]
    constructor
    · exact_mod_cast hcut
    · have hle5 : N ≤ 5 := (Nat.le_of_lt_succ htail).trans (by norm_num)
      exact_mod_cast hle5
  tailBound := by
    intro N _hN
    simp [evalAtNat, oneErr, deltaOneOverNCert, OneOverNStieltjesCert.toStieltjesCert]

example (N : Nat) (hN : 1 ≤ N) :
    evalAtNat deltaOneOverNCert.toStieltjesCert.errorTerm N ≤ evalAtNat oneErr N := by
  exact verify_stieltjes_error_le_target_with_slab_tail_dyadic
    deltaOneOverNCert.toStieltjesCert oneErr deltaOneErrorSlabTail (-53) 10
    zeroErrLeOneSupport (by norm_num)
    (by
      change checkExprLeOnSlabsDyadic (Expr.const 0) oneErr [slab15] (-53) 10 = true
      native_decide)
    N hN

noncomputable def deltaOneOverNWeakEnv : AsympEnv :=
  deltaOneOverNCert.toAsympEnv.weakenError oneErr (by
    intro N hN
    exact verify_stieltjes_error_le_target_with_slab_tail_dyadic
      deltaOneOverNCert.toStieltjesCert oneErr deltaOneErrorSlabTail (-53) 10
      zeroErrLeOneSupport (by norm_num)
      (by
        change checkExprLeOnSlabsDyadic (Expr.const 0) oneErr [slab15] (-53) 10 = true
        native_decide)
      N hN)

example (N : Nat) (hN : 1 ≤ N) :
    |deltaOneOverNWeakEnv.summatory N - evalAtNat deltaOneOverNWeakEnv.mainTerm N| ≤
      evalAtNat deltaOneOverNWeakEnv.errorTerm N := by
  exact deltaOneOverNWeakEnv.cert N hN

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
    prefixSum (discreteDerivative F) (N + 1) = F N := by
  exact prefixSum_discreteDerivative F N

noncomputable def zeroHyperbolaCert : HyperbolaCert zeroEnvT zeroEnvT where
  cutoff := 0
  mainTerm := Expr.const 0
  errorTerm := Expr.const 0
  cert := by
    intro N _hN
    simp [hyperbolaPairSum, zeroEnvT, evalAtNat]
  error_nonneg := by
    intro N _hN
    simp [evalAtNat]

noncomputable def zeroHyperbolaSplitCert : HyperbolaSplitCert zeroEnvT zeroEnvT where
  split := fun _ => 1
  cutoff := 0
  mainTerm := Expr.const 0
  errorTerm := Expr.const 0
  split_pos := by
    intro N _hN
    norm_num
  cert := by
    intro N _hN
    simp [hyperbolaLeft, hyperbolaBottom, hyperbolaOverlap, zeroEnvT, evalAtNat]
  error_nonneg := by
    intro N _hN
    simp [evalAtNat]

example (N : Nat) :
    |hyperbolaPairSum zeroEnvT.seq zeroEnvT.seq N -
        evalAtNat zeroHyperbolaSplitCert.mainTerm N| ≤
      evalAtNat zeroHyperbolaSplitCert.errorTerm N := by
  exact verify_dirichlet_hyperbola_split_envelope zeroHyperbolaSplitCert
    N (Nat.zero_le N)

def zeroHyperbolaSplitErrorLeOne :
    ErrorDomination zeroHyperbolaSplitCert.errorTerm oneErr where
  cutoff := 0
  cert := by
    intro N _hN
    simp [zeroHyperbolaSplitCert, oneErr, evalAtNat]

example (N : Nat) :
    |(zeroHyperbolaSplitCert.toAsympEnvWithTargetError oneErr
        zeroHyperbolaSplitErrorLeOne (Nat.le_refl 0)).summatory N -
        evalAtNat zeroHyperbolaSplitCert.mainTerm N| ≤
      evalAtNat oneErr N := by
  exact verify_dirichlet_hyperbola_split_envelope_with_target_error
    zeroHyperbolaSplitCert oneErr zeroHyperbolaSplitErrorLeOne
    (Nat.le_refl 0) N (Nat.zero_le N)

noncomputable def zeroConvolutionBridge :
    DirichletConvolutionBridge zeroEnvT zeroEnvT where
  convSeq := fun _ => 0
  summatory_eq_hyperbola := by
    intro N
    simp [prefixSum, hyperbolaPairSum, zeroEnvT]

example (N : Nat) :
    |zeroHyperbolaCert.toAsympEnv.summatory N -
        evalAtNat zeroHyperbolaCert.mainTerm N| ≤
      evalAtNat zeroHyperbolaCert.errorTerm N := by
  exact zeroHyperbolaCert.toAsympEnv.cert N (Nat.zero_le N)

example (N : Nat) :
    |(zeroConvolutionBridge.toAsympEnv zeroHyperbolaCert).summatory N -
        evalAtNat zeroHyperbolaCert.mainTerm N| ≤
      evalAtNat zeroHyperbolaCert.errorTerm N := by
  exact verify_dirichlet_convolution_envelope zeroConvolutionBridge zeroHyperbolaCert
    N (Nat.zero_le N)

example (N : Nat) :
    |(zeroConvolutionBridge.toAsympEnvFromSplit zeroHyperbolaSplitCert).summatory N -
        evalAtNat zeroHyperbolaSplitCert.mainTerm N| ≤
      evalAtNat zeroHyperbolaSplitCert.errorTerm N := by
  exact verify_dirichlet_convolution_split_envelope
    zeroConvolutionBridge zeroHyperbolaSplitCert N (Nat.zero_le N)

example (N : Nat) :
    |(zeroConvolutionBridge.toAsympEnvFromSplitWithTargetError
        zeroHyperbolaSplitCert oneErr zeroHyperbolaSplitErrorLeOne
        (Nat.le_refl 0)).summatory N -
        evalAtNat zeroHyperbolaSplitCert.mainTerm N| ≤
      evalAtNat oneErr N := by
  exact verify_dirichlet_convolution_split_envelope_with_target_error
    zeroConvolutionBridge zeroHyperbolaSplitCert oneErr zeroHyperbolaSplitErrorLeOne
    (Nat.le_refl 0) N (Nat.zero_le N)

end LeanCert.Test.AsympTransforms
