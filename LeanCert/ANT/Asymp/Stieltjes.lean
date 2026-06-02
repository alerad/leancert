/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.ANT.Asymp.Env
import Mathlib.Algebra.BigOperators.Module

/-!
# Stieltjes-Abel envelope kernel

This file contains the exact finite summation-by-parts kernel used by the
Stieltjes side of CAEE.  The analytic checker layer should target the semantic
certificate wrapper at the bottom of the file.
-/

namespace LeanCert.ANT.Asymp

open scoped BigOperators
open LeanCert.Core

/-- Weighted sum over a half-open interval `[m, n)`. -/
noncomputable def weightedIntervalSumReal
    (a w : Nat → ℝ) (m n : Nat) : ℝ :=
  ∑ i ∈ Finset.Ico m n, w i * a i

/-- Weighted prefix sum over `i ≤ N`. -/
noncomputable def weightedPrefixSumReal
    (a w : Nat → ℝ) (N : Nat) : ℝ :=
  ∑ i ∈ Finset.range (N + 1), w i * a i

/-- Abel transform over an arbitrary real prefix function. -/
noncomputable def abelTransformOfPrefixReal
    (w : Nat → ℝ) (A : Nat → ℝ) (m n : Nat) : ℝ :=
  w (n - 1) * A n -
    w m * A m -
      ∑ i ∈ Finset.Ico m (n - 1),
        (w (i + 1) - w i) * A (i + 1)

/-- Weighted prefixes are ordinary prefixes of the pointwise weighted sequence. -/
theorem weightedPrefixSumReal_eq_prefixSum
    (a w : Nat → ℝ) (N : Nat) :
    weightedPrefixSumReal a w N =
      prefixSum (fun n => w n * a n) (N + 1) := by
  rfl

/-- Abel's finite summation-by-parts identity for real weights. -/
theorem weightedIntervalSumReal_eq_abelTransformOfPrefixReal
    {a w : Nat → ℝ} {m n : Nat} (hmn : m < n) :
    weightedIntervalSumReal a w m n =
      abelTransformOfPrefixReal w (prefixSum a) m n := by
  unfold weightedIntervalSumReal abelTransformOfPrefixReal
  have h := Finset.sum_Ico_by_parts (R := ℝ) (M := ℝ) w a hmn
  simpa [prefixSum, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using h

/-- Prefix version of Abel's identity, valid for `N + 1 > 0` by construction. -/
theorem weightedPrefixSumReal_eq_abelTransformOfPrefixReal
    (a w : Nat → ℝ) (N : Nat) :
    weightedPrefixSumReal a w N =
      abelTransformOfPrefixReal w (prefixSum a) 0 (N + 1) := by
  simpa [weightedPrefixSumReal, weightedIntervalSumReal, Nat.Ico_zero_eq_range] using
    (weightedIntervalSumReal_eq_abelTransformOfPrefixReal
      (a := a) (w := w) (m := 0) (n := N + 1) (Nat.succ_pos N))

/-- A certified Stieltjes transform payload for a fixed source envelope. -/
structure StieltjesCert (A : AsympEnv) where
  /-- The discrete weight `f(n)`. -/
  weight : Nat → ℝ
  /-- First endpoint from which the transformed envelope is valid. -/
  cutoff : Nat
  /-- Main term for the weighted summatory function. -/
  mainTerm : Expr
  /-- Error term for the weighted summatory function. -/
  errorTerm : Expr
  /-- Semantic certificate, supplied by a checker or direct proof. -/
  cert :
    ∀ N, cutoff ≤ N →
      |weightedPrefixSumReal A.seq weight N - evalAtNat mainTerm N| ≤
        evalAtNat errorTerm N

namespace StieltjesCert

/-- Convert a certified Stieltjes transform into a new asymptotic envelope. -/
noncomputable def toAsympEnv {A : AsympEnv} (C : StieltjesCert A) :
    AsympEnv where
  seq := fun n => C.weight n * A.seq n
  cutoff := C.cutoff
  mainTerm := C.mainTerm
  errorTerm := C.errorTerm
  cert := by
    intro N hN
    simpa [weightedPrefixSumReal_eq_prefixSum] using C.cert N hN

end StieltjesCert

/-- Golden theorem for a certified Stieltjes-Abel transform payload. -/
theorem verify_stieltjes_envelope {A : AsympEnv} (C : StieltjesCert A) :
    ∀ N, C.cutoff ≤ N →
      |(C.toAsympEnv).summatory N - evalAtNat C.mainTerm N| ≤
        evalAtNat C.errorTerm N := by
  intro N hN
  exact C.toAsympEnv.cert N hN

end LeanCert.ANT.Asymp
