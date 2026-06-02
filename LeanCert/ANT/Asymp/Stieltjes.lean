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

/-- The discrete weight `1 / n`, with Lean's harmless convention `0⁻¹ = 0`. -/
noncomputable def oneOverNWeight (n : Nat) : ℝ :=
  ((n : ℝ)⁻¹)

/-- AST representation of the Stieltjes weight `1 / x`. -/
def oneOverNExpr : Expr :=
  Expr.inv (Expr.var 0)

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

@[simp] theorem oneOverNWeight_eq_evalAtNat (N : Nat) :
    oneOverNWeight N = evalAtNat oneOverNExpr N := by
  rfl

/-- Abel's identity specialized to the foundational ANT weight `1 / n`. -/
theorem weightedPrefixSumReal_oneOverN_eq_abelTransformOfPrefixReal
    (a : Nat → ℝ) (N : Nat) :
    weightedPrefixSumReal a oneOverNWeight N =
      abelTransformOfPrefixReal oneOverNWeight (prefixSum a) 0 (N + 1) := by
  exact weightedPrefixSumReal_eq_abelTransformOfPrefixReal a oneOverNWeight N

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
  /-- Error terms are genuine nonnegative envelope radii. -/
  error_nonneg :
    ∀ N, cutoff ≤ N → 0 ≤ evalAtNat errorTerm N

/-- Certified Stieltjes payload for the canonical ANT weight `1 / n`. -/
structure OneOverNStieltjesCert (A : AsympEnv) where
  /-- First endpoint from which the transformed envelope is valid. -/
  cutoff : Nat
  /-- The `1 / n` transform is intended for positive natural endpoints. -/
  cutoff_pos : 1 ≤ cutoff
  /-- Main term for `∑_{n ≤ N} a_n / n`. -/
  mainTerm : Expr
  /-- Error term for `∑_{n ≤ N} a_n / n`. -/
  errorTerm : Expr
  /-- Semantic certificate, supplied by a checker or direct proof. -/
  cert :
    ∀ N, cutoff ≤ N →
      |weightedPrefixSumReal A.seq oneOverNWeight N - evalAtNat mainTerm N| ≤
        evalAtNat errorTerm N
  /-- Error terms are genuine nonnegative envelope radii. -/
  error_nonneg :
    ∀ N, cutoff ≤ N → 0 ≤ evalAtNat errorTerm N

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
  error_nonneg := C.error_nonneg

end StieltjesCert

namespace OneOverNStieltjesCert

/-- Forget the `1 / n` specialization into the generic Stieltjes certificate. -/
noncomputable def toStieltjesCert {A : AsympEnv}
    (C : OneOverNStieltjesCert A) : StieltjesCert A where
  weight := oneOverNWeight
  cutoff := C.cutoff
  mainTerm := C.mainTerm
  errorTerm := C.errorTerm
  cert := C.cert
  error_nonneg := C.error_nonneg

/-- Convert a certified `1 / n` Stieltjes transform into an asymptotic envelope. -/
noncomputable def toAsympEnv {A : AsympEnv} (C : OneOverNStieltjesCert A) :
    AsympEnv :=
  C.toStieltjesCert.toAsympEnv

end OneOverNStieltjesCert

/-- Golden theorem for a certified Stieltjes-Abel transform payload. -/
theorem verify_stieltjes_envelope {A : AsympEnv} (C : StieltjesCert A) :
    ∀ N, C.cutoff ≤ N →
      |(C.toAsympEnv).summatory N - evalAtNat C.mainTerm N| ≤
        evalAtNat C.errorTerm N := by
  intro N hN
  exact C.toAsympEnv.cert N hN

/-- Golden theorem for the certified `1 / n` Stieltjes-Abel transform. -/
theorem verify_one_over_n_stieltjes_envelope {A : AsympEnv}
    (C : OneOverNStieltjesCert A) :
    ∀ N, C.cutoff ≤ N →
      |(C.toAsympEnv).summatory N - evalAtNat C.mainTerm N| ≤
        evalAtNat C.errorTerm N := by
  intro N hN
  exact C.toAsympEnv.cert N hN

end LeanCert.ANT.Asymp
