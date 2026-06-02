/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.ANT.Abel
import LeanCert.Core.Expr

/-!
# Certified asymptotic envelopes

This module introduces the semantic core of the Certified Asymptotic Envelope
Engine.  An `AsympEnv` packages an arithmetic sequence, a cutoff, a smooth
main term represented by `Core.Expr`, and a smooth error term represented by
`Core.Expr`.

The first layer is deliberately small: it proves envelope algebra directly from
the semantic certificate.  Later reflective checkers can target these semantic
combinators without increasing the trusted surface.
-/

namespace LeanCert.ANT.Asymp

open LeanCert.Core

/-- Evaluate a univariate expression at the natural number `N`. -/
noncomputable def evalAtNat (e : Expr) (N : Nat) : ℝ :=
  Expr.eval (fun _ => (N : ℝ)) e

/-- A certified asymptotic envelope for the summatory function of `seq`.

The certificate is indexed by natural endpoints:

`prefixSum seq (N + 1) = ∑ i < N + 1, seq i`,

so it represents the usual sum over `i ≤ N`.  Real-valued endpoints can be
reduced to this form later by flooring. -/
structure AsympEnv where
  /-- The semantic arithmetic sequence. -/
  seq : Nat → ℝ
  /-- The first endpoint from which the asymptotic certificate is valid. -/
  cutoff : Nat
  /-- Smooth main term as a LeanCert expression in variable 0. -/
  mainTerm : Expr
  /-- Smooth nonnegative error term as a LeanCert expression in variable 0. -/
  errorTerm : Expr
  /-- The semantic envelope certificate. -/
  cert :
    ∀ N, cutoff ≤ N →
      |prefixSum seq (N + 1) - evalAtNat mainTerm N| ≤ evalAtNat errorTerm N
  /-- Error terms are genuine nonnegative envelope radii. -/
  error_nonneg :
    ∀ N, cutoff ≤ N → 0 ≤ evalAtNat errorTerm N

namespace AsympEnv

/-- The summatory function represented by an envelope. -/
noncomputable def summatory (A : AsympEnv) (N : Nat) : ℝ :=
  prefixSum A.seq (N + 1)

/-- The summatory function at a real endpoint, interpreted by flooring. -/
noncomputable def summatoryReal (A : AsympEnv) (X : ℝ) : ℝ :=
  A.summatory ⌊X⌋₊

/-- Lower endpoint induced by an asymptotic envelope. -/
noncomputable def lower (A : AsympEnv) (N : Nat) : ℝ :=
  evalAtNat A.mainTerm N - evalAtNat A.errorTerm N

/-- Upper endpoint induced by an asymptotic envelope. -/
noncomputable def upper (A : AsympEnv) (N : Nat) : ℝ :=
  evalAtNat A.mainTerm N + evalAtNat A.errorTerm N

/-- Lower endpoint at a real argument, interpreted by flooring. -/
noncomputable def lowerReal (A : AsympEnv) (X : ℝ) : ℝ :=
  A.lower ⌊X⌋₊

/-- Upper endpoint at a real argument, interpreted by flooring. -/
noncomputable def upperReal (A : AsympEnv) (X : ℝ) : ℝ :=
  A.upper ⌊X⌋₊

@[simp] theorem evalAtNat_const (q : ℚ) (N : Nat) :
    evalAtNat (Expr.const q) N = (q : ℝ) := rfl

@[simp] theorem evalAtNat_add (e₁ e₂ : Expr) (N : Nat) :
    evalAtNat (Expr.add e₁ e₂) N = evalAtNat e₁ N + evalAtNat e₂ N := rfl

@[simp] theorem evalAtNat_mul (e₁ e₂ : Expr) (N : Nat) :
    evalAtNat (Expr.mul e₁ e₂) N = evalAtNat e₁ N * evalAtNat e₂ N := rfl

@[simp] theorem evalAtNat_neg (e : Expr) (N : Nat) :
    evalAtNat (Expr.neg e) N = -evalAtNat e N := rfl

theorem prefixSum_add (a b : Nat → ℝ) (n : Nat) :
    prefixSum (fun k => a k + b k) n = prefixSum a n + prefixSum b n := by
  simp [prefixSum, Finset.sum_add_distrib]

theorem prefixSum_neg (a : Nat → ℝ) (n : Nat) :
    prefixSum (fun k => -a k) n = -prefixSum a n := by
  simp [prefixSum]

theorem prefixSum_sub (a b : Nat → ℝ) (n : Nat) :
    prefixSum (fun k => a k - b k) n = prefixSum a n - prefixSum b n := by
  simp [sub_eq_add_neg, prefixSum_add, prefixSum_neg]

theorem prefixSum_const_mul (q : ℚ) (a : Nat → ℝ) (n : Nat) :
    prefixSum (fun k => (q : ℝ) * a k) n = (q : ℝ) * prefixSum a n := by
  simp [prefixSum, Finset.mul_sum]

/-- An envelope as a two-sided interval bound. -/
theorem lower_le_summatory (A : AsympEnv) (N : Nat) (hN : A.cutoff ≤ N) :
    A.lower N ≤ A.summatory N := by
  unfold lower summatory
  have h := A.cert N hN
  have hneg : -(evalAtNat A.errorTerm N) ≤
      prefixSum A.seq (N + 1) - evalAtNat A.mainTerm N :=
    neg_le_of_abs_le h
  linarith

/-- An envelope as a two-sided interval bound. -/
theorem summatory_le_upper (A : AsympEnv) (N : Nat) (hN : A.cutoff ≤ N) :
    A.summatory N ≤ A.upper N := by
  unfold upper summatory
  have h := A.cert N hN
  have hpos :
      prefixSum A.seq (N + 1) - evalAtNat A.mainTerm N ≤ evalAtNat A.errorTerm N :=
    le_of_abs_le h
  linarith

/-- Real-endpoint lower bound, reducing to the floored natural endpoint. -/
theorem lowerReal_le_summatoryReal (A : AsympEnv) (X : ℝ)
    (hX : A.cutoff ≤ ⌊X⌋₊) :
    A.lowerReal X ≤ A.summatoryReal X := by
  exact A.lower_le_summatory ⌊X⌋₊ hX

/-- Real-endpoint upper bound, reducing to the floored natural endpoint. -/
theorem summatoryReal_le_upperReal (A : AsympEnv) (X : ℝ)
    (hX : A.cutoff ≤ ⌊X⌋₊) :
    A.summatoryReal X ≤ A.upperReal X := by
  exact A.summatory_le_upper ⌊X⌋₊ hX

/-- Real-endpoint absolute-error certificate, reducing to the floored natural endpoint. -/
theorem certReal (A : AsympEnv) (X : ℝ) (hX : A.cutoff ≤ ⌊X⌋₊) :
    |A.summatoryReal X - evalAtNat A.mainTerm ⌊X⌋₊| ≤
      evalAtNat A.errorTerm ⌊X⌋₊ := by
  exact A.cert ⌊X⌋₊ hX

/-- If the current error term is pointwise bounded by a larger one, weaken the
envelope to that larger error term. -/
noncomputable def weakenError (A : AsympEnv) (newError : Expr)
    (hnew :
      ∀ N, A.cutoff ≤ N → evalAtNat A.errorTerm N ≤ evalAtNat newError N) :
    AsympEnv where
  seq := A.seq
  cutoff := A.cutoff
  mainTerm := A.mainTerm
  errorTerm := newError
  cert := by
    intro N hN
    exact (A.cert N hN).trans (hnew N hN)
  error_nonneg := by
    intro N hN
    exact (A.error_nonneg N hN).trans (hnew N hN)

/-- Raise the cutoff of an envelope. -/
noncomputable def shiftCutoff (A : AsympEnv) (newCutoff : Nat)
    (hcut : A.cutoff ≤ newCutoff) : AsympEnv where
  seq := A.seq
  cutoff := newCutoff
  mainTerm := A.mainTerm
  errorTerm := A.errorTerm
  cert := by
    intro N hN
    exact A.cert N (hcut.trans hN)
  error_nonneg := by
    intro N hN
    exact A.error_nonneg N (hcut.trans hN)

/-- Sum of two certified envelopes. -/
noncomputable def add (A B : AsympEnv) : AsympEnv where
  seq := fun n => A.seq n + B.seq n
  cutoff := max A.cutoff B.cutoff
  mainTerm := Expr.add A.mainTerm B.mainTerm
  errorTerm := Expr.add A.errorTerm B.errorTerm
  cert := by
    intro N hN
    have hAcut : A.cutoff ≤ N := (Nat.le_max_left A.cutoff B.cutoff).trans hN
    have hBcut : B.cutoff ≤ N := (Nat.le_max_right A.cutoff B.cutoff).trans hN
    have hA := A.cert N hAcut
    have hB := B.cert N hBcut
    calc
      |prefixSum (fun n => A.seq n + B.seq n) (N + 1)
          - evalAtNat (Expr.add A.mainTerm B.mainTerm) N|
          = |(prefixSum A.seq (N + 1) - evalAtNat A.mainTerm N)
              + (prefixSum B.seq (N + 1) - evalAtNat B.mainTerm N)| := by
              rw [prefixSum_add]
              simp
              ring_nf
      _ ≤ |prefixSum A.seq (N + 1) - evalAtNat A.mainTerm N|
            + |prefixSum B.seq (N + 1) - evalAtNat B.mainTerm N| := abs_add_le _ _
      _ ≤ evalAtNat A.errorTerm N + evalAtNat B.errorTerm N := add_le_add hA hB
      _ = evalAtNat (Expr.add A.errorTerm B.errorTerm) N := rfl
  error_nonneg := by
    intro N hN
    have hAcut : A.cutoff ≤ N := (Nat.le_max_left A.cutoff B.cutoff).trans hN
    have hBcut : B.cutoff ≤ N := (Nat.le_max_right A.cutoff B.cutoff).trans hN
    exact add_nonneg (A.error_nonneg N hAcut) (B.error_nonneg N hBcut)

/-- Negation of a certified envelope. -/
noncomputable def neg (A : AsympEnv) : AsympEnv where
  seq := fun n => -A.seq n
  cutoff := A.cutoff
  mainTerm := Expr.neg A.mainTerm
  errorTerm := A.errorTerm
  cert := by
    intro N hN
    calc
      |prefixSum (fun n => -A.seq n) (N + 1) - evalAtNat (Expr.neg A.mainTerm) N|
          = |prefixSum A.seq (N + 1) - evalAtNat A.mainTerm N| := by
              rw [prefixSum_neg]
              have hlin :
                  -prefixSum A.seq (N + 1) - -evalAtNat A.mainTerm N =
                    -(prefixSum A.seq (N + 1) - evalAtNat A.mainTerm N) := by
                ring
              calc
                |-prefixSum A.seq (N + 1) - -evalAtNat A.mainTerm N|
                    = |-(prefixSum A.seq (N + 1) - evalAtNat A.mainTerm N)| :=
                      congrArg abs hlin
                _ = |prefixSum A.seq (N + 1) - evalAtNat A.mainTerm N| := abs_neg _
      _ ≤ evalAtNat A.errorTerm N := A.cert N hN
  error_nonneg := by
    intro N hN
    exact A.error_nonneg N hN

/-- Difference of two certified envelopes. -/
noncomputable def sub (A B : AsympEnv) : AsympEnv :=
  add A (neg B)

/-- Rational scalar multiplication of a certified envelope. -/
noncomputable def constMul (q : ℚ) (A : AsympEnv) : AsympEnv where
  seq := fun n => (q : ℝ) * A.seq n
  cutoff := A.cutoff
  mainTerm := Expr.mul (Expr.const q) A.mainTerm
  errorTerm := Expr.mul (Expr.const |q|) A.errorTerm
  cert := by
    intro N hN
    have hA := A.cert N hN
    calc
      |prefixSum (fun n => (q : ℝ) * A.seq n) (N + 1)
          - evalAtNat (Expr.mul (Expr.const q) A.mainTerm) N|
          = |(q : ℝ) * (prefixSum A.seq (N + 1) - evalAtNat A.mainTerm N)| := by
              rw [prefixSum_const_mul]
              have hlin :
                  (q : ℝ) * prefixSum A.seq (N + 1) -
                      (q : ℝ) * evalAtNat A.mainTerm N =
                    (q : ℝ) * (prefixSum A.seq (N + 1) - evalAtNat A.mainTerm N) := by
                ring
              exact congrArg abs hlin
      _ = |(q : ℝ)| * |prefixSum A.seq (N + 1) - evalAtNat A.mainTerm N| := abs_mul _ _
      _ = ((|q| : ℚ) : ℝ) * |prefixSum A.seq (N + 1) - evalAtNat A.mainTerm N| := by
              rw [Rat.cast_abs]
      _ ≤ ((|q| : ℚ) : ℝ) * evalAtNat A.errorTerm N := by
              exact mul_le_mul_of_nonneg_left hA (by exact_mod_cast abs_nonneg q)
      _ = evalAtNat (Expr.mul (Expr.const |q|) A.errorTerm) N := rfl
  error_nonneg := by
    intro N hN
    have hq : 0 ≤ ((|q| : ℚ) : ℝ) := by
      exact_mod_cast abs_nonneg q
    simpa [evalAtNat] using mul_nonneg hq (A.error_nonneg N hN)

end AsympEnv

end LeanCert.ANT.Asymp
