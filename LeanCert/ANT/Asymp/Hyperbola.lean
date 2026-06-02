/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.ANT.Asymp.Env

/-!
# Dirichlet hyperbola envelope kernel

This file provides the exact finite pair-sum split underlying Dirichlet's
hyperbola method.  It works at the level of pairs `(i, j)` with `i * j ≤ N`;
arithmetic convolution presentations can later be connected to this semantic
kernel through divisor-pair equivalences.
-/

namespace LeanCert.ANT.Asymp

open scoped BigOperators
open LeanCert.Core

/-- Positive integer pairs under the hyperbola `i * j ≤ N`. -/
def hyperbolaPairs (N : Nat) : Finset (Nat × Nat) :=
  ((Finset.Icc 1 N).product (Finset.Icc 1 N)).filter
    (fun p : Nat × Nat => p.1 * p.2 ≤ N)

/-- Direct pair-sum form of a Dirichlet hyperbola summatory expression. -/
noncomputable def hyperbolaPairSum
    (a b : Nat → ℝ) (N : Nat) : ℝ :=
  ∑ p ∈ hyperbolaPairs N, a p.1 * b p.2

/-- Contribution from pairs with first coordinate at most `y`. -/
noncomputable def hyperbolaLeft
    (a b : Nat → ℝ) (N y : Nat) : ℝ :=
  ∑ p ∈ (hyperbolaPairs N).filter (fun p => p.1 ≤ y), a p.1 * b p.2

/-- Contribution from pairs with second coordinate at most `z`. -/
noncomputable def hyperbolaBottom
    (a b : Nat → ℝ) (N z : Nat) : ℝ :=
  ∑ p ∈ (hyperbolaPairs N).filter (fun p => p.2 ≤ z), a p.1 * b p.2

/-- Overlap rectangle of the two hyperbola cut regions. -/
noncomputable def hyperbolaOverlap
    (a b : Nat → ℝ) (N y z : Nat) : ℝ :=
  ∑ p ∈ (hyperbolaPairs N).filter (fun p => p.1 ≤ y ∧ p.2 ≤ z),
    a p.1 * b p.2

private theorem sum_filter_cover_sub_overlap
    {α : Type*} [DecidableEq α] (s : Finset α) (f : α → ℝ)
    (P Q : α → Prop) [DecidablePred P] [DecidablePred Q]
    (hcover : ∀ x ∈ s, P x ∨ Q x) :
    ∑ x ∈ s, f x =
      (∑ x ∈ s.filter P, f x) +
        (∑ x ∈ s.filter Q, f x) -
          (∑ x ∈ s.filter (fun x => P x ∧ Q x), f x) := by
  classical
  rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter]
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro x hx
  have hxcover := hcover x hx
  by_cases hP : P x
  · by_cases hQ : Q x <;> simp [hP, hQ]
  · by_cases hQ : Q x
    · simp [hP, hQ]
    · exact False.elim (hxcover.elim hP hQ)

private theorem hyperbola_cover
    {N y : Nat} (hy : 0 < y) :
    ∀ p ∈ hyperbolaPairs N, p.1 ≤ y ∨ p.2 ≤ N / y := by
  intro p hp
  by_cases hpy : p.1 ≤ y
  · exact Or.inl hpy
  · right
    have hy_le_p : y ≤ p.1 := Nat.le_of_lt (Nat.lt_of_not_ge hpy)
    have hp_mem := hp
    simp only [hyperbolaPairs, Finset.mem_filter] at hp_mem
    have hp_mul : p.1 * p.2 ≤ N := hp_mem.2
    have hmul_y : y * p.2 ≤ p.1 * p.2 := Nat.mul_le_mul_right p.2 hy_le_p
    have hmul : p.2 * y ≤ N := by
      calc
        p.2 * y = y * p.2 := by rw [Nat.mul_comm]
        _ ≤ p.1 * p.2 := hmul_y
        _ ≤ N := hp_mul
    exact (Nat.le_div_iff_mul_le hy).2 hmul

/-- Exact finite Dirichlet-hyperbola split with overlap subtraction. -/
theorem hyperbolaPairSum_eq_left_add_bottom_sub_overlap
    (a b : Nat → ℝ) (N y : Nat) (hy : 0 < y) :
    hyperbolaPairSum a b N =
      hyperbolaLeft a b N y +
        hyperbolaBottom a b N (N / y) -
          hyperbolaOverlap a b N y (N / y) := by
  unfold hyperbolaPairSum hyperbolaLeft hyperbolaBottom hyperbolaOverlap
  exact sum_filter_cover_sub_overlap
    (hyperbolaPairs N) (fun p => a p.1 * b p.2)
    (fun p => p.1 ≤ y) (fun p => p.2 ≤ N / y)
    (hyperbola_cover (N := N) (y := y) hy)

/-- Prefix sums of discrete increments telescope. -/
theorem prefixSum_discreteDerivative (F : Nat → ℝ) (N : Nat) :
    prefixSum (fun n => F n - if n = 0 then 0 else F (n - 1)) (N + 1) =
      F N := by
  induction N with
  | zero =>
      simp [prefixSum]
  | succ N ih =>
      unfold prefixSum at ih ⊢
      rw [Finset.sum_range_succ, ih]
      simp

/-- A certified hyperbola-transform payload. -/
structure HyperbolaCert (A B : AsympEnv) where
  /-- First endpoint from which the transformed envelope is valid. -/
  cutoff : Nat
  /-- Main term for the hyperbola pair summatory function. -/
  mainTerm : Expr
  /-- Error term for the hyperbola pair summatory function. -/
  errorTerm : Expr
  /-- Semantic certificate, supplied by a checker or direct proof. -/
  cert :
    ∀ N, cutoff ≤ N →
      |hyperbolaPairSum A.seq B.seq N - evalAtNat mainTerm N| ≤
        evalAtNat errorTerm N

/-- A bridge from a conventional Dirichlet-convolution sequence to the
hyperbola pair-summatory kernel.

The intended `convSeq` is `(a * b)(n)`.  The bridge certificate isolates the
finite divisor-pair identity

`∑_{n ≤ N} (a * b)(n) = ∑_{ij ≤ N} a(i)b(j)`,

so hyperbola envelope certificates can be reused without committing this file
to one particular divisor API. -/
structure DirichletConvolutionBridge (A B : AsympEnv) where
  /-- The conventional convolution sequence. -/
  convSeq : Nat → ℝ
  /-- The summatory convolution agrees with the hyperbola pair sum. -/
  summatory_eq_hyperbola :
    ∀ N, prefixSum convSeq (N + 1) = hyperbolaPairSum A.seq B.seq N

namespace HyperbolaCert

/-- Convert a certified hyperbola transform into an envelope whose `N`th
sequence value is the discrete increment of the pair-summatory function. -/
noncomputable def toAsympEnv {A B : AsympEnv} (C : HyperbolaCert A B) :
    AsympEnv where
  seq := fun n => hyperbolaPairSum A.seq B.seq n -
    if n = 0 then 0 else hyperbolaPairSum A.seq B.seq (n - 1)
  cutoff := C.cutoff
  mainTerm := C.mainTerm
  errorTerm := C.errorTerm
  cert := by
    intro N hN
    rw [prefixSum_discreteDerivative]
    exact C.cert N hN

end HyperbolaCert

namespace DirichletConvolutionBridge

/-- Lift a hyperbola pair-sum certificate to the conventional convolution
sequence supplied by the bridge. -/
noncomputable def toAsympEnv {A B : AsympEnv}
    (D : DirichletConvolutionBridge A B) (C : HyperbolaCert A B) :
    AsympEnv where
  seq := D.convSeq
  cutoff := C.cutoff
  mainTerm := C.mainTerm
  errorTerm := C.errorTerm
  cert := by
    intro N hN
    rw [D.summatory_eq_hyperbola]
    exact C.cert N hN

end DirichletConvolutionBridge

/-- Golden theorem for a certified Dirichlet-hyperbola payload. -/
theorem verify_dirichlet_hyperbola_envelope {A B : AsympEnv}
    (C : HyperbolaCert A B) :
    ∀ N, C.cutoff ≤ N →
      |hyperbolaPairSum A.seq B.seq N - evalAtNat C.mainTerm N| ≤
        evalAtNat C.errorTerm N := by
  intro N hN
  exact C.cert N hN

/-- Golden theorem for a conventional convolution sequence certified through
the hyperbola pair-sum kernel. -/
theorem verify_dirichlet_convolution_envelope {A B : AsympEnv}
    (D : DirichletConvolutionBridge A B) (C : HyperbolaCert A B) :
    ∀ N, C.cutoff ≤ N →
      |(D.toAsympEnv C).summatory N - evalAtNat C.mainTerm N| ≤
        evalAtNat C.errorTerm N := by
  intro N hN
  exact (D.toAsympEnv C).cert N hN

end LeanCert.ANT.Asymp
