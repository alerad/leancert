/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.ANT.Asymp.Stieltjes
import LeanCert.ANT.Asymp.Hyperbola
import LeanCert.Validity.DyadicBounds

/-!
# Dyadic checker layer for asymptotic envelope transforms

This module provides the first automatic checker layer for CAEE.  Generated
Stieltjes and hyperbola transforms typically produce residual/error expressions
and then need to prove one expression dominates another on a slab.  The checker
below certifies goals of the form

`∀ x ∈ [lo, hi], lhs(x) ≤ rhs(x)`

by checking `lhs - rhs ≤ 0` with the dyadic interval backend.
-/

namespace LeanCert.ANT.Asymp

open LeanCert.Core
open LeanCert.Engine

/-- Dyadic check for expression domination on one rational interval. -/
def checkExprLeOnIntervalDyadic
    (lhs rhs : Expr) (I : IntervalRat) (prec : Int) (depth : Nat) : Bool :=
  LeanCert.Validity.checkUpperBoundDyadicWithInv
    (Expr.sub lhs rhs) I.lo I.hi I.le 0 prec depth

/-- Dyadic check for expression domination on a list of rational slabs. -/
def checkExprLeOnSlabsDyadic
    (lhs rhs : Expr) (slabs : List IntervalRat) (prec : Int) (depth : Nat) : Bool :=
  slabs.all fun I => checkExprLeOnIntervalDyadic lhs rhs I prec depth

/-- Soundness-facing certificate for one dyadic domination check.

The raw Boolean checker is intentionally separate and computable; this package
records the support and precision hypotheses needed to use its golden theorem. -/
structure ExprLeOnIntervalDyadicCert
    (lhs rhs : Expr) (I : IntervalRat) (prec : Int) (depth : Nat) where
  supported : ExprSupportedWithInv (Expr.sub lhs rhs)
  prec_ok : prec ≤ 0
  checked : checkExprLeOnIntervalDyadic lhs rhs I prec depth = true

/-- Soundness-facing certificate for dyadic domination on a list of slabs. -/
structure ExprLeOnSlabsDyadicCert
    (lhs rhs : Expr) (slabs : List IntervalRat) (prec : Int) (depth : Nat) where
  supported : ExprSupportedWithInv (Expr.sub lhs rhs)
  prec_ok : prec ≤ 0
  checked : checkExprLeOnSlabsDyadic lhs rhs slabs prec depth = true

/-- A finite slab cover for natural endpoints starting at `cutoff`. -/
structure NatSlabCover where
  /-- First endpoint covered by the slab family. -/
  cutoff : Nat
  /-- Rational slabs checked by the dyadic backend. -/
  slabs : List IntervalRat
  /-- Every relevant natural endpoint lies in at least one slab. -/
  covers :
    ∀ N, cutoff ≤ N →
      ∃ I ∈ slabs, (N : ℝ) ∈ Set.Icc (I.lo : ℝ) I.hi

/-- A global domination certificate from finite slabs plus a tail proof.

This is the first CAEE coverage layer: numerical interval arithmetic handles a
finite initial range, while a symbolic/asymptotic tail proof handles every
endpoint from `tailStart` onward.  No relation between `cutoff` and
`tailStart` is required: if `tailStart ≤ cutoff`, the tail proof handles every
endpoint in the certificate's domain. -/
structure SlabTailCert (lhs rhs : Expr) where
  /-- First endpoint covered by the combined certificate. -/
  cutoff : Nat
  /-- First endpoint handled by the tail proof. -/
  tailStart : Nat
  /-- Rational slabs covering `cutoff ≤ N < tailStart`. -/
  slabs : List IntervalRat
  /-- Slab coverage for the finite pre-tail range. -/
  coversSlabs :
    ∀ N, cutoff ≤ N → N < tailStart →
      ∃ I ∈ slabs, (N : ℝ) ∈ Set.Icc (I.lo : ℝ) I.hi
  /-- Symbolic/asymptotic domination proof on the tail. -/
  tailBound :
    ∀ N, tailStart ≤ N → evalAtNat lhs N ≤ evalAtNat rhs N

namespace SlabTailCert

/-- Every endpoint in the certificate domain is either covered by a pre-tail
slab or handled by the tail proof. -/
theorem covered_or_tail {lhs rhs : Expr} (cert : SlabTailCert lhs rhs)
    (N : Nat) (hN : cert.cutoff ≤ N) :
    (∃ I ∈ cert.slabs, (N : ℝ) ∈ Set.Icc (I.lo : ℝ) I.hi) ∨ cert.tailStart ≤ N := by
  by_cases htail : cert.tailStart ≤ N
  · exact Or.inr htail
  · have hpre : N < cert.tailStart := Nat.lt_of_not_ge htail
    exact Or.inl (cert.coversSlabs N hN hpre)

end SlabTailCert

/-- Golden theorem for dyadic expression domination on one slab. -/
theorem verify_expr_le_on_interval_dyadic
    (lhs rhs : Expr) (I : IntervalRat) (prec : Int) (depth : Nat)
    (hsupp : ExprSupportedWithInv (Expr.sub lhs rhs))
    (hprec : prec ≤ 0)
    (hcheck : checkExprLeOnIntervalDyadic lhs rhs I prec depth = true) :
    ∀ x ∈ Set.Icc (I.lo : ℝ) I.hi,
      Expr.eval (fun _ => x) lhs ≤ Expr.eval (fun _ => x) rhs := by
  intro x hx
  have h :=
    LeanCert.Validity.verify_upper_bound_dyadic_withInv
      (Expr.sub lhs rhs) hsupp I.lo I.hi I.le 0 prec depth hprec hcheck x hx
  simp [Expr.sub] at h
  linarith

/-- Verify a packaged one-slab dyadic domination certificate. -/
theorem ExprLeOnIntervalDyadicCert.verify
    {lhs rhs : Expr} {I : IntervalRat} {prec : Int} {depth : Nat}
    (cert : ExprLeOnIntervalDyadicCert lhs rhs I prec depth) :
    ∀ x ∈ Set.Icc (I.lo : ℝ) I.hi,
      Expr.eval (fun _ => x) lhs ≤ Expr.eval (fun _ => x) rhs :=
  verify_expr_le_on_interval_dyadic lhs rhs I prec depth
    cert.supported cert.prec_ok cert.checked

/-- Golden theorem for dyadic expression domination on a list of slabs. -/
theorem verify_expr_le_on_slabs_dyadic
    (lhs rhs : Expr) (slabs : List IntervalRat) (prec : Int) (depth : Nat)
    (hsupp : ExprSupportedWithInv (Expr.sub lhs rhs))
    (hprec : prec ≤ 0)
    (hcheck : checkExprLeOnSlabsDyadic lhs rhs slabs prec depth = true) :
    ∀ I ∈ slabs, ∀ x ∈ Set.Icc (I.lo : ℝ) I.hi,
      Expr.eval (fun _ => x) lhs ≤ Expr.eval (fun _ => x) rhs := by
  intro I hI x hx
  rw [checkExprLeOnSlabsDyadic, List.all_eq_true] at hcheck
  exact verify_expr_le_on_interval_dyadic lhs rhs I prec depth hsupp hprec
    (hcheck I hI) x hx

/-- Verify a packaged dyadic domination certificate over slabs. -/
theorem ExprLeOnSlabsDyadicCert.verify
    {lhs rhs : Expr} {slabs : List IntervalRat} {prec : Int} {depth : Nat}
    (cert : ExprLeOnSlabsDyadicCert lhs rhs slabs prec depth) :
    ∀ I ∈ slabs, ∀ x ∈ Set.Icc (I.lo : ℝ) I.hi,
      Expr.eval (fun _ => x) lhs ≤ Expr.eval (fun _ => x) rhs :=
  verify_expr_le_on_slabs_dyadic lhs rhs slabs prec depth
    cert.supported cert.prec_ok cert.checked

/-- Verify expression domination for all natural endpoints covered by a finite
slab family. -/
theorem verify_expr_le_on_nat_slab_cover_dyadic
    (lhs rhs : Expr) (cover : NatSlabCover) (prec : Int) (depth : Nat)
    (hsupp : ExprSupportedWithInv (Expr.sub lhs rhs))
    (hprec : prec ≤ 0)
    (hcheck : checkExprLeOnSlabsDyadic lhs rhs cover.slabs prec depth = true) :
    ∀ N, cover.cutoff ≤ N → evalAtNat lhs N ≤ evalAtNat rhs N := by
  intro N hN
  rcases cover.covers N hN with ⟨I, hI, hmem⟩
  simpa [evalAtNat] using
    verify_expr_le_on_slabs_dyadic lhs rhs cover.slabs prec depth hsupp hprec
      hcheck I hI (N : ℝ) hmem

/-- Verify expression domination for all natural endpoints using finite dyadic
slabs before `tailStart` and a symbolic tail proof afterwards. -/
theorem verify_expr_le_with_slab_tail_dyadic
    (lhs rhs : Expr) (cert : SlabTailCert lhs rhs) (prec : Int) (depth : Nat)
    (hsupp : ExprSupportedWithInv (Expr.sub lhs rhs))
    (hprec : prec ≤ 0)
    (hcheck : checkExprLeOnSlabsDyadic lhs rhs cert.slabs prec depth = true) :
    ∀ N, cert.cutoff ≤ N → evalAtNat lhs N ≤ evalAtNat rhs N := by
  intro N hN
  by_cases htail : cert.tailStart ≤ N
  · exact cert.tailBound N htail
  · have hpre : N < cert.tailStart := Nat.lt_of_not_ge htail
    rcases cert.coversSlabs N hN hpre with ⟨I, hI, hmem⟩
    simpa [evalAtNat] using
      verify_expr_le_on_slabs_dyadic lhs rhs cert.slabs prec depth hsupp hprec
        hcheck I hI (N : ℝ) hmem

/-- Check that a Stieltjes certificate's generated error is dominated by a
target error expression on one slab. -/
def checkStieltjesErrorLeTargetOnIntervalDyadic {A : AsympEnv}
    (C : StieltjesCert A) (targetError : Expr)
    (I : IntervalRat) (prec : Int) (depth : Nat) : Bool :=
  checkExprLeOnIntervalDyadic C.errorTerm targetError I prec depth

/-- Verify Stieltjes generated-error domination on one slab. -/
theorem verify_stieltjes_error_le_target_on_interval_dyadic {A : AsympEnv}
    (C : StieltjesCert A) (targetError : Expr)
    (I : IntervalRat) (prec : Int) (depth : Nat)
    (hsupp : ExprSupportedWithInv (Expr.sub C.errorTerm targetError))
    (hprec : prec ≤ 0)
    (hcheck :
      checkStieltjesErrorLeTargetOnIntervalDyadic C targetError I prec depth = true) :
    ∀ N : Nat, (N : ℝ) ∈ Set.Icc (I.lo : ℝ) I.hi →
      evalAtNat C.errorTerm N ≤ evalAtNat targetError N := by
  intro N hN
  exact verify_expr_le_on_interval_dyadic C.errorTerm targetError I prec depth
    hsupp hprec hcheck (N : ℝ) hN

/-- Verify Stieltjes generated-error domination on all endpoints covered by a
slab-tail certificate. -/
theorem verify_stieltjes_error_le_target_with_slab_tail_dyadic {A : AsympEnv}
    (C : StieltjesCert A) (targetError : Expr)
    (cert : SlabTailCert C.errorTerm targetError)
    (prec : Int) (depth : Nat)
    (hsupp : ExprSupportedWithInv (Expr.sub C.errorTerm targetError))
    (hprec : prec ≤ 0)
    (hcheck : checkExprLeOnSlabsDyadic C.errorTerm targetError cert.slabs prec depth = true) :
    ∀ N, cert.cutoff ≤ N → evalAtNat C.errorTerm N ≤ evalAtNat targetError N := by
  exact verify_expr_le_with_slab_tail_dyadic C.errorTerm targetError cert prec depth
    hsupp hprec hcheck

/-- Check that a hyperbola certificate's generated error is dominated by a
target error expression on one slab. -/
def checkHyperbolaErrorLeTargetOnIntervalDyadic {A B : AsympEnv}
    (C : HyperbolaCert A B) (targetError : Expr)
    (I : IntervalRat) (prec : Int) (depth : Nat) : Bool :=
  checkExprLeOnIntervalDyadic C.errorTerm targetError I prec depth

/-- Verify hyperbola generated-error domination on one slab. -/
theorem verify_hyperbola_error_le_target_on_interval_dyadic {A B : AsympEnv}
    (C : HyperbolaCert A B) (targetError : Expr)
    (I : IntervalRat) (prec : Int) (depth : Nat)
    (hsupp : ExprSupportedWithInv (Expr.sub C.errorTerm targetError))
    (hprec : prec ≤ 0)
    (hcheck :
      checkHyperbolaErrorLeTargetOnIntervalDyadic C targetError I prec depth = true) :
    ∀ N : Nat, (N : ℝ) ∈ Set.Icc (I.lo : ℝ) I.hi →
      evalAtNat C.errorTerm N ≤ evalAtNat targetError N := by
  intro N hN
  exact verify_expr_le_on_interval_dyadic C.errorTerm targetError I prec depth
    hsupp hprec hcheck (N : ℝ) hN

/-- Verify hyperbola generated-error domination on all endpoints covered by a
slab-tail certificate. -/
theorem verify_hyperbola_error_le_target_with_slab_tail_dyadic {A B : AsympEnv}
    (C : HyperbolaCert A B) (targetError : Expr)
    (cert : SlabTailCert C.errorTerm targetError)
    (prec : Int) (depth : Nat)
    (hsupp : ExprSupportedWithInv (Expr.sub C.errorTerm targetError))
    (hprec : prec ≤ 0)
    (hcheck :
      checkExprLeOnSlabsDyadic C.errorTerm targetError cert.slabs prec depth = true) :
    ∀ N, cert.cutoff ≤ N → evalAtNat C.errorTerm N ≤ evalAtNat targetError N := by
  exact verify_expr_le_with_slab_tail_dyadic C.errorTerm targetError cert prec depth
    hsupp hprec hcheck

end LeanCert.ANT.Asymp
