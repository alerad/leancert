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

end LeanCert.ANT.Asymp
