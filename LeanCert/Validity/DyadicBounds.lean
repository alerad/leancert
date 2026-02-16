/-
Copyright (c) 2024 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Engine.IntervalEvalDyadic

/-!
# Certificate-Driven Verification with Dyadic Arithmetic

This file provides Golden Theorems for the Dyadic arithmetic backend, mirroring the
structure of `Validity/Bounds.lean` but using the high-performance `IntervalDyadic` type.

## Overview

The Dyadic backend offers significant performance advantages over rational arithmetic
for many verification tasks, while maintaining full soundness. This module exposes
the Dyadic evaluator as a first-class citizen for certificate-driven verification.

## Main definitions

### Boolean Checkers
* `checkUpperBoundDyadic` - Check if the computed upper bound is ≤ c
* `checkLowerBoundDyadic` - Check if the computed lower bound is ≥ c

### Golden Theorems
* `verify_upper_bound_dyadic` - Converts boolean check to semantic proof for upper bounds
* `verify_lower_bound_dyadic` - Converts boolean check to semantic proof for lower bounds

For `ExprSupported` expressions (no log), convenience versions are provided that
don't require explicit domain validity proofs.

## Design

The Dyadic backend uses `IntervalDyadic` which represents intervals with dyadic endpoints
(numbers of the form m · 2^e). This allows for faster arithmetic than arbitrary rationals
while still providing rigorous bounds.

Key parameters:
- `prec : Int` - Precision (negative = more precision). Must satisfy `prec ≤ 0`.
- `depth : Nat` - Taylor series depth for transcendental functions.

## Trust Hierarchy

This provides an alternative verification path to the rational-based `Validity/Bounds.lean`:
- Same `Expr` AST and `ExprSupportedCore` predicate
- Different computational backend (`IntervalDyadic` vs `IntervalRat`)
- Same semantic guarantees (bounds on real-valued evaluation)

The Dyadic path is faster but the rational path may be preferred for reproducibility
across different platforms.
-/

namespace LeanCert.Validity

open LeanCert.Core
open LeanCert.Engine

/-! ### Boolean Checkers

These check the computed interval bounds. Domain validity is handled separately.
-/

/-- Check if an expression's computed upper bound is ≤ c using Dyadic arithmetic.
    This is the computable check that `native_decide` will execute.

    Note: Domain validity must be established separately. -/
def checkUpperBoundDyadic (e : Expr) (lo hi : ℚ) (hle : lo ≤ hi) (c : ℚ)
    (prec : Int) (depth : Nat) : Bool :=
  let I_rat : IntervalRat := ⟨lo, hi, hle⟩
  let ρ := fun _ => IntervalDyadic.ofIntervalRat I_rat prec
  (evalIntervalDyadic e ρ { precision := prec, taylorDepth := depth }).upperBoundedBy c

/-- Check if an expression's computed lower bound is ≥ c using Dyadic arithmetic. -/
def checkLowerBoundDyadic (e : Expr) (lo hi : ℚ) (hle : lo ≤ hi) (c : ℚ)
    (prec : Int) (depth : Nat) : Bool :=
  let I_rat : IntervalRat := ⟨lo, hi, hle⟩
  let ρ := fun _ => IntervalDyadic.ofIntervalRat I_rat prec
  (evalIntervalDyadic e ρ { precision := prec, taylorDepth := depth }).lowerBoundedBy c

/-- Check if an expression's computed upper bound is strictly < c using Dyadic arithmetic. -/
def checkStrictUpperBoundDyadic (e : Expr) (lo hi : ℚ) (hle : lo ≤ hi) (c : ℚ)
    (prec : Int) (depth : Nat) : Bool :=
  let I_rat : IntervalRat := ⟨lo, hi, hle⟩
  let ρ := fun _ => IntervalDyadic.ofIntervalRat I_rat prec
  decide ((evalIntervalDyadic e ρ { precision := prec, taylorDepth := depth }).hi.toRat < c)

/-- Check if an expression's computed lower bound is strictly > c using Dyadic arithmetic. -/
def checkStrictLowerBoundDyadic (e : Expr) (lo hi : ℚ) (hle : lo ≤ hi) (c : ℚ)
    (prec : Int) (depth : Nat) : Bool :=
  let I_rat : IntervalRat := ⟨lo, hi, hle⟩
  let ρ := fun _ => IntervalDyadic.ofIntervalRat I_rat prec
  decide (c < (evalIntervalDyadic e ρ { precision := prec, taylorDepth := depth }).lo.toRat)

/-! ### Golden Theorems

These theorems convert the boolean `true` from the checkers into semantic proofs
about Real numbers.
-/

/-- **Golden Theorem for Dyadic Upper Bounds**

    If the bound check passes and domain validity holds, then
    `∀ x ∈ [lo, hi], Expr.eval (fun _ => x) e ≤ c`.

    This is the key theorem for certificate-driven verification using the Dyadic backend.

    Parameters:
    - `e`: The expression to evaluate
    - `hsupp`: Proof that the expression is supported (ExprSupportedCore)
    - `lo`, `hi`, `hle`: The interval [lo, hi] with proof lo ≤ hi
    - `c`: The upper bound to verify
    - `prec`: Precision (must be ≤ 0)
    - `depth`: Taylor series depth
    - `h_prec`: Proof that prec ≤ 0
    - `hdom`: Proof of domain validity (automatic for ExprSupported)
    - `h_check`: The boolean check result -/
theorem verify_upper_bound_dyadic (e : Expr) (hsupp : ExprSupportedCore e)
    (lo hi : ℚ) (hle : lo ≤ hi) (c : ℚ)
    (prec : Int) (depth : Nat) (h_prec : prec ≤ 0)
    (hdom : evalDomainValidDyadic e (fun _ => IntervalDyadic.ofIntervalRat ⟨lo, hi, hle⟩ prec)
        { precision := prec, taylorDepth := depth })
    (h_check : checkUpperBoundDyadic e lo hi hle c prec depth = true) :
    ∀ x ∈ Set.Icc (lo : ℝ) hi, Expr.eval (fun _ => x) e ≤ c := by
  intro x hx
  -- Setup environments
  let I_rat : IntervalRat := ⟨lo, hi, hle⟩
  let ρ_dyad : IntervalDyadicEnv := fun _ => IntervalDyadic.ofIntervalRat I_rat prec
  let ρ_real : Nat → ℝ := fun _ => x
  -- Show x is in the Dyadic environment
  have h_env : envMemDyadic ρ_real ρ_dyad := by
    intro i
    apply IntervalDyadic.mem_ofIntervalRat _ prec h_prec
    rwa [IntervalRat.mem_iff_mem_Icc]
  -- Apply correctness of evaluator
  have h_eval := evalIntervalDyadic_correct e hsupp ρ_real ρ_dyad h_env
    { precision := prec, taylorDepth := depth } h_prec hdom
  -- Extract upper bound from boolean check
  simp only [checkUpperBoundDyadic, IntervalDyadic.upperBoundedBy, decide_eq_true_eq] at h_check
  -- Conclude: eval ≤ hi.toRat ≤ c
  calc Expr.eval (fun _ => x) e
      ≤ ((evalIntervalDyadic e ρ_dyad { precision := prec, taylorDepth := depth }).hi.toRat : ℝ) := h_eval.2
    _ ≤ c := by exact_mod_cast h_check

/-- **Golden Theorem for Dyadic Lower Bounds**

    If the bound check passes and domain validity holds, then
    `∀ x ∈ [lo, hi], c ≤ Expr.eval (fun _ => x) e`. -/
theorem verify_lower_bound_dyadic (e : Expr) (hsupp : ExprSupportedCore e)
    (lo hi : ℚ) (hle : lo ≤ hi) (c : ℚ)
    (prec : Int) (depth : Nat) (h_prec : prec ≤ 0)
    (hdom : evalDomainValidDyadic e (fun _ => IntervalDyadic.ofIntervalRat ⟨lo, hi, hle⟩ prec)
        { precision := prec, taylorDepth := depth })
    (h_check : checkLowerBoundDyadic e lo hi hle c prec depth = true) :
    ∀ x ∈ Set.Icc (lo : ℝ) hi, c ≤ Expr.eval (fun _ => x) e := by
  intro x hx
  let I_rat : IntervalRat := ⟨lo, hi, hle⟩
  let ρ_dyad : IntervalDyadicEnv := fun _ => IntervalDyadic.ofIntervalRat I_rat prec
  let ρ_real : Nat → ℝ := fun _ => x
  have h_env : envMemDyadic ρ_real ρ_dyad := by
    intro i
    apply IntervalDyadic.mem_ofIntervalRat _ prec h_prec
    rwa [IntervalRat.mem_iff_mem_Icc]
  have h_eval := evalIntervalDyadic_correct e hsupp ρ_real ρ_dyad h_env
    { precision := prec, taylorDepth := depth } h_prec hdom
  simp only [checkLowerBoundDyadic, IntervalDyadic.lowerBoundedBy, decide_eq_true_eq] at h_check
  calc (c : ℝ)
      ≤ ((evalIntervalDyadic e ρ_dyad { precision := prec, taylorDepth := depth }).lo.toRat : ℝ) := by exact_mod_cast h_check
    _ ≤ Expr.eval (fun _ => x) e := h_eval.1

/-! ### Convenience Theorems for ExprSupported

For expressions that don't use `log`, domain validity is automatic.
These versions don't require the `hdom` hypothesis. -/

/-- Convenience theorem for ExprSupported expressions (no log).
    Domain validity is automatic, so only the bound check is needed. -/
theorem verify_upper_bound_dyadic' (e : Expr) (hsupp : ExprSupported e)
    (lo hi : ℚ) (hle : lo ≤ hi) (c : ℚ)
    (prec : Int) (depth : Nat) (h_prec : prec ≤ 0)
    (h_check : checkUpperBoundDyadic e lo hi hle c prec depth = true) :
    ∀ x ∈ Set.Icc (lo : ℝ) hi, Expr.eval (fun _ => x) e ≤ c := by
  have hdom : evalDomainValidDyadic e
      (fun _ => IntervalDyadic.ofIntervalRat ⟨lo, hi, hle⟩ prec)
      { precision := prec, taylorDepth := depth } :=
    evalDomainValidDyadic_of_ExprSupported hsupp _ _
  exact verify_upper_bound_dyadic e hsupp.toCore lo hi hle c prec depth h_prec hdom h_check

/-- Convenience theorem for ExprSupported expressions (no log).
    Domain validity is automatic, so only the bound check is needed. -/
theorem verify_lower_bound_dyadic' (e : Expr) (hsupp : ExprSupported e)
    (lo hi : ℚ) (hle : lo ≤ hi) (c : ℚ)
    (prec : Int) (depth : Nat) (h_prec : prec ≤ 0)
    (h_check : checkLowerBoundDyadic e lo hi hle c prec depth = true) :
    ∀ x ∈ Set.Icc (lo : ℝ) hi, c ≤ Expr.eval (fun _ => x) e := by
  have hdom : evalDomainValidDyadic e
      (fun _ => IntervalDyadic.ofIntervalRat ⟨lo, hi, hle⟩ prec)
      { precision := prec, taylorDepth := depth } :=
    evalDomainValidDyadic_of_ExprSupported hsupp _ _
  exact verify_lower_bound_dyadic e hsupp.toCore lo hi hle c prec depth h_prec hdom h_check

/-! ### Strict Inequality Theorems -/

/-- **Golden Theorem for Strict Dyadic Upper Bounds**

    If the strict bound check passes and domain validity holds, then
    `∀ x ∈ [lo, hi], Expr.eval (fun _ => x) e < c`. -/
theorem verify_strict_upper_bound_dyadic (e : Expr) (hsupp : ExprSupportedCore e)
    (lo hi : ℚ) (hle : lo ≤ hi) (c : ℚ)
    (prec : Int) (depth : Nat) (h_prec : prec ≤ 0)
    (hdom : evalDomainValidDyadic e (fun _ => IntervalDyadic.ofIntervalRat ⟨lo, hi, hle⟩ prec)
        { precision := prec, taylorDepth := depth })
    (h_check : checkStrictUpperBoundDyadic e lo hi hle c prec depth = true) :
    ∀ x ∈ Set.Icc (lo : ℝ) hi, Expr.eval (fun _ => x) e < c := by
  intro x hx
  let I_rat : IntervalRat := ⟨lo, hi, hle⟩
  let ρ_dyad : IntervalDyadicEnv := fun _ => IntervalDyadic.ofIntervalRat I_rat prec
  let ρ_real : Nat → ℝ := fun _ => x
  have h_env : envMemDyadic ρ_real ρ_dyad := by
    intro i
    apply IntervalDyadic.mem_ofIntervalRat _ prec h_prec
    rwa [IntervalRat.mem_iff_mem_Icc]
  have h_eval := evalIntervalDyadic_correct e hsupp ρ_real ρ_dyad h_env
    { precision := prec, taylorDepth := depth } h_prec hdom
  simp only [checkStrictUpperBoundDyadic, decide_eq_true_eq] at h_check
  calc Expr.eval (fun _ => x) e
      ≤ ((evalIntervalDyadic e ρ_dyad { precision := prec, taylorDepth := depth }).hi.toRat : ℝ) := h_eval.2
    _ < c := by exact_mod_cast h_check

/-- **Golden Theorem for Strict Dyadic Lower Bounds**

    If the strict bound check passes and domain validity holds, then
    `∀ x ∈ [lo, hi], c < Expr.eval (fun _ => x) e`. -/
theorem verify_strict_lower_bound_dyadic (e : Expr) (hsupp : ExprSupportedCore e)
    (lo hi : ℚ) (hle : lo ≤ hi) (c : ℚ)
    (prec : Int) (depth : Nat) (h_prec : prec ≤ 0)
    (hdom : evalDomainValidDyadic e (fun _ => IntervalDyadic.ofIntervalRat ⟨lo, hi, hle⟩ prec)
        { precision := prec, taylorDepth := depth })
    (h_check : checkStrictLowerBoundDyadic e lo hi hle c prec depth = true) :
    ∀ x ∈ Set.Icc (lo : ℝ) hi, c < Expr.eval (fun _ => x) e := by
  intro x hx
  let I_rat : IntervalRat := ⟨lo, hi, hle⟩
  let ρ_dyad : IntervalDyadicEnv := fun _ => IntervalDyadic.ofIntervalRat I_rat prec
  let ρ_real : Nat → ℝ := fun _ => x
  have h_env : envMemDyadic ρ_real ρ_dyad := by
    intro i
    apply IntervalDyadic.mem_ofIntervalRat _ prec h_prec
    rwa [IntervalRat.mem_iff_mem_Icc]
  have h_eval := evalIntervalDyadic_correct e hsupp ρ_real ρ_dyad h_env
    { precision := prec, taylorDepth := depth } h_prec hdom
  simp only [checkStrictLowerBoundDyadic, decide_eq_true_eq] at h_check
  calc (c : ℝ)
      < ((evalIntervalDyadic e ρ_dyad { precision := prec, taylorDepth := depth }).lo.toRat : ℝ) := by exact_mod_cast h_check
    _ ≤ Expr.eval (fun _ => x) e := h_eval.1

/-! ### Convenience Theorems for Strict Inequalities (ExprSupported) -/

/-- Convenience theorem for strict upper bounds with ExprSupported expressions. -/
theorem verify_strict_upper_bound_dyadic' (e : Expr) (hsupp : ExprSupported e)
    (lo hi : ℚ) (hle : lo ≤ hi) (c : ℚ)
    (prec : Int) (depth : Nat) (h_prec : prec ≤ 0)
    (h_check : checkStrictUpperBoundDyadic e lo hi hle c prec depth = true) :
    ∀ x ∈ Set.Icc (lo : ℝ) hi, Expr.eval (fun _ => x) e < c := by
  have hdom : evalDomainValidDyadic e
      (fun _ => IntervalDyadic.ofIntervalRat ⟨lo, hi, hle⟩ prec)
      { precision := prec, taylorDepth := depth } :=
    evalDomainValidDyadic_of_ExprSupported hsupp _ _
  exact verify_strict_upper_bound_dyadic e hsupp.toCore lo hi hle c prec depth h_prec hdom h_check

/-- Convenience theorem for strict lower bounds with ExprSupported expressions. -/
theorem verify_strict_lower_bound_dyadic' (e : Expr) (hsupp : ExprSupported e)
    (lo hi : ℚ) (hle : lo ≤ hi) (c : ℚ)
    (prec : Int) (depth : Nat) (h_prec : prec ≤ 0)
    (h_check : checkStrictLowerBoundDyadic e lo hi hle c prec depth = true) :
    ∀ x ∈ Set.Icc (lo : ℝ) hi, c < Expr.eval (fun _ => x) e := by
  have hdom : evalDomainValidDyadic e
      (fun _ => IntervalDyadic.ofIntervalRat ⟨lo, hi, hle⟩ prec)
      { precision := prec, taylorDepth := depth } :=
    evalDomainValidDyadic_of_ExprSupported hsupp _ _
  exact verify_strict_lower_bound_dyadic e hsupp.toCore lo hi hle c prec depth h_prec hdom h_check

/-! ### WithInv Check Functions

These bundle domain validity + bound check for expressions containing inv/log.
A single `native_decide` call proves both domain validity and the bound. -/

/-- Check upper bound for WithInv expressions (inv/log). Includes domain validity check. -/
def checkUpperBoundDyadicWithInv (e : Expr) (lo hi : ℚ) (hle : lo ≤ hi) (c : ℚ)
    (prec : Int) (depth : Nat) : Bool :=
  let I_rat : IntervalRat := ⟨lo, hi, hle⟩
  let ρ := fun _ => IntervalDyadic.ofIntervalRat I_rat prec
  let cfg : DyadicConfig := { precision := prec, taylorDepth := depth }
  checkDomainValidDyadic e ρ cfg &&
    (evalIntervalDyadic e ρ cfg).upperBoundedBy c

/-- Check lower bound for WithInv expressions (inv/log). Includes domain validity check. -/
def checkLowerBoundDyadicWithInv (e : Expr) (lo hi : ℚ) (hle : lo ≤ hi) (c : ℚ)
    (prec : Int) (depth : Nat) : Bool :=
  let I_rat : IntervalRat := ⟨lo, hi, hle⟩
  let ρ := fun _ => IntervalDyadic.ofIntervalRat I_rat prec
  let cfg : DyadicConfig := { precision := prec, taylorDepth := depth }
  checkDomainValidDyadic e ρ cfg &&
    (evalIntervalDyadic e ρ cfg).lowerBoundedBy c

/-- Check strict upper bound for WithInv expressions. Includes domain validity check. -/
def checkStrictUpperBoundDyadicWithInv (e : Expr) (lo hi : ℚ) (hle : lo ≤ hi) (c : ℚ)
    (prec : Int) (depth : Nat) : Bool :=
  let I_rat : IntervalRat := ⟨lo, hi, hle⟩
  let ρ := fun _ => IntervalDyadic.ofIntervalRat I_rat prec
  let cfg : DyadicConfig := { precision := prec, taylorDepth := depth }
  checkDomainValidDyadic e ρ cfg &&
    decide ((evalIntervalDyadic e ρ cfg).hi.toRat < c)

/-- Check strict lower bound for WithInv expressions. Includes domain validity check. -/
def checkStrictLowerBoundDyadicWithInv (e : Expr) (lo hi : ℚ) (hle : lo ≤ hi) (c : ℚ)
    (prec : Int) (depth : Nat) : Bool :=
  let I_rat : IntervalRat := ⟨lo, hi, hle⟩
  let ρ := fun _ => IntervalDyadic.ofIntervalRat I_rat prec
  let cfg : DyadicConfig := { precision := prec, taylorDepth := depth }
  checkDomainValidDyadic e ρ cfg &&
    decide (c < (evalIntervalDyadic e ρ cfg).lo.toRat)

/-! ### WithInv Golden Theorems

For `ExprSupportedWithInv` expressions (with inv/log). Domain validity is extracted
from the combined check function, so no separate `hdom` argument is needed. -/

/-- Golden Theorem for Dyadic upper bounds with inv/log expressions. -/
theorem verify_upper_bound_dyadic_withInv (e : Expr) (hsupp : ExprSupportedWithInv e)
    (lo hi : ℚ) (hle : lo ≤ hi) (c : ℚ)
    (prec : Int) (depth : Nat) (h_prec : prec ≤ 0)
    (h_check : checkUpperBoundDyadicWithInv e lo hi hle c prec depth = true) :
    ∀ x ∈ Set.Icc (lo : ℝ) hi, Expr.eval (fun _ => x) e ≤ c := by
  intro x hx
  let I_rat : IntervalRat := ⟨lo, hi, hle⟩
  let ρ_dyad : IntervalDyadicEnv := fun _ => IntervalDyadic.ofIntervalRat I_rat prec
  let cfg : DyadicConfig := { precision := prec, taylorDepth := depth }
  simp only [checkUpperBoundDyadicWithInv, Bool.and_eq_true] at h_check
  obtain ⟨h_dom_bool, h_bound⟩ := h_check
  have hdom := checkDomainValidDyadic_correct e ρ_dyad cfg h_dom_bool
  have h_env : envMemDyadic (fun _ => x) ρ_dyad := by
    intro i
    apply IntervalDyadic.mem_ofIntervalRat _ prec h_prec
    rwa [IntervalRat.mem_iff_mem_Icc]
  have h_eval := evalIntervalDyadic_correct_withInv e hsupp (fun _ => x) ρ_dyad h_env cfg h_prec hdom
  simp only [IntervalDyadic.upperBoundedBy, decide_eq_true_eq] at h_bound
  calc Expr.eval (fun _ => x) e
      ≤ ((evalIntervalDyadic e ρ_dyad cfg).hi.toRat : ℝ) := h_eval.2
    _ ≤ c := by exact_mod_cast h_bound

/-- Golden Theorem for Dyadic lower bounds with inv/log expressions. -/
theorem verify_lower_bound_dyadic_withInv (e : Expr) (hsupp : ExprSupportedWithInv e)
    (lo hi : ℚ) (hle : lo ≤ hi) (c : ℚ)
    (prec : Int) (depth : Nat) (h_prec : prec ≤ 0)
    (h_check : checkLowerBoundDyadicWithInv e lo hi hle c prec depth = true) :
    ∀ x ∈ Set.Icc (lo : ℝ) hi, c ≤ Expr.eval (fun _ => x) e := by
  intro x hx
  let I_rat : IntervalRat := ⟨lo, hi, hle⟩
  let ρ_dyad : IntervalDyadicEnv := fun _ => IntervalDyadic.ofIntervalRat I_rat prec
  let cfg : DyadicConfig := { precision := prec, taylorDepth := depth }
  simp only [checkLowerBoundDyadicWithInv, Bool.and_eq_true] at h_check
  obtain ⟨h_dom_bool, h_bound⟩ := h_check
  have hdom := checkDomainValidDyadic_correct e ρ_dyad cfg h_dom_bool
  have h_env : envMemDyadic (fun _ => x) ρ_dyad := by
    intro i
    apply IntervalDyadic.mem_ofIntervalRat _ prec h_prec
    rwa [IntervalRat.mem_iff_mem_Icc]
  have h_eval := evalIntervalDyadic_correct_withInv e hsupp (fun _ => x) ρ_dyad h_env cfg h_prec hdom
  simp only [IntervalDyadic.lowerBoundedBy, decide_eq_true_eq] at h_bound
  calc (c : ℝ)
      ≤ ((evalIntervalDyadic e ρ_dyad cfg).lo.toRat : ℝ) := by exact_mod_cast h_bound
    _ ≤ Expr.eval (fun _ => x) e := h_eval.1

/-- Golden Theorem for strict Dyadic upper bounds with inv/log expressions. -/
theorem verify_strict_upper_bound_dyadic_withInv (e : Expr) (hsupp : ExprSupportedWithInv e)
    (lo hi : ℚ) (hle : lo ≤ hi) (c : ℚ)
    (prec : Int) (depth : Nat) (h_prec : prec ≤ 0)
    (h_check : checkStrictUpperBoundDyadicWithInv e lo hi hle c prec depth = true) :
    ∀ x ∈ Set.Icc (lo : ℝ) hi, Expr.eval (fun _ => x) e < c := by
  intro x hx
  let I_rat : IntervalRat := ⟨lo, hi, hle⟩
  let ρ_dyad : IntervalDyadicEnv := fun _ => IntervalDyadic.ofIntervalRat I_rat prec
  let cfg : DyadicConfig := { precision := prec, taylorDepth := depth }
  simp only [checkStrictUpperBoundDyadicWithInv, Bool.and_eq_true] at h_check
  obtain ⟨h_dom_bool, h_bound⟩ := h_check
  have hdom := checkDomainValidDyadic_correct e ρ_dyad cfg h_dom_bool
  have h_env : envMemDyadic (fun _ => x) ρ_dyad := by
    intro i
    apply IntervalDyadic.mem_ofIntervalRat _ prec h_prec
    rwa [IntervalRat.mem_iff_mem_Icc]
  have h_eval := evalIntervalDyadic_correct_withInv e hsupp (fun _ => x) ρ_dyad h_env cfg h_prec hdom
  simp only [decide_eq_true_eq] at h_bound
  calc Expr.eval (fun _ => x) e
      ≤ ((evalIntervalDyadic e ρ_dyad cfg).hi.toRat : ℝ) := h_eval.2
    _ < c := by exact_mod_cast h_bound

/-- Golden Theorem for strict Dyadic lower bounds with inv/log expressions. -/
theorem verify_strict_lower_bound_dyadic_withInv (e : Expr) (hsupp : ExprSupportedWithInv e)
    (lo hi : ℚ) (hle : lo ≤ hi) (c : ℚ)
    (prec : Int) (depth : Nat) (h_prec : prec ≤ 0)
    (h_check : checkStrictLowerBoundDyadicWithInv e lo hi hle c prec depth = true) :
    ∀ x ∈ Set.Icc (lo : ℝ) hi, c < Expr.eval (fun _ => x) e := by
  intro x hx
  let I_rat : IntervalRat := ⟨lo, hi, hle⟩
  let ρ_dyad : IntervalDyadicEnv := fun _ => IntervalDyadic.ofIntervalRat I_rat prec
  let cfg : DyadicConfig := { precision := prec, taylorDepth := depth }
  simp only [checkStrictLowerBoundDyadicWithInv, Bool.and_eq_true] at h_check
  obtain ⟨h_dom_bool, h_bound⟩ := h_check
  have hdom := checkDomainValidDyadic_correct e ρ_dyad cfg h_dom_bool
  have h_env : envMemDyadic (fun _ => x) ρ_dyad := by
    intro i
    apply IntervalDyadic.mem_ofIntervalRat _ prec h_prec
    rwa [IntervalRat.mem_iff_mem_Icc]
  have h_eval := evalIntervalDyadic_correct_withInv e hsupp (fun _ => x) ρ_dyad h_env cfg h_prec hdom
  simp only [decide_eq_true_eq] at h_bound
  calc (c : ℝ)
      < ((evalIntervalDyadic e ρ_dyad cfg).lo.toRat : ℝ) := by exact_mod_cast h_bound
    _ ≤ Expr.eval (fun _ => x) e := h_eval.1

end LeanCert.Validity
