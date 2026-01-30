/-
Copyright (c) 2024 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Engine.IntervalEval

/-!
# Bounds with Inverse Support

This module provides checkers and theorems for expressions that may contain
inverse-like operations (inv, log, atan, arsinh, atanh) using `evalInterval?`
which handles domain validation.

## Main definitions

### Boolean Checkers
* `checkUpperBoundWithInv` - Check upper bounds for expressions with inverse support
* `checkLowerBoundWithInv` - Check lower bounds for expressions with inverse support
* `checkStrictUpperBoundWithInv` - Check strict upper bounds
* `checkStrictLowerBoundWithInv` - Check strict lower bounds

### Golden Theorems
* `verify_upper_bound_withInv` - Converts boolean check to semantic proof
* `verify_lower_bound_withInv` - Converts boolean check to semantic proof
* `verify_strict_upper_bound_withInv` - Strict upper bound verification
* `verify_strict_lower_bound_withInv` - Strict lower bound verification

### Bridge Theorems
* `verify_upper_bound_Icc_withInv` - Bridge to Set.Icc upper bounds
* `verify_lower_bound_Icc_withInv` - Bridge to Set.Icc lower bounds
* `verify_strict_upper_bound_Icc_withInv` - Bridge to Set.Icc strict upper bounds
* `verify_strict_lower_bound_Icc_withInv` - Bridge to Set.Icc strict lower bounds
-/

namespace LeanCert.Validity

open LeanCert.Core
open LeanCert.Engine

/-! ### Boolean Checkers for ExprSupportedWithInv

NOTE: These are noncomputable because `evalInterval?` uses Real Taylor approximations.
They cannot be used with `native_decide`. Use the verification theorems directly
in term proofs or with explicit computation.
-/

/-- Check upper bound for ExprSupportedWithInv expressions.
    Returns `true` iff evalInterval?1 succeeds and the upper bound is ≤ c.
    NOTE: Noncomputable - cannot be used with native_decide. -/
def checkUpperBoundWithInv (e : Expr) (I : IntervalRat) (c : ℚ) : Bool :=
  match evalInterval?1 e I with
  | some J => decide (J.hi ≤ c)
  | none => false

/-- Check lower bound for ExprSupportedWithInv expressions.
    Returns `true` iff evalInterval?1 succeeds and the lower bound is ≥ c.
    NOTE: Noncomputable - cannot be used with native_decide. -/
def checkLowerBoundWithInv (e : Expr) (I : IntervalRat) (c : ℚ) : Bool :=
  match evalInterval?1 e I with
  | some J => decide (c ≤ J.lo)
  | none => false

/-- Check strict upper bound for ExprSupportedWithInv expressions.
    NOTE: Noncomputable - cannot be used with native_decide. -/
def checkStrictUpperBoundWithInv (e : Expr) (I : IntervalRat) (c : ℚ) : Bool :=
  match evalInterval?1 e I with
  | some J => decide (J.hi < c)
  | none => false

/-- Check strict lower bound for ExprSupportedWithInv expressions.
    NOTE: Noncomputable - cannot be used with native_decide. -/
def checkStrictLowerBoundWithInv (e : Expr) (I : IntervalRat) (c : ℚ) : Bool :=
  match evalInterval?1 e I with
  | some J => decide (c < J.lo)
  | none => false

/-! ### Golden Theorems for ExprSupportedWithInv -/

/-- Verification theorem for upper bounds with ExprSupportedWithInv. -/
theorem verify_upper_bound_withInv (e : Expr) (hsupp : ExprSupportedWithInv e)
    (I : IntervalRat) (c : ℚ)
    (h_cert : checkUpperBoundWithInv e I c = true) :
    ∀ x ∈ I, Expr.eval (fun _ => x) e ≤ c := by
  simp only [checkUpperBoundWithInv] at h_cert
  split at h_cert
  · next J hsome =>
    simp only [decide_eq_true_eq] at h_cert
    exact evalInterval?_le_of_hi e hsupp I J c hsome h_cert
  · simp at h_cert

/-- Verification theorem for lower bounds with ExprSupportedWithInv. -/
theorem verify_lower_bound_withInv (e : Expr) (hsupp : ExprSupportedWithInv e)
    (I : IntervalRat) (c : ℚ)
    (h_cert : checkLowerBoundWithInv e I c = true) :
    ∀ x ∈ I, c ≤ Expr.eval (fun _ => x) e := by
  simp only [checkLowerBoundWithInv] at h_cert
  split at h_cert
  · next J hsome =>
    simp only [decide_eq_true_eq] at h_cert
    exact evalInterval?_ge_of_lo e hsupp I J c hsome h_cert
  · simp at h_cert

/-- Verification theorem for strict upper bounds with ExprSupportedWithInv. -/
theorem verify_strict_upper_bound_withInv (e : Expr) (hsupp : ExprSupportedWithInv e)
    (I : IntervalRat) (c : ℚ)
    (h_cert : checkStrictUpperBoundWithInv e I c = true) :
    ∀ x ∈ I, Expr.eval (fun _ => x) e < c := by
  simp only [checkStrictUpperBoundWithInv] at h_cert
  split at h_cert
  · next J hsome =>
    simp only [decide_eq_true_eq] at h_cert
    intro x hx
    have hle := evalInterval?_le_of_hi e hsupp I J J.hi hsome (le_refl _) x hx
    have hJ_hi : Expr.eval (fun _ => x) e ≤ J.hi := hle
    calc Expr.eval (fun _ => x) e ≤ J.hi := hJ_hi
      _ < c := by exact_mod_cast h_cert
  · simp at h_cert

/-- Verification theorem for strict lower bounds with ExprSupportedWithInv. -/
theorem verify_strict_lower_bound_withInv (e : Expr) (hsupp : ExprSupportedWithInv e)
    (I : IntervalRat) (c : ℚ)
    (h_cert : checkStrictLowerBoundWithInv e I c = true) :
    ∀ x ∈ I, c < Expr.eval (fun _ => x) e := by
  simp only [checkStrictLowerBoundWithInv] at h_cert
  split at h_cert
  · next J hsome =>
    simp only [decide_eq_true_eq] at h_cert
    intro x hx
    have hge := evalInterval?_ge_of_lo e hsupp I J J.lo hsome (le_refl _) x hx
    have hJ_lo : (J.lo : ℝ) ≤ Expr.eval (fun _ => x) e := hge
    have hc_lt_lo : (c : ℝ) < (J.lo : ℝ) := by exact_mod_cast h_cert
    exact lt_of_lt_of_le hc_lt_lo hJ_lo
  · simp at h_cert

/-! ### Set.Icc Bridge Theorems for ExprSupportedWithInv -/

/-- Bridge theorem for Set.Icc upper bounds with ExprSupportedWithInv. -/
theorem verify_upper_bound_Icc_withInv (e : Expr) (hsupp : ExprSupportedWithInv e)
    (lo hi : ℚ) (hle : lo ≤ hi) (c : ℚ)
    (h_cert : checkUpperBoundWithInv e ⟨lo, hi, hle⟩ c = true) :
    ∀ x ∈ Set.Icc (lo : ℝ) (hi : ℝ), Expr.eval (fun _ => x) e ≤ c := by
  intro x hx
  have := verify_upper_bound_withInv e hsupp ⟨lo, hi, hle⟩ c h_cert
  apply this
  rwa [IntervalRat.mem_iff_mem_Icc]

/-- Bridge theorem for Set.Icc lower bounds with ExprSupportedWithInv. -/
theorem verify_lower_bound_Icc_withInv (e : Expr) (hsupp : ExprSupportedWithInv e)
    (lo hi : ℚ) (hle : lo ≤ hi) (c : ℚ)
    (h_cert : checkLowerBoundWithInv e ⟨lo, hi, hle⟩ c = true) :
    ∀ x ∈ Set.Icc (lo : ℝ) (hi : ℝ), c ≤ Expr.eval (fun _ => x) e := by
  intro x hx
  have := verify_lower_bound_withInv e hsupp ⟨lo, hi, hle⟩ c h_cert
  apply this
  rwa [IntervalRat.mem_iff_mem_Icc]

/-- Bridge theorem for Set.Icc strict upper bounds with ExprSupportedWithInv. -/
theorem verify_strict_upper_bound_Icc_withInv (e : Expr) (hsupp : ExprSupportedWithInv e)
    (lo hi : ℚ) (hle : lo ≤ hi) (c : ℚ)
    (h_cert : checkStrictUpperBoundWithInv e ⟨lo, hi, hle⟩ c = true) :
    ∀ x ∈ Set.Icc (lo : ℝ) (hi : ℝ), Expr.eval (fun _ => x) e < c := by
  intro x hx
  have := verify_strict_upper_bound_withInv e hsupp ⟨lo, hi, hle⟩ c h_cert
  apply this
  rwa [IntervalRat.mem_iff_mem_Icc]

/-- Bridge theorem for Set.Icc strict lower bounds with ExprSupportedWithInv. -/
theorem verify_strict_lower_bound_Icc_withInv (e : Expr) (hsupp : ExprSupportedWithInv e)
    (lo hi : ℚ) (hle : lo ≤ hi) (c : ℚ)
    (h_cert : checkStrictLowerBoundWithInv e ⟨lo, hi, hle⟩ c = true) :
    ∀ x ∈ Set.Icc (lo : ℝ) (hi : ℝ), c < Expr.eval (fun _ => x) e := by
  intro x hx
  have := verify_strict_lower_bound_withInv e hsupp ⟨lo, hi, hle⟩ c h_cert
  apply this
  rwa [IntervalRat.mem_iff_mem_Icc]

end LeanCert.Validity
