/-
Copyright (c) 2024 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Engine.IntervalEval

/-!
# Checked Bounds for Partial Operations

This module provides checkers and theorems for expressions that may contain
inverse-like operations (inv, log, atan, arsinh, atanh) using `evalInterval?`
which handles domain validation.

## Main definitions

### Boolean Checkers
* `checkUpperBoundChecked` - Check upper bounds for expressions with inverse support
* `checkLowerBoundChecked` - Check lower bounds for expressions with inverse support
* `checkStrictUpperBoundChecked` - Check strict upper bounds
* `checkStrictLowerBoundChecked` - Check strict lower bounds

### Golden Theorems
* `verify_upper_bound_checked` - Converts boolean check to semantic proof
* `verify_lower_bound_checked` - Converts boolean check to semantic proof
* `verify_strict_upper_bound_checked` - Strict upper bound verification
* `verify_strict_lower_bound_checked` - Strict lower bound verification

### Bridge Theorems
* `verify_upper_bound_Icc_checked` - Bridge to Set.Icc upper bounds
* `verify_lower_bound_Icc_checked` - Bridge to Set.Icc lower bounds
* `verify_strict_upper_bound_Icc_checked` - Bridge to Set.Icc strict upper bounds
* `verify_strict_lower_bound_Icc_checked` - Bridge to Set.Icc strict lower bounds
-/

namespace LeanCert.Validity

open LeanCert.Core
open LeanCert.Engine

/-! ### Boolean Checkers for arbitrary expressions

NOTE: These are noncomputable because `evalInterval?` uses Real Taylor approximations.
They cannot be used with `native_decide`. Use the verification theorems directly
in term proofs or with explicit computation.
-/

/-- Check upper bound for arbitrary expressions.
    Returns `true` iff evalInterval?1 succeeds and the upper bound is ≤ c.
    NOTE: Noncomputable - cannot be used with native_decide. -/
def checkUpperBoundChecked (e : Expr) (I : IntervalRat) (c : ℚ) : Bool :=
  match evalInterval?1 e I with
  | some J => decide (J.hi ≤ c)
  | none => false

/-- Check lower bound for arbitrary expressions.
    Returns `true` iff evalInterval?1 succeeds and the lower bound is ≥ c.
    NOTE: Noncomputable - cannot be used with native_decide. -/
def checkLowerBoundChecked (e : Expr) (I : IntervalRat) (c : ℚ) : Bool :=
  match evalInterval?1 e I with
  | some J => decide (c ≤ J.lo)
  | none => false

/-- Check strict upper bound for arbitrary expressions.
    NOTE: Noncomputable - cannot be used with native_decide. -/
def checkStrictUpperBoundChecked (e : Expr) (I : IntervalRat) (c : ℚ) : Bool :=
  match evalInterval?1 e I with
  | some J => decide (J.hi < c)
  | none => false

/-- Check strict lower bound for arbitrary expressions.
    NOTE: Noncomputable - cannot be used with native_decide. -/
def checkStrictLowerBoundChecked (e : Expr) (I : IntervalRat) (c : ℚ) : Bool :=
  match evalInterval?1 e I with
  | some J => decide (c < J.lo)
  | none => false

/-! ### Golden Theorems for arbitrary expressions -/

/-- Verification theorem for upper bounds with arbitrary expressions. -/
theorem verify_upper_bound_checked (e : Expr)
    (I : IntervalRat) (c : ℚ)
    (h_cert : checkUpperBoundChecked e I c = true) :
    ∀ x ∈ I, Expr.eval (fun _ => x) e ≤ c := by
  simp only [checkUpperBoundChecked] at h_cert
  split at h_cert
  · next J hsome =>
    simp only [decide_eq_true_eq] at h_cert
    exact evalInterval?_le_of_hi e I J c hsome h_cert
  · simp at h_cert

/-- Verification theorem for lower bounds with arbitrary expressions. -/
theorem verify_lower_bound_checked (e : Expr)
    (I : IntervalRat) (c : ℚ)
    (h_cert : checkLowerBoundChecked e I c = true) :
    ∀ x ∈ I, c ≤ Expr.eval (fun _ => x) e := by
  simp only [checkLowerBoundChecked] at h_cert
  split at h_cert
  · next J hsome =>
    simp only [decide_eq_true_eq] at h_cert
    exact evalInterval?_ge_of_lo e I J c hsome h_cert
  · simp at h_cert

/-- Verification theorem for strict upper bounds with arbitrary expressions. -/
theorem verify_strict_upper_bound_checked (e : Expr)
    (I : IntervalRat) (c : ℚ)
    (h_cert : checkStrictUpperBoundChecked e I c = true) :
    ∀ x ∈ I, Expr.eval (fun _ => x) e < c := by
  simp only [checkStrictUpperBoundChecked] at h_cert
  split at h_cert
  · next J hsome =>
    simp only [decide_eq_true_eq] at h_cert
    intro x hx
    have hle := evalInterval?_le_of_hi e I J J.hi hsome (le_refl _) x hx
    have hJ_hi : Expr.eval (fun _ => x) e ≤ J.hi := hle
    calc Expr.eval (fun _ => x) e ≤ J.hi := hJ_hi
      _ < c := by exact_mod_cast h_cert
  · simp at h_cert

/-- Verification theorem for strict lower bounds with arbitrary expressions. -/
theorem verify_strict_lower_bound_checked (e : Expr)
    (I : IntervalRat) (c : ℚ)
    (h_cert : checkStrictLowerBoundChecked e I c = true) :
    ∀ x ∈ I, c < Expr.eval (fun _ => x) e := by
  simp only [checkStrictLowerBoundChecked] at h_cert
  split at h_cert
  · next J hsome =>
    simp only [decide_eq_true_eq] at h_cert
    intro x hx
    have hge := evalInterval?_ge_of_lo e I J J.lo hsome (le_refl _) x hx
    have hJ_lo : (J.lo : ℝ) ≤ Expr.eval (fun _ => x) e := hge
    have hc_lt_lo : (c : ℝ) < (J.lo : ℝ) := by exact_mod_cast h_cert
    exact lt_of_lt_of_le hc_lt_lo hJ_lo
  · simp at h_cert

/-! ### Set.Icc Bridge Theorems for arbitrary expressions -/

/-- Bridge theorem for Set.Icc upper bounds with arbitrary expressions. -/
theorem verify_upper_bound_Icc_checked (e : Expr)
    (lo hi : ℚ) (hle : lo ≤ hi) (c : ℚ)
    (h_cert : checkUpperBoundChecked e ⟨lo, hi, hle⟩ c = true) :
    ∀ x ∈ Set.Icc (lo : ℝ) (hi : ℝ), Expr.eval (fun _ => x) e ≤ c := by
  intro x hx
  have := verify_upper_bound_checked e ⟨lo, hi, hle⟩ c h_cert
  apply this
  rwa [IntervalRat.mem_iff_mem_Icc]

/-- Bridge theorem for Set.Icc lower bounds with arbitrary expressions. -/
theorem verify_lower_bound_Icc_checked (e : Expr)
    (lo hi : ℚ) (hle : lo ≤ hi) (c : ℚ)
    (h_cert : checkLowerBoundChecked e ⟨lo, hi, hle⟩ c = true) :
    ∀ x ∈ Set.Icc (lo : ℝ) (hi : ℝ), c ≤ Expr.eval (fun _ => x) e := by
  intro x hx
  have := verify_lower_bound_checked e ⟨lo, hi, hle⟩ c h_cert
  apply this
  rwa [IntervalRat.mem_iff_mem_Icc]

/-- Bridge theorem for Set.Icc strict upper bounds with arbitrary expressions. -/
theorem verify_strict_upper_bound_Icc_checked (e : Expr)
    (lo hi : ℚ) (hle : lo ≤ hi) (c : ℚ)
    (h_cert : checkStrictUpperBoundChecked e ⟨lo, hi, hle⟩ c = true) :
    ∀ x ∈ Set.Icc (lo : ℝ) (hi : ℝ), Expr.eval (fun _ => x) e < c := by
  intro x hx
  have := verify_strict_upper_bound_checked e ⟨lo, hi, hle⟩ c h_cert
  apply this
  rwa [IntervalRat.mem_iff_mem_Icc]

/-- Bridge theorem for Set.Icc strict lower bounds with arbitrary expressions. -/
theorem verify_strict_lower_bound_Icc_checked (e : Expr)
    (lo hi : ℚ) (hle : lo ≤ hi) (c : ℚ)
    (h_cert : checkStrictLowerBoundChecked e ⟨lo, hi, hle⟩ c = true) :
    ∀ x ∈ Set.Icc (lo : ℝ) (hi : ℝ), c < Expr.eval (fun _ => x) e := by
  intro x hx
  have := verify_strict_lower_bound_checked e ⟨lo, hi, hle⟩ c h_cert
  apply this
  rwa [IntervalRat.mem_iff_mem_Icc]

end LeanCert.Validity
