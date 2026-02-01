/-
Copyright (c) 2024 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Engine.IntervalEval

/-!
# Core Bound Verification

This module provides the fundamental infrastructure for certificate-driven verification of
numerical bounds using interval arithmetic.

## Main definitions

### Boolean Checkers
* `checkUpperBound` - Check if `∀ x ∈ I, f(x) ≤ c` via interval arithmetic
* `checkLowerBound` - Check if `∀ x ∈ I, c ≤ f(x)` via interval arithmetic
* `checkStrictUpperBound` - Check if `∀ x ∈ I, f(x) < c`
* `checkStrictLowerBound` - Check if `∀ x ∈ I, c < f(x)`

### Golden Theorems
* `verify_upper_bound` - Converts `checkUpperBound = true` to semantic proof
* `verify_lower_bound` - Converts `checkLowerBound = true` to semantic proof
* `verify_strict_upper_bound` - Converts `checkStrictUpperBound = true` to semantic proof
* `verify_strict_lower_bound` - Converts `checkStrictLowerBound = true` to semantic proof
-/

namespace LeanCert.Validity

open LeanCert.Core
open LeanCert.Engine

/-! ### Boolean Checkers

These are the functions `native_decide` will execute. They return `Bool`, not `Prop`.
-/

/-- Check if an expression is bounded above by `c` on interval `I`.
    Returns `true` iff domain validity holds AND the computed upper bound is ≤ c. -/
def checkUpperBound (e : Expr) (I : IntervalRat) (c : ℚ) (cfg : EvalConfig) : Bool :=
  checkDomainValid1 e I cfg && decide ((evalIntervalCore1 e I cfg).hi ≤ c)

/-- Check if an expression is bounded below by `c` on interval `I`.
    Returns `true` iff domain validity holds AND the computed lower bound is ≥ c. -/
def checkLowerBound (e : Expr) (I : IntervalRat) (c : ℚ) (cfg : EvalConfig) : Bool :=
  checkDomainValid1 e I cfg && decide (c ≤ (evalIntervalCore1 e I cfg).lo)

/-- Check if an expression is strictly bounded above by `c` on interval `I`.
    Returns `true` iff domain validity holds AND the computed upper bound is < c. -/
def checkStrictUpperBound (e : Expr) (I : IntervalRat) (c : ℚ) (cfg : EvalConfig) : Bool :=
  checkDomainValid1 e I cfg && decide ((evalIntervalCore1 e I cfg).hi < c)

/-- Check if an expression is strictly bounded below by `c` on interval `I`.
    Returns `true` iff domain validity holds AND the computed lower bound is > c. -/
def checkStrictLowerBound (e : Expr) (I : IntervalRat) (c : ℚ) (cfg : EvalConfig) : Bool :=
  checkDomainValid1 e I cfg && decide (c < (evalIntervalCore1 e I cfg).lo)

/-! ### Golden Theorems

These theorems convert the boolean `true` from the checkers into semantic proofs
about Real numbers. They are the theorems a tactic will `apply`.
-/

/-- **Golden Theorem for Upper Bounds**

    If `checkUpperBound e I c cfg = true`, then `∀ x ∈ I, Expr.eval (fun _ => x) e ≤ c`. -/
theorem verify_upper_bound (e : Expr) (hsupp : ExprSupportedCore e)
    (I : IntervalRat) (c : ℚ) (cfg : EvalConfig)
    (h_cert : checkUpperBound e I c cfg = true) :
    ∀ x ∈ I, Expr.eval (fun _ => x) e ≤ c := by
  simp only [checkUpperBound, Bool.and_eq_true, decide_eq_true_eq] at h_cert
  have hdom := checkDomainValid1_correct e I cfg h_cert.1
  have hhi := h_cert.2
  exact exprCore_le_of_interval_hi e hsupp I c cfg hdom hhi

/-- **Golden Theorem for Lower Bounds**

    If `checkLowerBound e I c cfg = true`, then `∀ x ∈ I, c ≤ Expr.eval (fun _ => x) e`. -/
theorem verify_lower_bound (e : Expr) (hsupp : ExprSupportedCore e)
    (I : IntervalRat) (c : ℚ) (cfg : EvalConfig)
    (h_cert : checkLowerBound e I c cfg = true) :
    ∀ x ∈ I, c ≤ Expr.eval (fun _ => x) e := by
  simp only [checkLowerBound, Bool.and_eq_true, decide_eq_true_eq] at h_cert
  have hdom := checkDomainValid1_correct e I cfg h_cert.1
  have hlo := h_cert.2
  exact exprCore_ge_of_interval_lo e hsupp I c cfg hdom hlo

/-- **Golden Theorem for Strict Upper Bounds**

    If `checkStrictUpperBound e I c cfg = true`, then `∀ x ∈ I, Expr.eval (fun _ => x) e < c`. -/
theorem verify_strict_upper_bound (e : Expr) (hsupp : ExprSupportedCore e)
    (I : IntervalRat) (c : ℚ) (cfg : EvalConfig)
    (h_cert : checkStrictUpperBound e I c cfg = true) :
    ∀ x ∈ I, Expr.eval (fun _ => x) e < c := by
  simp only [checkStrictUpperBound, Bool.and_eq_true, decide_eq_true_eq] at h_cert
  have hdom := checkDomainValid1_correct e I cfg h_cert.1
  have hhi := h_cert.2
  exact exprCore_lt_of_interval_hi_lt e hsupp I c cfg hdom hhi

/-- **Golden Theorem for Strict Lower Bounds**

    If `checkStrictLowerBound e I c cfg = true`, then `∀ x ∈ I, c < Expr.eval (fun _ => x) e`. -/
theorem verify_strict_lower_bound (e : Expr) (hsupp : ExprSupportedCore e)
    (I : IntervalRat) (c : ℚ) (cfg : EvalConfig)
    (h_cert : checkStrictLowerBound e I c cfg = true) :
    ∀ x ∈ I, c < Expr.eval (fun _ => x) e := by
  simp only [checkStrictLowerBound, Bool.and_eq_true, decide_eq_true_eq] at h_cert
  have hdom := checkDomainValid1_correct e I cfg h_cert.1
  have hlo := h_cert.2
  exact exprCore_gt_of_interval_lo_gt e hsupp I c cfg hdom hlo

/-! ### Convenience lemmas for pointwise bounds -/

/-- Pointwise upper bound: if check passes and x ∈ I, then f(x) ≤ c -/
theorem verify_upper_bound_pt (e : Expr) (hsupp : ExprSupportedCore e)
    (I : IntervalRat) (c : ℚ) (cfg : EvalConfig) (x : ℝ) (hx : x ∈ I)
    (h_cert : checkUpperBound e I c cfg = true) :
    Expr.eval (fun _ => x) e ≤ c :=
  verify_upper_bound e hsupp I c cfg h_cert x hx

/-- Pointwise lower bound: if check passes and x ∈ I, then c ≤ f(x) -/
theorem verify_lower_bound_pt (e : Expr) (hsupp : ExprSupportedCore e)
    (I : IntervalRat) (c : ℚ) (cfg : EvalConfig) (x : ℝ) (hx : x ∈ I)
    (h_cert : checkLowerBound e I c cfg = true) :
    c ≤ Expr.eval (fun _ => x) e :=
  verify_lower_bound e hsupp I c cfg h_cert x hx

/-! ### Two-sided bounds -/

/-- Check both lower and upper bounds simultaneously -/
def checkBounds (e : Expr) (I : IntervalRat) (lo hi : ℚ) (cfg : EvalConfig) : Bool :=
  checkLowerBound e I lo cfg && checkUpperBound e I hi cfg

/-- Two-sided bound verification: if both checks pass, then lo ≤ f(x) ≤ hi for all x ∈ I -/
theorem verify_bounds (e : Expr) (hsupp : ExprSupportedCore e)
    (I : IntervalRat) (lo hi : ℚ) (cfg : EvalConfig)
    (h_cert : checkBounds e I lo hi cfg = true) :
    ∀ x ∈ I, lo ≤ Expr.eval (fun _ => x) e ∧ Expr.eval (fun _ => x) e ≤ hi := by
  simp only [checkBounds, Bool.and_eq_true] at h_cert
  intro x hx
  exact ⟨verify_lower_bound e hsupp I lo cfg h_cert.1 x hx,
         verify_upper_bound e hsupp I hi cfg h_cert.2 x hx⟩

/-! ### Argmax/Argmin Verification -/

/-- Check that evaluating f at a point x gives a value ≥ c. -/
def checkPointLowerBound (e : Expr) (x c : ℚ) (cfg : EvalConfig) : Bool :=
  let Ipt : IntervalRat := ⟨x, x, le_refl x⟩
  checkDomainValid1 e Ipt cfg && decide (c ≤ (evalIntervalCore1 e Ipt cfg).lo)

/-- Check that evaluating f at a point x gives a value ≤ c. -/
def checkPointUpperBound (e : Expr) (x c : ℚ) (cfg : EvalConfig) : Bool :=
  let Ipt : IntervalRat := ⟨x, x, le_refl x⟩
  checkDomainValid1 e Ipt cfg && decide ((evalIntervalCore1 e Ipt cfg).hi ≤ c)

/-- Verify that c ≤ f(x) at a specific point x. -/
theorem verify_point_lower_bound (e : Expr) (hsupp : ExprSupportedCore e)
    (x c : ℚ) (cfg : EvalConfig)
    (h_cert : checkPointLowerBound e x c cfg = true) :
    c ≤ Expr.eval (fun _ => (x : ℝ)) e := by
  simp only [checkPointLowerBound, Bool.and_eq_true, decide_eq_true_eq] at h_cert
  let Ipt : IntervalRat := ⟨x, x, le_refl x⟩
  have hdom := checkDomainValid1_correct e Ipt cfg h_cert.1
  have hlo := h_cert.2
  have hx_mem : (x : ℝ) ∈ Ipt := ⟨le_refl _, le_refl _⟩
  exact exprCore_ge_of_interval_lo e hsupp Ipt c cfg hdom hlo (x : ℝ) hx_mem

/-- Verify that f(x) ≤ c at a specific point x. -/
theorem verify_point_upper_bound (e : Expr) (hsupp : ExprSupportedCore e)
    (x c : ℚ) (cfg : EvalConfig)
    (h_cert : checkPointUpperBound e x c cfg = true) :
    Expr.eval (fun _ => (x : ℝ)) e ≤ c := by
  simp only [checkPointUpperBound, Bool.and_eq_true, decide_eq_true_eq] at h_cert
  let Ipt : IntervalRat := ⟨x, x, le_refl x⟩
  have hdom := checkDomainValid1_correct e Ipt cfg h_cert.1
  have hhi := h_cert.2
  have hx_mem : (x : ℝ) ∈ Ipt := ⟨le_refl _, le_refl _⟩
  exact exprCore_le_of_interval_hi e hsupp Ipt c cfg hdom hhi (x : ℝ) hx_mem

/-- **Argmax Verification Theorem**

    Proves `∀ y ∈ I, f(y) ≤ f(x)` (x is a maximizer) by:
    1. Checking that `∀ y ∈ I, f(y) ≤ c` (the max over I is at most c)
    2. Checking that `c ≤ f(x)` (the value at x is at least c) -/
theorem verify_argmax (e : Expr) (hsupp : ExprSupportedCore e)
    (I : IntervalRat) (x c : ℚ) (cfg : EvalConfig) (_hx : (x : ℝ) ∈ I)
    (h_upper : checkUpperBound e I c cfg = true)
    (h_point : checkPointLowerBound e x c cfg = true) :
    ∀ y ∈ I, Expr.eval (fun _ => y) e ≤ Expr.eval (fun _ => (x : ℝ)) e := by
  intro y hy
  have h1 : Expr.eval (fun _ => y) e ≤ c := verify_upper_bound e hsupp I c cfg h_upper y hy
  have h2 : c ≤ Expr.eval (fun _ => (x : ℝ)) e := verify_point_lower_bound e hsupp x c cfg h_point
  exact le_trans h1 h2

/-- **Argmin Verification Theorem**

    Proves `∀ y ∈ I, f(x) ≤ f(y)` (x is a minimizer). -/
theorem verify_argmin (e : Expr) (hsupp : ExprSupportedCore e)
    (I : IntervalRat) (x c : ℚ) (cfg : EvalConfig) (_hx : (x : ℝ) ∈ I)
    (h_lower : checkLowerBound e I c cfg = true)
    (h_point : checkPointUpperBound e x c cfg = true) :
    ∀ y ∈ I, Expr.eval (fun _ => (x : ℝ)) e ≤ Expr.eval (fun _ => y) e := by
  intro y hy
  have h1 : Expr.eval (fun _ => (x : ℝ)) e ≤ c := verify_point_upper_bound e hsupp x c cfg h_point
  have h2 : c ≤ Expr.eval (fun _ => y) e := verify_lower_bound e hsupp I c cfg h_lower y hy
  exact le_trans h1 h2

end LeanCert.Validity
