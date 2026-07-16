/-
Copyright (c) 2024 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Engine.IntervalEvalAffine

/-!
# Certificate-Driven Verification with Affine Arithmetic

This file provides Golden Theorems for the Affine arithmetic backend, enabling
certificate-driven verification with tighter bounds than standard interval arithmetic.

## Overview

Affine arithmetic solves the "dependency problem" in interval arithmetic by tracking
linear correlations between variables. For example:
- Standard IA: `x - x` on `[-1, 1]` gives `[-2, 2]`
- Affine AA: `x - x` on `[-1, 1]` gives `[0, 0]`

This is particularly valuable for neural network verification where the same input
variable flows through multiple paths.

## Main definitions

### Boolean Checkers
* `checkUpperBoundAffine1` - Check if computed upper bound is ≤ c for single variable
* `checkLowerBoundAffine1` - Check if computed lower bound is ≥ c for single variable
* `checkUpperBoundAffine1Strict` - Strict checker that rejects unsupported/domain-invalid cases
* `checkLowerBoundAffine1Strict` - Strict lower-bound checker

### Golden Theorems
* `verify_upper_bound_affine1` - Single-variable upper bound verification
* `verify_lower_bound_affine1` - Single-variable lower bound verification
* `verify_upper_bound_affine1_strict` - Upper bound verification from the strict checker
* `verify_lower_bound_affine1_strict` - Lower bound verification from the strict checker

For `ADSupported` expressions (no log), convenience versions are provided.

## Design

The Affine backend represents values as:
  `x̂ = c₀ + Σᵢ cᵢ·εᵢ + [-r, r]`

where `εᵢ ∈ [-1, 1]` are noise symbols tracking input correlations.

## Trust Hierarchy

This provides an alternative verification path to both:
- `Validity/Bounds.lean` (rational interval arithmetic)
- `Validity/DyadicBounds.lean` (dyadic interval arithmetic)

Affine arithmetic typically gives the tightest bounds but is computationally more
expensive. Use it when standard interval arithmetic is too conservative.
-/

namespace LeanCert.Validity

open LeanCert.Core
open LeanCert.Engine
open LeanCert.Engine.Affine

/-! ### Single-Variable Boolean Checkers -/

/-- Create an affine environment where ALL variables map to the same interval.
    This mirrors the pattern of `fun _ => I` used in standard interval arithmetic. -/
def toAffineEnvConst (I : IntervalRat) : AffineEnv :=
  fun _ => AffineForm.ofInterval I 0 1

/-- Check if an expression's computed upper bound is ≤ c using Affine arithmetic.
    This uses a single-variable setup where all variables map to the same interval. -/
def checkUpperBoundAffine1 (e : Expr) (I : IntervalRat) (c : ℚ) (cfg : AffineConfig := {}) : Bool :=
  let ρ := toAffineEnvConst I
  (LeanCert.Internal.Affine.evalUnchecked e ρ cfg).toInterval.hi ≤ c

/-- Check if an expression's computed lower bound is ≥ c using Affine arithmetic. -/
def checkLowerBoundAffine1 (e : Expr) (I : IntervalRat) (c : ℚ) (cfg : AffineConfig := {}) : Bool :=
  let ρ := toAffineEnvConst I
  c ≤ (LeanCert.Internal.Affine.evalUnchecked e ρ cfg).toInterval.lo

/-- Boolean affine domain-validity checker.

This mirrors `evalDomainValidAffine`, but produces executable data for
certificate checkers. -/
def checkDomainValidAffine (e : Expr) (ρ : AffineEnv) (cfg : AffineConfig := {}) : Bool :=
  match e with
  | Expr.const _ => true
  | Expr.var _ => true
  | Expr.add e₁ e₂ => checkDomainValidAffine e₁ ρ cfg && checkDomainValidAffine e₂ ρ cfg
  | Expr.mul e₁ e₂ => checkDomainValidAffine e₁ ρ cfg && checkDomainValidAffine e₂ ρ cfg
  | Expr.neg e => checkDomainValidAffine e ρ cfg
  | Expr.inv e => checkDomainValidAffine e ρ cfg
  | Expr.exp e => checkDomainValidAffine e ρ cfg
  | Expr.sin e => checkDomainValidAffine e ρ cfg
  | Expr.cos e => checkDomainValidAffine e ρ cfg
  | Expr.log e =>
      checkDomainValidAffine e ρ cfg &&
        decide (0 < (LeanCert.Internal.Affine.evalUnchecked e ρ cfg).toInterval.lo)
  | Expr.atan e => checkDomainValidAffine e ρ cfg
  | Expr.arsinh e => checkDomainValidAffine e ρ cfg
  | Expr.atanh e => checkDomainValidAffine e ρ cfg
  | Expr.sinc e => checkDomainValidAffine e ρ cfg
  | Expr.erf e => checkDomainValidAffine e ρ cfg
  | Expr.sinh e => checkDomainValidAffine e ρ cfg
  | Expr.cosh e => checkDomainValidAffine e ρ cfg
  | Expr.tanh e => checkDomainValidAffine e ρ cfg
  | Expr.sqrt e => checkDomainValidAffine e ρ cfg
  | Expr.namedConst _ => true

/-- Strict affine upper-bound checker.

This rejects expressions that the strict affine evaluator does not accept and
checks affine domain validity as part of the executable certificate. The bound
itself is still computed with the legacy affine evaluator so existing affine
correctness theorems apply directly once the Boolean check succeeds. -/
def checkUpperBoundAffine1Strict
    (e : Expr) (I : IntervalRat) (c : ℚ) (cfg : AffineConfig := {}) : Bool :=
  let ρ := toAffineEnvConst I
  match evalAffineToInterval? e ρ cfg with
  | none => false
  | some _ =>
      if checkDomainValidAffine e ρ cfg then
        (LeanCert.Internal.Affine.evalUnchecked e ρ cfg).toInterval.hi ≤ c
      else
        false

/-- Strict affine lower-bound checker. -/
def checkLowerBoundAffine1Strict
    (e : Expr) (I : IntervalRat) (c : ℚ) (cfg : AffineConfig := {}) : Bool :=
  let ρ := toAffineEnvConst I
  match evalAffineToInterval? e ρ cfg with
  | none => false
  | some _ =>
      if checkDomainValidAffine e ρ cfg then
        c ≤ (LeanCert.Internal.Affine.evalUnchecked e ρ cfg).toInterval.lo
      else
        false

/-! ### Helper Lemmas for Single-Variable Affine Proofs -/

/-- The executable affine domain checker implies the Prop-valued domain predicate. -/
theorem checkDomainValidAffine_correct {e : Expr} {ρ : AffineEnv} {cfg : AffineConfig}
    (h : checkDomainValidAffine e ρ cfg = true) :
    evalDomainValidAffine e ρ cfg := by
  induction e with
  | const q => trivial
  | var idx => trivial
  | add e₁ e₂ ih₁ ih₂ =>
      simp [checkDomainValidAffine, evalDomainValidAffine] at h ⊢
      exact ⟨ih₁ h.1, ih₂ h.2⟩
  | mul e₁ e₂ ih₁ ih₂ =>
      simp [checkDomainValidAffine, evalDomainValidAffine] at h ⊢
      exact ⟨ih₁ h.1, ih₂ h.2⟩
  | neg e ih
  | inv e ih
  | exp e ih
  | sin e ih
  | cos e ih
  | atan e ih
  | arsinh e ih
  | atanh e ih
  | sinc e ih
  | erf e ih
  | sinh e ih
  | cosh e ih
  | tanh e ih
  | sqrt e ih =>
      simp [checkDomainValidAffine, evalDomainValidAffine] at h ⊢
      exact ih h
  | log e ih =>
      simp [checkDomainValidAffine, evalDomainValidAffine] at h ⊢
      exact ⟨ih h.1, h.2⟩
  | namedConst c => trivial

/-- For x ∈ I, |x - mid(I)| ≤ rad(I) -/
private lemma abs_sub_mid_le_rad {x : ℝ} {I : IntervalRat} (hx : x ∈ I) :
    |x - ((I.lo + I.hi) / 2 : ℚ)| ≤ ((I.hi - I.lo) / 2 : ℚ) := by
  have hx' : (I.lo : ℝ) ≤ x ∧ x ≤ I.hi := by
    simpa [IntervalRat.mem_def] using hx
  rw [abs_le]
  constructor
  · calc -((((I.hi : ℚ) - I.lo) / 2 : ℚ) : ℝ)
        = (I.lo : ℝ) - ((I.lo : ℝ) + I.hi) / 2 := by push_cast; ring
      _ ≤ x - ((I.lo : ℝ) + I.hi) / 2 := by linarith [hx'.1]
      _ = x - ((((I.lo : ℚ) + I.hi) / 2 : ℚ) : ℝ) := by push_cast; ring
  · calc x - ((((I.lo : ℚ) + I.hi) / 2 : ℚ) : ℝ)
        = x - ((I.lo : ℝ) + I.hi) / 2 := by push_cast; ring
      _ ≤ (I.hi : ℝ) - ((I.lo : ℝ) + I.hi) / 2 := by linarith [hx'.2]
      _ = ((((I.hi : ℚ) - I.lo) / 2 : ℚ) : ℝ) := by push_cast; ring

/-- Create the canonical noise assignment for a single variable x in interval I -/
private noncomputable def mkNoise1 (I : IntervalRat) (x : ℝ) : AffineForm.NoiseAssignment :=
  let mid := ((I.lo + I.hi) / 2 : ℚ)
  let rad := ((I.hi - I.lo) / 2 : ℚ)
  let eps0 : ℝ := if (rad : ℝ) = 0 then 0 else (x - mid) / rad
  List.singleton eps0

/-- The single-variable noise assignment is valid when x ∈ I -/
private theorem mkNoise1_valid (I : IntervalRat) (x : ℝ) (hx : x ∈ I) :
    AffineForm.validNoise (mkNoise1 I x) := by
  intro e he
  simp only [mkNoise1, List.singleton] at he
  rw [List.mem_singleton] at he
  subst he
  set mid := ((I.lo + I.hi) / 2 : ℚ) with hmid_def
  set rad := ((I.hi - I.lo) / 2 : ℚ) with hrad_def
  split_ifs with hr
  · -- rad = 0 case: eps = 0
    constructor <;> linarith
  · -- rad ≠ 0 case: need to show (x - mid) / rad ∈ [-1, 1]
    have habs := abs_sub_mid_le_rad hx
    have hrad_nonneg : (0 : ℝ) ≤ rad := by
      have hI := I.le
      have h : (0 : ℚ) ≤ (I.hi - I.lo) / 2 := by linarith
      exact_mod_cast h
    have hrad_pos : (0 : ℝ) < rad := lt_of_le_of_ne hrad_nonneg (Ne.symm hr)
    constructor
    · have h1 : -(rad : ℝ) ≤ x - mid := by rw [abs_le] at habs; exact habs.1
      calc -1 = -(rad : ℝ) / rad := by field_simp
        _ ≤ (x - mid) / rad := div_le_div_of_nonneg_right h1 (le_of_lt hrad_pos)
    · have h1 : x - mid ≤ rad := by rw [abs_le] at habs; exact habs.2
      calc (x - mid) / rad ≤ (rad : ℝ) / rad := div_le_div_of_nonneg_right h1 (le_of_lt hrad_pos)
        _ = 1 := by field_simp

/-- linearSum of a singleton list -/
private lemma linearSum_singleton (c : ℚ) (e : ℝ) :
    AffineForm.linearSum [c] [e] = (c : ℝ) * e := by
  simp only [AffineForm.linearSum, List.zipWith_cons_cons, List.zipWith_nil_right,
    List.sum_cons, List.sum_nil, add_zero]

/-- The real value x is represented by the affine form from toAffineEnvConst I -/
private theorem mkNoise1_envMem (I : IntervalRat) (x : ℝ) (hx : x ∈ I) :
    envMemAffine (fun _ => x) (toAffineEnvConst I) (mkNoise1 I x) := by
  intro i
  -- All variables map to the same affine form: AffineForm.ofInterval I 0 1
  simp only [toAffineEnvConst]
  simp only [AffineForm.mem_affine, AffineForm.ofInterval, AffineForm.evalLinear]
  set mid := ((I.lo + I.hi) / 2 : ℚ) with hmid_def
  set rad := ((I.hi - I.lo) / 2 : ℚ) with hrad_def
  use 0
  constructor
  · norm_num
  · simp only [add_zero]
    -- coeffs = [rad] (single element: rad at index 0 since totalVars=1)
    simp only [List.ofFn_succ, Fin.val_zero, Fin.isValue, ↓reduceIte, List.ofFn_zero]
    -- Now we need: x = mid + linearSum [rad] [mkNoise1 I x]
    simp only [mkNoise1, List.singleton]
    split_ifs with hr
    · -- rad = 0: x = mid
      rw [linearSum_singleton]
      simp only [mul_zero, add_zero]
      have habs := abs_sub_mid_le_rad hx
      rw [abs_le] at habs
      have hle : x - mid ≤ 0 := by linarith [habs.2, hr]
      have hge : 0 ≤ x - mid := by linarith [habs.1, hr]
      linarith
    · -- rad ≠ 0: x = mid + rad * (x - mid) / rad
      rw [linearSum_singleton]
      have hrad_ne : (rad : ℝ) ≠ 0 := hr
      field_simp [hrad_ne]
      ring

/-! ### Golden Theorems for Single-Variable Affine Bounds -/

/-- **Golden Theorem for Affine Upper Bounds (Single Variable)**

    If `checkUpperBoundAffine1 e I c cfg = true` and domain validity holds, then
    `∀ x ∈ I, Expr.eval (fun _ => x) e ≤ c`.

    This is the key theorem for certificate-driven verification using Affine arithmetic.
    The tighter bounds from affine arithmetic enable proving inequalities that are
    too loose for standard interval arithmetic. -/
theorem verify_upper_bound_affine1 (e : Expr) (hsupp : ExprSupportedCore e)
    (I : IntervalRat) (c : ℚ) (cfg : AffineConfig)
    (hdom : evalDomainValidAffine e (toAffineEnvConst I) cfg)
    (h_check : checkUpperBoundAffine1 e I c cfg = true) :
    ∀ x ∈ I, Expr.eval (fun _ => x) e ≤ c := by
  intro x hx
  let ρ_real : Nat → ℝ := fun _ => x
  let ρ_affine := toAffineEnvConst I
  let eps := mkNoise1 I x
  -- Prove noise validity
  have hvalid : AffineForm.validNoise eps := mkNoise1_valid I x hx
  -- Prove environment membership
  have henv : envMemAffine ρ_real ρ_affine eps := mkNoise1_envMem I x hx
  -- Apply correctness theorem to get affine membership
  have hmem_affine := evalIntervalAffine_correct e hsupp ρ_real ρ_affine eps hvalid henv cfg hdom
  -- Use mem_toInterval_weak (no length constraint needed)
  have hmem := AffineForm.mem_toInterval_weak hvalid hmem_affine
  -- Extract upper bound from boolean check
  simp only [checkUpperBoundAffine1, decide_eq_true_eq] at h_check
  -- Combine membership and bound check
  have hhi := hmem.2
  calc Expr.eval (fun _ => x) e
      ≤ ((LeanCert.Internal.Affine.evalUnchecked e ρ_affine cfg).toInterval.hi : ℝ) := hhi
    _ ≤ c := by exact_mod_cast h_check

/-- **Golden Theorem for Affine Lower Bounds (Single Variable)** -/
theorem verify_lower_bound_affine1 (e : Expr) (hsupp : ExprSupportedCore e)
    (I : IntervalRat) (c : ℚ) (cfg : AffineConfig)
    (hdom : evalDomainValidAffine e (toAffineEnvConst I) cfg)
    (h_check : checkLowerBoundAffine1 e I c cfg = true) :
    ∀ x ∈ I, c ≤ Expr.eval (fun _ => x) e := by
  intro x hx
  let ρ_real : Nat → ℝ := fun _ => x
  let ρ_affine := toAffineEnvConst I
  let eps := mkNoise1 I x
  have hvalid : AffineForm.validNoise eps := mkNoise1_valid I x hx
  have henv : envMemAffine ρ_real ρ_affine eps := mkNoise1_envMem I x hx
  have hmem_affine := evalIntervalAffine_correct e hsupp ρ_real ρ_affine eps hvalid henv cfg hdom
  have hmem := AffineForm.mem_toInterval_weak hvalid hmem_affine
  simp only [checkLowerBoundAffine1, decide_eq_true_eq] at h_check
  have hlo := hmem.1
  calc (c : ℝ)
      ≤ ((LeanCert.Internal.Affine.evalUnchecked e ρ_affine cfg).toInterval.lo : ℝ) := by exact_mod_cast h_check
    _ ≤ Expr.eval (fun _ => x) e := hlo

/-! ### Strict Affine Checkers -/

/-- Strict affine upper-bound verification.

Compared with `verify_upper_bound_affine1`, the domain-validity obligation is
part of the Boolean checker. The strict checker also rejects expressions whose
strict affine evaluator returns `none`. -/
theorem verify_upper_bound_affine1_strict (e : Expr) (hsupp : ExprSupportedCore e)
    (I : IntervalRat) (c : ℚ) (cfg : AffineConfig)
    (h_check : checkUpperBoundAffine1Strict e I c cfg = true) :
    ∀ x ∈ I, Expr.eval (fun _ => x) e ≤ c := by
  unfold checkUpperBoundAffine1Strict at h_check
  cases hstrict : evalAffineToInterval? e (toAffineEnvConst I) cfg with
  | none =>
      simp [hstrict] at h_check
  | some J =>
      simp [hstrict] at h_check
      have hdom := checkDomainValidAffine_correct h_check.1
      intro x hx
      let ρ_real : Nat → ℝ := fun _ => x
      let ρ_affine := toAffineEnvConst I
      let eps := mkNoise1 I x
      have hvalid : AffineForm.validNoise eps := mkNoise1_valid I x hx
      have henv : envMemAffine ρ_real ρ_affine eps := mkNoise1_envMem I x hx
      have hmem_affine :=
        evalIntervalAffine_correct e hsupp ρ_real ρ_affine eps hvalid henv cfg hdom
      have hmem := AffineForm.mem_toInterval_weak hvalid hmem_affine
      calc Expr.eval (fun _ => x) e
          ≤ ((LeanCert.Internal.Affine.evalUnchecked e ρ_affine cfg).toInterval.hi : ℝ) := hmem.2
        _ ≤ c := by exact_mod_cast h_check.2

/-- Strict affine lower-bound verification. -/
theorem verify_lower_bound_affine1_strict (e : Expr) (hsupp : ExprSupportedCore e)
    (I : IntervalRat) (c : ℚ) (cfg : AffineConfig)
    (h_check : checkLowerBoundAffine1Strict e I c cfg = true) :
    ∀ x ∈ I, c ≤ Expr.eval (fun _ => x) e := by
  unfold checkLowerBoundAffine1Strict at h_check
  cases hstrict : evalAffineToInterval? e (toAffineEnvConst I) cfg with
  | none =>
      simp [hstrict] at h_check
  | some J =>
      simp [hstrict] at h_check
      have hdom := checkDomainValidAffine_correct h_check.1
      intro x hx
      let ρ_real : Nat → ℝ := fun _ => x
      let ρ_affine := toAffineEnvConst I
      let eps := mkNoise1 I x
      have hvalid : AffineForm.validNoise eps := mkNoise1_valid I x hx
      have henv : envMemAffine ρ_real ρ_affine eps := mkNoise1_envMem I x hx
      have hmem_affine :=
        evalIntervalAffine_correct e hsupp ρ_real ρ_affine eps hvalid henv cfg hdom
      have hmem := AffineForm.mem_toInterval_weak hvalid hmem_affine
      calc (c : ℝ)
          ≤ ((LeanCert.Internal.Affine.evalUnchecked e ρ_affine cfg).toInterval.lo : ℝ) := by
              exact_mod_cast h_check.2
        _ ≤ Expr.eval (fun _ => x) e := hmem.1

/-! ### Convenience Theorems for ADSupported

For expressions that don't use `log`, domain validity is automatic. -/

/-- Convenience theorem for ADSupported expressions (no log).
    Domain validity is automatic, so only the bound check is needed. -/
theorem verify_upper_bound_affine1' (e : Expr) (hsupp : ADSupported e)
    (I : IntervalRat) (c : ℚ) (cfg : AffineConfig)
    (h_check : checkUpperBoundAffine1 e I c cfg = true) :
    ∀ x ∈ I, Expr.eval (fun _ => x) e ≤ c := by
  have hdom : evalDomainValidAffine e (toAffineEnvConst I) cfg :=
    evalDomainValidAffine_of_ExprSupported hsupp _ _
  exact verify_upper_bound_affine1 e hsupp.toCore I c cfg hdom h_check

/-- Convenience theorem for ADSupported expressions (no log). -/
theorem verify_lower_bound_affine1' (e : Expr) (hsupp : ADSupported e)
    (I : IntervalRat) (c : ℚ) (cfg : AffineConfig)
    (h_check : checkLowerBoundAffine1 e I c cfg = true) :
    ∀ x ∈ I, c ≤ Expr.eval (fun _ => x) e := by
  have hdom : evalDomainValidAffine e (toAffineEnvConst I) cfg :=
    evalDomainValidAffine_of_ExprSupported hsupp _ _
  exact verify_lower_bound_affine1 e hsupp.toCore I c cfg hdom h_check

end LeanCert.Validity
