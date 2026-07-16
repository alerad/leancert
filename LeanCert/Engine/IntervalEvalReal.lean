/-
Copyright (c) 2024 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Core.Expr
import LeanCert.Core.IntervalRealEndpoints
import LeanCert.Engine.IntervalEval

/-!
# Interval Evaluation with Real Endpoints

This file implements interval evaluation using `IntervalReal` (real endpoints),
which allows us to support exp in a fully verified way.

## Main definitions

* `ExprSupportedExt` - Extended predicate for the real-endpoint evaluator
* `evalIntervalReal?` - Strict partial evaluator that rejects unsupported partial operations
* `evalIntervalReal?_correct` - Correctness theorem for successful evaluation

## Design notes

This extends the verified subset from {const, var, add, mul, neg, sin, cos}
to also include {exp}. The key insight is that with real endpoints, we can
use `Real.exp` directly and its monotonicity properties.

For numerical computation, users should still use `IntervalRat` and convert
to `IntervalReal` when they need to reason about exp. This keeps computation
efficient while allowing proofs about transcendental functions.
-/

namespace LeanCert.Engine

open LeanCert.Core

/-! ### Extended supported expression subset -/

/-- Predicate indicating an expression is in the extended verified subset.
    This includes total functions handled by `evalIntervalReal?`.
    Does NOT support: inv/log/atanh, which require domain checks. -/
inductive ExprSupportedExt : Expr → Prop where
  | const (q : ℚ) : ExprSupportedExt (Expr.const q)
  | var (idx : Nat) : ExprSupportedExt (Expr.var idx)
  | add {e₁ e₂ : Expr} : ExprSupportedExt e₁ → ExprSupportedExt e₂ →
      ExprSupportedExt (Expr.add e₁ e₂)
  | mul {e₁ e₂ : Expr} : ExprSupportedExt e₁ → ExprSupportedExt e₂ →
      ExprSupportedExt (Expr.mul e₁ e₂)
  | neg {e : Expr} : ExprSupportedExt e → ExprSupportedExt (Expr.neg e)
  | sin {e : Expr} : ExprSupportedExt e → ExprSupportedExt (Expr.sin e)
  | cos {e : Expr} : ExprSupportedExt e → ExprSupportedExt (Expr.cos e)
  | exp {e : Expr} : ExprSupportedExt e → ExprSupportedExt (Expr.exp e)
  | atan {e : Expr} : ExprSupportedExt e → ExprSupportedExt (Expr.atan e)
  | arsinh {e : Expr} : ExprSupportedExt e → ExprSupportedExt (Expr.arsinh e)
  | sinh {e : Expr} : ExprSupportedExt e → ExprSupportedExt (Expr.sinh e)
  | cosh {e : Expr} : ExprSupportedExt e → ExprSupportedExt (Expr.cosh e)
  | tanh {e : Expr} : ExprSupportedExt e → ExprSupportedExt (Expr.tanh e)
  | sqrt {e : Expr} : ExprSupportedExt e → ExprSupportedExt (Expr.sqrt e)
  | sinc {e : Expr} : ExprSupportedExt e → ExprSupportedExt (Expr.sinc e)
  | erf {e : Expr} : ExprSupportedExt e → ExprSupportedExt (Expr.erf e)
  | namedConst (c : MathConst) : ExprSupportedExt (Expr.namedConst c)

/-- The base supported subset is a subset of the extended one -/
theorem ADSupported.toExt {e : Expr} (h : ADSupported e) : ExprSupportedExt e := by
  induction h with
  | const q => exact ExprSupportedExt.const q
  | var idx => exact ExprSupportedExt.var idx
  | add _ _ ih₁ ih₂ => exact ExprSupportedExt.add ih₁ ih₂
  | mul _ _ ih₁ ih₂ => exact ExprSupportedExt.mul ih₁ ih₂
  | neg _ ih => exact ExprSupportedExt.neg ih
  | sin _ ih => exact ExprSupportedExt.sin ih
  | cos _ ih => exact ExprSupportedExt.cos ih
  | exp _ ih => exact ExprSupportedExt.exp ih

/-! ### Real-endpoint interval evaluation -/

/-- Variable assignment as real-endpoint intervals -/
abbrev IntervalRealEnv := Nat → IntervalReal

/-- Strict real-endpoint interval evaluator.

Returns `none` for unsupported partial operations (`inv`, `log`, `atanh`) and
for compound expressions whose required subexpression failed. Globally bounded
total functions such as `sinc`, `erf`, and `tanh` still return their global
range without requiring a refined subexpression interval.
-/
noncomputable def evalIntervalReal? (e : Expr) (ρ : IntervalRealEnv) : Option IntervalReal :=
  match e with
  | Expr.const q => some (IntervalReal.singleton q)
  | Expr.var idx => some (ρ idx)
  | Expr.add e₁ e₂ =>
      match evalIntervalReal? e₁ ρ, evalIntervalReal? e₂ ρ with
      | some I₁, some I₂ => some (IntervalReal.add I₁ I₂)
      | _, _ => none
  | Expr.mul e₁ e₂ =>
      match evalIntervalReal? e₁ ρ, evalIntervalReal? e₂ ρ with
      | some I₁, some I₂ => some (IntervalReal.mul I₁ I₂)
      | _, _ => none
  | Expr.neg e =>
      match evalIntervalReal? e ρ with
      | some I => some (IntervalReal.neg I)
      | none => none
  | Expr.inv _ => none
  | Expr.exp e =>
      match evalIntervalReal? e ρ with
      | some I => some (IntervalReal.expInterval I)
      | none => none
  | Expr.sin e =>
      match evalIntervalReal? e ρ with
      | some I => some (IntervalReal.sinInterval I)
      | none => none
  | Expr.cos e =>
      match evalIntervalReal? e ρ with
      | some I => some (IntervalReal.cosInterval I)
      | none => none
  | Expr.log _ => none
  | Expr.atan e =>
      match evalIntervalReal? e ρ with
      | some I => some (IntervalReal.atanInterval I)
      | none => none
  | Expr.arsinh e =>
      match evalIntervalReal? e ρ with
      | some I => some (IntervalReal.arsinhInterval I)
      | none => none
  | Expr.atanh _ => none
  | Expr.sinc _ => some ⟨-1, 1, by norm_num⟩
  | Expr.erf _ => some ⟨-1, 1, by norm_num⟩
  | Expr.sinh e =>
      match evalIntervalReal? e ρ with
      | some I => some (IntervalReal.sinhInterval I)
      | none => none
  | Expr.cosh e =>
      match evalIntervalReal? e ρ with
      | some I => some (IntervalReal.coshInterval I)
      | none => none
  | Expr.tanh _ => some ⟨-1, 1, by norm_num⟩
  | Expr.sqrt e =>
      match evalIntervalReal? e ρ with
      | some I => some (IntervalReal.sqrtInterval I)
      | none => none
  | Expr.namedConst c => some ⟨c.toReal, c.toReal, le_refl _⟩

/-- A real environment is contained in a real-interval environment -/
def envMemReal (ρ_real : Nat → ℝ) (ρ_int : IntervalRealEnv) : Prop :=
  ∀ i, ρ_real i ∈ ρ_int i

/-! ### Membership lemmas for IntervalReal operations -/

/-- Membership in singleton -/
theorem IntervalReal.mem_singleton' (r : ℝ) : r ∈ IntervalReal.singleton r := by
  simp only [IntervalReal.mem_def, IntervalReal.singleton]
  exact ⟨le_refl r, le_refl r⟩

/-- Membership for rational casts in singleton -/
theorem IntervalReal.mem_singleton_rat (q : ℚ) : (q : ℝ) ∈ IntervalReal.singleton q := by
  simp only [IntervalReal.mem_def, IntervalReal.singleton]
  constructor <;> exact le_refl _

/-- Helper: for x ∈ [a₁, a₂], x*y lies between endpoint products. -/
private theorem mul_mem_endpoints_left {x a₁ a₂ y : ℝ}
    (ha : a₁ ≤ x ∧ x ≤ a₂) :
    min (a₁ * y) (a₂ * y) ≤ x * y ∧ x * y ≤ max (a₁ * y) (a₂ * y) := by
  by_cases! hy : 0 ≤ y
  · have h1 : a₁ * y ≤ x * y := mul_le_mul_of_nonneg_right ha.1 hy
    have h2 : x * y ≤ a₂ * y := mul_le_mul_of_nonneg_right ha.2 hy
    constructor
    · exact le_trans (min_le_left _ _) h1
    · exact le_trans h2 (le_max_right _ _)
  · have hy' := le_of_lt hy
    have h1 : a₂ * y ≤ x * y := mul_le_mul_of_nonpos_right ha.2 hy'
    have h2 : x * y ≤ a₁ * y := mul_le_mul_of_nonpos_right ha.1 hy'
    constructor
    · exact le_trans (min_le_right _ _) h1
    · exact le_trans h2 (le_max_left _ _)

/-- Helper: for y ∈ [b₁, b₂], x*y lies between endpoint products. -/
private theorem mul_mem_endpoints_right {y b₁ b₂ x : ℝ}
    (hb : b₁ ≤ y ∧ y ≤ b₂) :
    min (x * b₁) (x * b₂) ≤ x * y ∧ x * y ≤ max (x * b₁) (x * b₂) := by
  by_cases! hx : 0 ≤ x
  · have h1 : x * b₁ ≤ x * y := mul_le_mul_of_nonneg_left hb.1 hx
    have h2 : x * y ≤ x * b₂ := mul_le_mul_of_nonneg_left hb.2 hx
    constructor
    · exact le_trans (min_le_left _ _) h1
    · exact le_trans h2 (le_max_right _ _)
  · have hx' := le_of_lt hx
    have h1 : x * b₂ ≤ x * y := mul_le_mul_of_nonpos_left hb.2 hx'
    have h2 : x * y ≤ x * b₁ := mul_le_mul_of_nonpos_left hb.1 hx'
    constructor
    · exact le_trans (min_le_right _ _) h1
    · exact le_trans h2 (le_max_left _ _)

/-- Lower bound: xy ≥ min of corner products -/
private theorem mul_lower_bound {x y a₁ a₂ b₁ b₂ : ℝ}
    (ha : a₁ ≤ x ∧ x ≤ a₂) (hb : b₁ ≤ y ∧ y ≤ b₂) :
    min (min (a₁ * b₁) (a₁ * b₂)) (min (a₂ * b₁) (a₂ * b₂)) ≤ x * y := by
  have h1 := (mul_mem_endpoints_left (y := y) ha).1
  by_cases! hcmp : a₁ * y ≤ a₂ * y
  · rw [min_eq_left hcmp] at h1
    have h2 := (mul_mem_endpoints_right hb (x := a₁)).1
    calc min (min (a₁ * b₁) (a₁ * b₂)) (min (a₂ * b₁) (a₂ * b₂))
        ≤ min (a₁ * b₁) (a₁ * b₂) := min_le_left _ _
      _ ≤ a₁ * y := h2
      _ ≤ x * y := h1
  · rw [min_eq_right (le_of_lt hcmp)] at h1
    have h2 := (mul_mem_endpoints_right hb (x := a₂)).1
    calc min (min (a₁ * b₁) (a₁ * b₂)) (min (a₂ * b₁) (a₂ * b₂))
        ≤ min (a₂ * b₁) (a₂ * b₂) := min_le_right _ _
      _ ≤ a₂ * y := h2
      _ ≤ x * y := h1

/-- Upper bound: xy ≤ max of corner products -/
private theorem mul_upper_bound {x y a₁ a₂ b₁ b₂ : ℝ}
    (ha : a₁ ≤ x ∧ x ≤ a₂) (hb : b₁ ≤ y ∧ y ≤ b₂) :
    x * y ≤ max (max (a₁ * b₁) (a₁ * b₂)) (max (a₂ * b₁) (a₂ * b₂)) := by
  have h1 := (mul_mem_endpoints_left (y := y) ha).2
  by_cases! hcmp : a₁ * y ≤ a₂ * y
  · rw [max_eq_right hcmp] at h1
    have h2 := (mul_mem_endpoints_right hb (x := a₂)).2
    calc x * y
        ≤ a₂ * y := h1
      _ ≤ max (a₂ * b₁) (a₂ * b₂) := h2
      _ ≤ max (max (a₁ * b₁) (a₁ * b₂)) (max (a₂ * b₁) (a₂ * b₂)) := le_max_right _ _
  · rw [max_eq_left (le_of_lt hcmp)] at h1
    have h2 := (mul_mem_endpoints_right hb (x := a₁)).2
    calc x * y
        ≤ a₁ * y := h1
      _ ≤ max (a₁ * b₁) (a₁ * b₂) := h2
      _ ≤ max (max (a₁ * b₁) (a₁ * b₂)) (max (a₂ * b₁) (a₂ * b₂)) := le_max_left _ _

/-- FTIA for multiplication on IntervalReal -/
theorem IntervalReal.mem_mul' {x y : ℝ} {I J : IntervalReal}
    (hx : x ∈ I) (hy : y ∈ J) : x * y ∈ IntervalReal.mul I J := by
  simp only [IntervalReal.mem_def] at *
  simp only [IntervalReal.mul]
  exact ⟨mul_lower_bound hx hy, mul_upper_bound hx hy⟩

/-! ### Main correctness theorem -/

/-- Correctness theorem for the strict partial real-endpoint evaluator.

The returned `some I` certificate is the support check: unsupported partial
operations return `none`, so callers cannot accidentally use a fallback interval
for `inv`, `log`, or `atanh`.
-/
theorem evalIntervalReal?_correct (e : Expr) (ρ_real : Nat → ℝ)
    (ρ_int : IntervalRealEnv) (hρ : envMemReal ρ_real ρ_int)
    {I : IntervalReal} (hI : evalIntervalReal? e ρ_int = some I) :
    Expr.eval ρ_real e ∈ I := by
  induction e generalizing I with
  | const q =>
      simp [evalIntervalReal?] at hI
      subst I
      simp only [Expr.eval_const]
      exact IntervalReal.mem_singleton_rat q
  | var idx =>
      simp [evalIntervalReal?] at hI
      subst I
      simp only [Expr.eval_var]
      exact hρ idx
  | add e₁ e₂ ih₁ ih₂ =>
      cases h₁ : evalIntervalReal? e₁ ρ_int with
      | none =>
          simp [evalIntervalReal?, h₁] at hI
      | some I₁ =>
          cases h₂ : evalIntervalReal? e₂ ρ_int with
          | none =>
              simp [evalIntervalReal?, h₁, h₂] at hI
          | some I₂ =>
              simp [evalIntervalReal?, h₁, h₂] at hI
              subst I
              simp only [Expr.eval_add]
              exact IntervalReal.mem_add (ih₁ h₁) (ih₂ h₂)
  | mul e₁ e₂ ih₁ ih₂ =>
      cases h₁ : evalIntervalReal? e₁ ρ_int with
      | none =>
          simp [evalIntervalReal?, h₁] at hI
      | some I₁ =>
          cases h₂ : evalIntervalReal? e₂ ρ_int with
          | none =>
              simp [evalIntervalReal?, h₁, h₂] at hI
          | some I₂ =>
              simp [evalIntervalReal?, h₁, h₂] at hI
              subst I
              simp only [Expr.eval_mul]
              exact IntervalReal.mem_mul' (ih₁ h₁) (ih₂ h₂)
  | neg e ih =>
      simp only [evalIntervalReal?] at hI
      split at hI <;> try contradiction
      next I₀ h₀ =>
        simp only [Option.some.injEq] at hI
        subst I
        simp only [Expr.eval_neg]
        exact IntervalReal.mem_neg (ih h₀)
  | inv _ =>
      simp [evalIntervalReal?] at hI
  | exp e ih =>
      simp only [evalIntervalReal?] at hI
      split at hI <;> try contradiction
      next I₀ h₀ =>
        simp only [Option.some.injEq] at hI
        subst I
        simp only [Expr.eval_exp]
        exact IntervalReal.mem_expInterval (ih h₀)
  | sin e ih =>
      simp only [evalIntervalReal?] at hI
      split at hI <;> try contradiction
      next I₀ h₀ =>
        simp only [Option.some.injEq] at hI
        subst I
        simp only [Expr.eval_sin]
        exact IntervalReal.mem_sinInterval (ih h₀)
  | cos e ih =>
      simp only [evalIntervalReal?] at hI
      split at hI <;> try contradiction
      next I₀ h₀ =>
        simp only [Option.some.injEq] at hI
        subst I
        simp only [Expr.eval_cos]
        exact IntervalReal.mem_cosInterval (ih h₀)
  | log _ =>
      simp [evalIntervalReal?] at hI
  | atan e ih =>
      simp only [evalIntervalReal?] at hI
      split at hI <;> try contradiction
      next I₀ h₀ =>
        simp only [Option.some.injEq] at hI
        subst I
        simp only [Expr.eval_atan]
        exact IntervalReal.mem_atanInterval (ih h₀)
  | arsinh e ih =>
      simp only [evalIntervalReal?] at hI
      split at hI <;> try contradiction
      next I₀ h₀ =>
        simp only [Option.some.injEq] at hI
        subst I
        simp only [Expr.eval_arsinh]
        exact IntervalReal.mem_arsinhInterval (ih h₀)
  | atanh _ =>
      simp [evalIntervalReal?] at hI
  | sinc e =>
      simp [evalIntervalReal?] at hI
      subst I
      simp only [Expr.eval_sinc]
      exact Real.sinc_mem_Icc _
  | erf e =>
      simp [evalIntervalReal?] at hI
      subst I
      simp only [Expr.eval_erf]
      exact Real.erf_mem_Icc _
  | sinh e ih =>
      simp only [evalIntervalReal?] at hI
      split at hI <;> try contradiction
      next I₀ h₀ =>
        simp only [Option.some.injEq] at hI
        subst I
        simp only [Expr.eval_sinh]
        exact IntervalReal.mem_sinhInterval (ih h₀)
  | cosh e ih =>
      simp only [evalIntervalReal?] at hI
      split at hI <;> try contradiction
      next I₀ h₀ =>
        simp only [Option.some.injEq] at hI
        subst I
        simp only [Expr.eval_cosh]
        exact IntervalReal.mem_coshInterval (ih h₀)
  | tanh e =>
      simp [evalIntervalReal?] at hI
      subst I
      simp only [Expr.eval_tanh, IntervalReal.mem_def]
      constructor
      · exact le_of_lt (Real.neg_one_lt_tanh _)
      · exact le_of_lt (Real.tanh_lt_one _)
  | sqrt e ih =>
      simp only [evalIntervalReal?] at hI
      split at hI <;> try contradiction
      next I₀ h₀ =>
        simp only [Option.some.injEq] at hI
        subst I
        simp only [Expr.eval_sqrt]
        exact IntervalReal.mem_sqrtInterval (ih h₀)
  | namedConst c =>
      simp [evalIntervalReal?] at hI
      subst I
      simp only [Expr.eval_namedConst, IntervalReal.mem_def]
      exact ⟨le_rfl, le_rfl⟩

/-! ### Convenience functions -/

/-- Strict single-variable real-endpoint interval evaluator. -/
noncomputable def evalIntervalReal1? (e : Expr) (I : IntervalReal) : Option IntervalReal :=
  evalIntervalReal? e (fun _ => I)

/-- Correctness for strict single-variable evaluation. -/
theorem evalIntervalReal1?_correct (e : Expr) (x : ℝ) (I J : IntervalReal)
    (hx : x ∈ I) (hJ : evalIntervalReal1? e I = some J) :
    Expr.eval (fun _ => x) e ∈ J :=
  evalIntervalReal?_correct e (fun _ => x) (fun _ => I) (fun _ => hx) hJ

/-! ### Conversion from rational to real interval environment -/

/-- Convert a rational interval environment to a real one -/
def toIntervalRealEnv (ρ : IntervalEnv) : IntervalRealEnv :=
  fun i => IntervalReal.ofRat (ρ i)

/-- Membership is preserved under conversion -/
theorem mem_toIntervalRealEnv {x : ℝ} {ρ : IntervalEnv} {i : Nat}
    (hx : x ∈ ρ i) : x ∈ toIntervalRealEnv ρ i :=
  IntervalReal.mem_ofRat hx

end LeanCert.Engine
