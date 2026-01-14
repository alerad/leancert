/-
Copyright (c) 2024 LeanBound Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanBound Contributors
-/
import LeanBound.Core.Expr
import LeanBound.Core.IntervalRealEndpoints
import LeanBound.Numerics.IntervalEval

/-!
# Interval Evaluation with Real Endpoints

This file implements interval evaluation using `IntervalReal` (real endpoints),
which allows us to support exp in a fully verified way.

## Main definitions

* `ExprSupportedExt` - Extended predicate including exp
* `evalIntervalReal` - Evaluate an expression over real-endpoint intervals
* `evalIntervalReal_correct` - Correctness theorem (fully proved)

## Design notes

This extends the verified subset from {const, var, add, mul, neg, sin, cos}
to also include {exp}. The key insight is that with real endpoints, we can
use `Real.exp` directly and its monotonicity properties.

For numerical computation, users should still use `IntervalRat` and convert
to `IntervalReal` when they need to reason about exp. This keeps computation
efficient while allowing proofs about transcendental functions.
-/

namespace LeanBound.Numerics

open LeanBound.Core

/-! ### Extended supported expression subset -/

/-- Predicate indicating an expression is in the extended verified subset.
    This includes exp in addition to the base subset.
    Does NOT support: inv (requires nonzero interval checks) -/
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
  | sqrt {e : Expr} : ExprSupportedExt e → ExprSupportedExt (Expr.sqrt e)

/-- The base supported subset is a subset of the extended one -/
theorem ExprSupported.toExt {e : Expr} (h : ExprSupported e) : ExprSupportedExt e := by
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

/-- Evaluate an expression over real-endpoint intervals.

    For expressions in ExprSupportedExt (const, var, add, mul, neg, sin, cos, exp),
    this computes correct interval bounds with a fully-verified proof.

    For unsupported expressions (inv, log), this returns a trivial interval.
    Do not call evalIntervalReal on expressions containing inv or log unless
    you are prepared for unsound results. -/
noncomputable def evalIntervalReal (e : Expr) (ρ : IntervalRealEnv) : IntervalReal :=
  match e with
  | Expr.const q => IntervalReal.singleton q
  | Expr.var idx => ρ idx
  | Expr.add e₁ e₂ => IntervalReal.add (evalIntervalReal e₁ ρ) (evalIntervalReal e₂ ρ)
  | Expr.mul e₁ e₂ => IntervalReal.mul (evalIntervalReal e₁ ρ) (evalIntervalReal e₂ ρ)
  | Expr.neg e => IntervalReal.neg (evalIntervalReal e ρ)
  | Expr.inv _ => ⟨0, 0, le_refl 0⟩  -- Unsupported: returns trivial interval
  | Expr.exp e => IntervalReal.expInterval (evalIntervalReal e ρ)
  | Expr.sin e => IntervalReal.sinInterval (evalIntervalReal e ρ)
  | Expr.cos e => IntervalReal.cosInterval (evalIntervalReal e ρ)
  | Expr.log _ => ⟨0, 0, le_refl 0⟩  -- Unsupported: returns trivial interval
  | Expr.atan e => IntervalReal.atanInterval (evalIntervalReal e ρ)
  | Expr.arsinh e => IntervalReal.arsinhInterval (evalIntervalReal e ρ)
  | Expr.atanh _ => ⟨0, 0, le_refl 0⟩  -- Partial function: returns trivial interval
  | Expr.sinc _ => ⟨-1, 1, by norm_num⟩  -- sinc is bounded by [-1, 1]
  | Expr.erf _ => ⟨-1, 1, by norm_num⟩  -- erf is bounded by [-1, 1]
  | Expr.sinh e => IntervalReal.sinhInterval (evalIntervalReal e ρ)
  | Expr.cosh e => IntervalReal.coshInterval (evalIntervalReal e ρ)
  | Expr.tanh _ => ⟨-1, 1, by norm_num⟩  -- tanh is bounded by (-1, 1)
  | Expr.sqrt e => IntervalReal.sqrtInterval (evalIntervalReal e ρ)
  | Expr.pi => ⟨Real.pi, Real.pi, le_refl _⟩  -- Pi as singleton interval

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
  by_cases hy : 0 ≤ y
  · have h1 : a₁ * y ≤ x * y := mul_le_mul_of_nonneg_right ha.1 hy
    have h2 : x * y ≤ a₂ * y := mul_le_mul_of_nonneg_right ha.2 hy
    constructor
    · exact le_trans (min_le_left _ _) h1
    · exact le_trans h2 (le_max_right _ _)
  · push_neg at hy
    have hy' := le_of_lt hy
    have h1 : a₂ * y ≤ x * y := mul_le_mul_of_nonpos_right ha.2 hy'
    have h2 : x * y ≤ a₁ * y := mul_le_mul_of_nonpos_right ha.1 hy'
    constructor
    · exact le_trans (min_le_right _ _) h1
    · exact le_trans h2 (le_max_left _ _)

/-- Helper: for y ∈ [b₁, b₂], x*y lies between endpoint products. -/
private theorem mul_mem_endpoints_right {y b₁ b₂ x : ℝ}
    (hb : b₁ ≤ y ∧ y ≤ b₂) :
    min (x * b₁) (x * b₂) ≤ x * y ∧ x * y ≤ max (x * b₁) (x * b₂) := by
  by_cases hx : 0 ≤ x
  · have h1 : x * b₁ ≤ x * y := mul_le_mul_of_nonneg_left hb.1 hx
    have h2 : x * y ≤ x * b₂ := mul_le_mul_of_nonneg_left hb.2 hx
    constructor
    · exact le_trans (min_le_left _ _) h1
    · exact le_trans h2 (le_max_right _ _)
  · push_neg at hx
    have hx' := le_of_lt hx
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
  by_cases hcmp : a₁ * y ≤ a₂ * y
  · rw [min_eq_left hcmp] at h1
    have h2 := (mul_mem_endpoints_right hb (x := a₁)).1
    calc min (min (a₁ * b₁) (a₁ * b₂)) (min (a₂ * b₁) (a₂ * b₂))
        ≤ min (a₁ * b₁) (a₁ * b₂) := min_le_left _ _
      _ ≤ a₁ * y := h2
      _ ≤ x * y := h1
  · push_neg at hcmp
    rw [min_eq_right (le_of_lt hcmp)] at h1
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
  by_cases hcmp : a₁ * y ≤ a₂ * y
  · rw [max_eq_right hcmp] at h1
    have h2 := (mul_mem_endpoints_right hb (x := a₂)).2
    calc x * y
        ≤ a₂ * y := h1
      _ ≤ max (a₂ * b₁) (a₂ * b₂) := h2
      _ ≤ max (max (a₁ * b₁) (a₁ * b₂)) (max (a₂ * b₁) (a₂ * b₂)) := le_max_right _ _
  · push_neg at hcmp
    rw [max_eq_left (le_of_lt hcmp)] at h1
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

/-- Fundamental correctness theorem for real-endpoint interval evaluation.
    If variables are in their intervals, the expression evaluates to a value
    in the computed interval.

    This theorem is FULLY PROVED (no sorry, no axioms) for ExprSupportedExt expressions.
    This includes exp! -/
theorem evalIntervalReal_correct (e : Expr) (hsupp : ExprSupportedExt e)
    (ρ_real : Nat → ℝ) (ρ_int : IntervalRealEnv) (hρ : envMemReal ρ_real ρ_int) :
    Expr.eval ρ_real e ∈ evalIntervalReal e ρ_int := by
  induction hsupp with
  | const q =>
    simp only [Expr.eval_const, evalIntervalReal]
    exact IntervalReal.mem_singleton_rat q
  | var idx =>
    simp only [Expr.eval_var, evalIntervalReal]
    exact hρ idx
  | add _ _ ih₁ ih₂ =>
    simp only [Expr.eval_add, evalIntervalReal]
    exact IntervalReal.mem_add ih₁ ih₂
  | mul _ _ ih₁ ih₂ =>
    simp only [Expr.eval_mul, evalIntervalReal]
    exact IntervalReal.mem_mul' ih₁ ih₂
  | neg _ ih =>
    simp only [Expr.eval_neg, evalIntervalReal]
    exact IntervalReal.mem_neg ih
  | sin _ ih =>
    simp only [Expr.eval_sin, evalIntervalReal]
    exact IntervalReal.mem_sinInterval ih
  | cos _ ih =>
    simp only [Expr.eval_cos, evalIntervalReal]
    exact IntervalReal.mem_cosInterval ih
  | exp _ ih =>
    simp only [Expr.eval_exp, evalIntervalReal]
    exact IntervalReal.mem_expInterval ih
  | atan _ ih =>
    simp only [Expr.eval_atan, evalIntervalReal]
    exact IntervalReal.mem_atanInterval ih
  | arsinh _ ih =>
    simp only [Expr.eval_arsinh, evalIntervalReal]
    exact IntervalReal.mem_arsinhInterval ih
  | sinh _ ih =>
    simp only [Expr.eval_sinh, evalIntervalReal]
    exact IntervalReal.mem_sinhInterval ih
  | cosh _ ih =>
    simp only [Expr.eval_cosh, evalIntervalReal]
    exact IntervalReal.mem_coshInterval ih
  | sqrt _ ih =>
    simp only [Expr.eval_sqrt, evalIntervalReal]
    exact IntervalReal.mem_sqrtInterval ih

/-! ### Convenience functions -/

/-- Evaluate an expression with a single variable over a real-endpoint interval -/
noncomputable def evalIntervalReal1 (e : Expr) (I : IntervalReal) : IntervalReal :=
  evalIntervalReal e (fun _ => I)

/-- Correctness for single-variable evaluation -/
theorem evalIntervalReal1_correct (e : Expr) (hsupp : ExprSupportedExt e)
    (x : ℝ) (I : IntervalReal) (hx : x ∈ I) :
    Expr.eval (fun _ => x) e ∈ evalIntervalReal1 e I :=
  evalIntervalReal_correct e hsupp _ _ (fun _ => hx)

/-! ### Conversion from rational to real interval environment -/

/-- Convert a rational interval environment to a real one -/
def toIntervalRealEnv (ρ : IntervalEnv) : IntervalRealEnv :=
  fun i => IntervalReal.ofRat (ρ i)

/-- Membership is preserved under conversion -/
theorem mem_toIntervalRealEnv {x : ℝ} {ρ : IntervalEnv} {i : Nat}
    (hx : x ∈ ρ i) : x ∈ toIntervalRealEnv ρ i :=
  IntervalReal.mem_ofRat hx

/-! ### Tactic-facing lemmas for interval bounds (extended subset with exp) -/

/-- Upper bound lemma for extended subset (includes exp).
    FULLY PROVED - no sorry, no axioms. -/
theorem exprExt_le_of_interval_hi (e : Expr) (hsupp : ExprSupportedExt e)
    (I : IntervalReal) (c : ℝ) (hhi : (evalIntervalReal1 e I).hi ≤ c) :
    ∀ x ∈ I, Expr.eval (fun _ => x) e ≤ c := by
  intro x hx
  have hmem := evalIntervalReal1_correct e hsupp x I hx
  simp only [IntervalReal.mem_def] at hmem
  exact le_trans hmem.2 hhi

/-- Lower bound lemma for extended subset (includes exp).
    FULLY PROVED - no sorry, no axioms. -/
theorem exprExt_ge_of_interval_lo (e : Expr) (hsupp : ExprSupportedExt e)
    (I : IntervalReal) (c : ℝ) (hlo : c ≤ (evalIntervalReal1 e I).lo) :
    ∀ x ∈ I, c ≤ Expr.eval (fun _ => x) e := by
  intro x hx
  have hmem := evalIntervalReal1_correct e hsupp x I hx
  simp only [IntervalReal.mem_def] at hmem
  exact le_trans hlo hmem.1

/-- Strict upper bound for extended subset.
    FULLY PROVED - no sorry, no axioms. -/
theorem exprExt_lt_of_interval_hi_lt (e : Expr) (hsupp : ExprSupportedExt e)
    (I : IntervalReal) (c : ℝ) (hhi : (evalIntervalReal1 e I).hi < c) :
    ∀ x ∈ I, Expr.eval (fun _ => x) e < c := by
  intro x hx
  have hmem := evalIntervalReal1_correct e hsupp x I hx
  simp only [IntervalReal.mem_def] at hmem
  exact lt_of_le_of_lt hmem.2 hhi

/-- Strict lower bound for extended subset.
    FULLY PROVED - no sorry, no axioms. -/
theorem exprExt_gt_of_interval_lo_gt (e : Expr) (hsupp : ExprSupportedExt e)
    (I : IntervalReal) (c : ℝ) (hlo : c < (evalIntervalReal1 e I).lo) :
    ∀ x ∈ I, c < Expr.eval (fun _ => x) e := by
  intro x hx
  have hmem := evalIntervalReal1_correct e hsupp x I hx
  simp only [IntervalReal.mem_def] at hmem
  exact lt_of_lt_of_le hlo hmem.1

/-- Point variant for extended subset. -/
theorem exprExt_le_of_mem_interval (e : Expr) (hsupp : ExprSupportedExt e)
    (I : IntervalReal) (c : ℝ) (x : ℝ) (hx : x ∈ I)
    (hhi : (evalIntervalReal1 e I).hi ≤ c) :
    Expr.eval (fun _ => x) e ≤ c :=
  exprExt_le_of_interval_hi e hsupp I c hhi x hx

/-- Point variant for extended subset. -/
theorem exprExt_ge_of_mem_interval (e : Expr) (hsupp : ExprSupportedExt e)
    (I : IntervalReal) (c : ℝ) (x : ℝ) (hx : x ∈ I)
    (hlo : c ≤ (evalIntervalReal1 e I).lo) :
    c ≤ Expr.eval (fun _ => x) e :=
  exprExt_ge_of_interval_lo e hsupp I c hlo x hx

end LeanBound.Numerics
