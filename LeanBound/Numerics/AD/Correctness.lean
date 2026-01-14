/-
Copyright (c) 2024 LeanBound Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanBound Contributors
-/
import LeanBound.Numerics.AD.Eval
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Automatic Differentiation - Correctness Theorems

This file proves the correctness of forward-mode automatic differentiation
for supported expressions (ExprSupported).

## Main theorems

* `evalDual_val_correct` - Value component is correct
* `evalDual_der_correct` - Derivative component is correct
* `evalFunc1_differentiable` - Supported expressions are differentiable
* `deriv_mem_dualDer` - Key theorem: computed derivative contains true derivative
* `evalDual_der_correct_idx` - n-variable derivative correctness
* `evalWithDeriv1_correct` - Single-variable correctness

## Design notes

All theorems in this file are FULLY PROVED with no sorry or axioms.
The correctness relies on the chain rule for each supported operation.
-/

namespace LeanBound.Numerics

open LeanBound.Core Filter
open scoped Topology

/-! ### Correctness -/

/-- The value component is correct for supported expressions.

    This theorem is FULLY PROVED (no sorry, no axioms) for supported expressions.
    The `hsupp` hypothesis ensures we only consider expressions in the verified subset. -/
theorem evalDual_val_correct (e : Expr) (hsupp : ExprSupported e)
    (ρ_real : Nat → ℝ) (ρ_dual : DualEnv)
    (hρ : ∀ i, ρ_real i ∈ (ρ_dual i).val) :
    Expr.eval ρ_real e ∈ (evalDual e ρ_dual).val := by
  induction hsupp with
  | const q =>
    simp only [Expr.eval_const, evalDual, DualInterval.const]
    exact IntervalRat.mem_singleton q
  | var idx =>
    simp only [Expr.eval_var, evalDual]
    exact hρ idx
  | add _ _ ih₁ ih₂ =>
    simp only [Expr.eval_add, evalDual, DualInterval.add]
    exact IntervalRat.mem_add ih₁ ih₂
  | mul _ _ ih₁ ih₂ =>
    simp only [Expr.eval_mul, evalDual, DualInterval.mul]
    exact IntervalRat.mem_mul ih₁ ih₂
  | neg _ ih =>
    simp only [Expr.eval_neg, evalDual, DualInterval.neg]
    exact IntervalRat.mem_neg ih
  | sin _ ih =>
    simp only [Expr.eval_sin, evalDual, DualInterval.sin]
    exact mem_sinInterval ih
  | cos _ ih =>
    simp only [Expr.eval_cos, evalDual, DualInterval.cos]
    exact mem_cosInterval ih
  | exp _ ih =>
    simp only [Expr.eval_exp, evalDual, DualInterval.exp]
    exact IntervalRat.mem_expInterval ih

/-! ### Single-variable evaluation for derivative proofs -/

/-- The function t ↦ Expr.eval (fun _ => t) e for single-variable expressions -/
noncomputable abbrev evalFunc1 (e : Expr) : ℝ → ℝ :=
  fun t => Expr.eval (fun _ => t) e

/-! ### Differentiability of supported expressions -/

/-- Supported expressions are differentiable as single-variable functions.
    This theorem shows that for any supported expression,
    the function `evalFunc1 e` is differentiable.

    FULLY PROVED - no sorry, no axioms. -/
theorem evalFunc1_differentiable (e : Expr) (hsupp : ExprSupported e) :
    Differentiable ℝ (evalFunc1 e) := by
  induction hsupp with
  | const q =>
    exact differentiable_const _
  | var _ =>
    exact differentiable_id
  | add _ _ ih₁ ih₂ =>
    exact Differentiable.add ih₁ ih₂
  | mul _ _ ih₁ ih₂ =>
    exact Differentiable.mul ih₁ ih₂
  | neg _ ih =>
    exact Differentiable.neg ih
  | sin _ ih =>
    exact Real.differentiable_sin.comp ih
  | cos _ ih =>
    exact Real.differentiable_cos.comp ih
  | exp _ ih =>
    exact Real.differentiable_exp.comp ih

/-! ### Core derivative correctness micro-lemmas -/

/-- Real.cos y is always in cosInterval I (which is [-1, 1]).
    This micro-lemma encapsulates the fact that cosInterval uses the global bound. -/
theorem cos_mem_cosInterval_of_any (y : ℝ) (I : IntervalRat) :
    Real.cos y ∈ cosInterval I := by
  simp only [cosInterval, IntervalRat.mem_def, Rat.cast_neg, Rat.cast_one]
  exact Real.cos_mem_Icc _

/-- Real.sin y is always in sinInterval I (which is [-1, 1]).
    This micro-lemma encapsulates the fact that sinInterval uses the global bound. -/
theorem sin_mem_sinInterval_of_any (y : ℝ) (I : IntervalRat) :
    Real.sin y ∈ sinInterval I := by
  simp only [sinInterval, IntervalRat.mem_def, Rat.cast_neg, Rat.cast_one]
  exact Real.sin_mem_Icc _

/-- -Real.sin y is always in IntervalRat.neg (sinInterval I).
    This combines the sin global bound with negation for the cos derivative rule. -/
theorem neg_sin_mem_neg_sinInterval (y : ℝ) (I : IntervalRat) :
    -Real.sin y ∈ IntervalRat.neg (sinInterval I) :=
  IntervalRat.mem_neg (sin_mem_sinInterval_of_any y I)

/-- The key lemma for n-variable AD: updateVar ρ_real idx x respects mkDualEnv ρ_int idx.
    This encapsulates the repeated proof that appears in mul/exp cases. -/
theorem updateVar_mem_mkDualEnv_val (ρ_real : Nat → ℝ) (ρ_int : IntervalEnv) (idx : Nat)
    (x : ℝ) (hx : x ∈ ρ_int idx) (hρ : ∀ i, ρ_real i ∈ ρ_int i) :
    ∀ i, Expr.updateVar ρ_real idx x i ∈ (mkDualEnv ρ_int idx i).val := by
  intro i
  by_cases hi : i = idx
  · subst hi
    simp only [Expr.updateVar_same, mkDualEnv, ↓reduceIte, DualInterval.varActive]
    exact hx
  · simp only [Expr.updateVar_other _ _ _ _ hi, mkDualEnv, if_neg hi, DualInterval.varPassive]
    exact hρ i

/-! ### evalFunc1 unfolding lemmas -/

/-- Helper lemma: evalFunc1 for addition unfolds correctly -/
theorem evalFunc1_add (e₁ e₂ : Expr) :
    evalFunc1 (Expr.add e₁ e₂) = fun t => evalFunc1 e₁ t + evalFunc1 e₂ t := rfl

/-- Helper lemma: evalFunc1 for addition in Pi form -/
theorem evalFunc1_add_pi (e₁ e₂ : Expr) :
    evalFunc1 (Expr.add e₁ e₂) = evalFunc1 e₁ + evalFunc1 e₂ := rfl

/-- Helper lemma: evalFunc1 for multiplication unfolds correctly -/
theorem evalFunc1_mul (e₁ e₂ : Expr) :
    evalFunc1 (Expr.mul e₁ e₂) = fun t => evalFunc1 e₁ t * evalFunc1 e₂ t := rfl

/-- Helper lemma: evalFunc1 for multiplication in Pi form -/
theorem evalFunc1_mul_pi (e₁ e₂ : Expr) :
    evalFunc1 (Expr.mul e₁ e₂) = evalFunc1 e₁ * evalFunc1 e₂ := rfl

/-- Helper lemma: evalFunc1 for negation unfolds correctly -/
theorem evalFunc1_neg (e : Expr) :
    evalFunc1 (Expr.neg e) = fun t => -(evalFunc1 e t) := rfl

/-- Helper lemma: evalFunc1 for negation in Pi form -/
theorem evalFunc1_neg_pi (e : Expr) :
    evalFunc1 (Expr.neg e) = -evalFunc1 e := rfl

/-- Helper lemma: evalFunc1 for sin unfolds correctly -/
theorem evalFunc1_sin (e : Expr) :
    evalFunc1 (Expr.sin e) = fun t => Real.sin (evalFunc1 e t) := rfl

/-- Helper lemma: evalFunc1 for cos unfolds correctly -/
theorem evalFunc1_cos (e : Expr) :
    evalFunc1 (Expr.cos e) = fun t => Real.cos (evalFunc1 e t) := rfl

/-- Helper lemma: evalFunc1 for exp unfolds correctly -/
theorem evalFunc1_exp (e : Expr) :
    evalFunc1 (Expr.exp e) = fun t => Real.exp (evalFunc1 e t) := rfl

/-- Helper lemma: evalFunc1 for log unfolds correctly -/
theorem evalFunc1_log (e : Expr) :
    evalFunc1 (Expr.log e) = fun t => Real.log (evalFunc1 e t) := rfl

/-- Helper lemma: evalFunc1 for atan unfolds correctly -/
theorem evalFunc1_atan (e : Expr) :
    evalFunc1 (Expr.atan e) = fun t => Real.arctan (evalFunc1 e t) := rfl

/-- Helper lemma: evalFunc1 for arsinh unfolds correctly -/
theorem evalFunc1_arsinh (e : Expr) :
    evalFunc1 (Expr.arsinh e) = fun t => Real.arsinh (evalFunc1 e t) := rfl

/-- Helper lemma: evalFunc1 for atanh unfolds correctly -/
theorem evalFunc1_atanh (e : Expr) :
    evalFunc1 (Expr.atanh e) = fun t => Real.atanh (evalFunc1 e t) := rfl

/-- Helper lemma: evalFunc1 for sinc unfolds correctly -/
theorem evalFunc1_sinc (e : Expr) :
    evalFunc1 (Expr.sinc e) = fun t => Real.sinc (evalFunc1 e t) := rfl

/-- Helper lemma: evalFunc1 for erf unfolds correctly -/
theorem evalFunc1_erf (e : Expr) :
    evalFunc1 (Expr.erf e) = fun t => Real.erf (evalFunc1 e t) := rfl

/-- Helper lemma: evalFunc1 for sqrt unfolds correctly -/
theorem evalFunc1_sqrt (e : Expr) :
    evalFunc1 (Expr.sqrt e) = fun t => Real.sqrt (evalFunc1 e t) := rfl

/-- Helper lemma: evalFunc1 for const -/
@[simp]
theorem evalFunc1_const (q : ℚ) : evalFunc1 (Expr.const q) = fun _ => (q : ℝ) := rfl

/-- Helper lemma: evalFunc1 for var -/
@[simp]
theorem evalFunc1_var (i : ℕ) : evalFunc1 (Expr.var i) = id := rfl

/-- Helper lemma: evalFunc1 for pi (constant function) -/
@[simp]
theorem evalFunc1_pi : evalFunc1 Expr.pi = fun _ => Real.pi := rfl

/-- Helper: the dual environment evaluation gives correct derivative.
    This connects the interval-based AD to actual calculus derivatives.

    FULLY PROVED - no sorry, no axioms. -/
theorem deriv_mem_dualDer (e : Expr) (hsupp : ExprSupported e)
    (I : IntervalRat) (x : ℝ) (hx : x ∈ I) :
    deriv (evalFunc1 e) x ∈
      (evalDual e (fun _ => DualInterval.varActive I)).der := by
  induction hsupp generalizing x with
  | const q =>
    -- d/dx (const) = 0
    simp only [evalDual, DualInterval.const, evalFunc1_const, deriv_const]
    convert IntervalRat.mem_singleton 0 using 1
    norm_cast
  | var _ =>
    -- d/dx (x) = 1
    simp only [evalDual, DualInterval.varActive, evalFunc1_var]
    rw [deriv_id]
    convert IntervalRat.mem_singleton 1 using 1
    norm_cast
  | add h₁ h₂ ih₁ ih₂ =>
    -- d/dx (f + g) = f' + g'
    have hd₁ := evalFunc1_differentiable _ h₁
    have hd₂ := evalFunc1_differentiable _ h₂
    simp only [evalDual, DualInterval.add, evalFunc1_add_pi, deriv_add (hd₁ x) (hd₂ x)]
    exact IntervalRat.mem_add (ih₁ x hx) (ih₂ x hx)
  | mul h₁ h₂ ih₁ ih₂ =>
    -- d/dx (f * g) = f' * g + f * g'
    have hd₁ := evalFunc1_differentiable _ h₁
    have hd₂ := evalFunc1_differentiable _ h₂
    simp only [evalDual, DualInterval.mul, evalFunc1_mul_pi, deriv_mul (hd₁ x) (hd₂ x)]
    -- Need: f'(x)*g(x) + f(x)*g'(x) ∈ der₁*val₂ + val₁*der₂
    have hval₁ := evalDual_val_correct _ h₁ (fun _ => x) (fun _ => DualInterval.varActive I)
      (fun _ => hx)
    have hval₂ := evalDual_val_correct _ h₂ (fun _ => x) (fun _ => DualInterval.varActive I)
      (fun _ => hx)
    simp only [DualInterval.varActive] at hval₁ hval₂
    exact IntervalRat.mem_add (IntervalRat.mem_mul (ih₁ x hx) hval₂) (IntervalRat.mem_mul hval₁ (ih₂ x hx))
  | neg hs ih =>
    -- d/dx (-f) = -f'
    have hd := evalFunc1_differentiable _ hs
    simp only [evalDual, DualInterval.neg, evalFunc1_neg_pi, deriv.neg]
    exact IntervalRat.mem_neg (ih x hx)
  | @sin e' hs ih =>
    -- d/dx (sin f) = cos(f) * f'
    have hd := evalFunc1_differentiable e' hs
    simp only [evalDual, DualInterval.sin, evalFunc1_sin]
    rw [deriv_sin (hd.differentiableAt)]
    exact IntervalRat.mem_mul (cos_mem_cosInterval_of_any _ _) (ih x hx)
  | @cos e' hs ih =>
    -- d/dx (cos f) = -sin(f) * f'
    have hd := evalFunc1_differentiable e' hs
    simp only [evalDual, DualInterval.cos, evalFunc1_cos]
    rw [deriv_cos (hd.differentiableAt)]
    exact IntervalRat.mem_mul (neg_sin_mem_neg_sinInterval _ _) (ih x hx)
  | @exp e' hs ih =>
    -- d/dx (exp f) = exp(f) * f'
    have hd := evalFunc1_differentiable e' hs
    simp only [evalDual, DualInterval.exp, evalFunc1_exp]
    rw [deriv_exp (hd.differentiableAt)]
    -- exp(f(x)) ∈ expInterval and f'(x) ∈ der
    have hval := evalDual_val_correct e' hs (fun _ => x) (fun _ => DualInterval.varActive I)
      (fun _ => hx)
    simp only [DualInterval.varActive] at hval
    have hexp := IntervalRat.mem_expInterval hval
    exact IntervalRat.mem_mul hexp (ih x hx)

/-- The derivative component of dual interval evaluation is correct.
    For a supported expression evaluated at a point x in the interval I,
    the derivative of the expression (as a function of x) lies in the
    computed derivative interval.

    This is the fundamental correctness theorem for forward-mode AD:
    the derivative bounds computed by interval arithmetic contain the
    true derivative at every point in the domain.

    FULLY PROVED - no sorry, no axioms. -/
theorem evalDual_der_correct (e : Expr) (hsupp : ExprSupported e)
    (I : IntervalRat) (x : ℝ) (hx : x ∈ I) :
    deriv (fun t => Expr.eval (fun _ => t) e) x ∈
      (evalDual e (fun _ => DualInterval.varActive I)).der :=
  deriv_mem_dualDer e hsupp I x hx

/-! ### Generalized n-variable derivative correctness -/

/-- Helper: evalAlong is differentiable for supported expressions -/
theorem evalAlong_differentiable (e : Expr) (hsupp : ExprSupported e)
    (ρ : Nat → ℝ) (idx : Nat) :
    Differentiable ℝ (Expr.evalAlong e ρ idx) := by
  induction hsupp with
  | const q =>
    simp only [Expr.evalAlong_const']
    exact differentiable_const _
  | var i =>
    by_cases h : i = idx
    · subst h
      simp only [Expr.evalAlong_var_active]
      exact differentiable_id
    · simp only [Expr.evalAlong_var_passive _ _ _ h]
      exact differentiable_const _
  | add _ _ ih₁ ih₂ =>
    simp only [Expr.evalAlong_add]
    exact Differentiable.add ih₁ ih₂
  | mul _ _ ih₁ ih₂ =>
    simp only [Expr.evalAlong_mul]
    exact Differentiable.mul ih₁ ih₂
  | neg _ ih =>
    simp only [Expr.evalAlong_neg]
    exact Differentiable.neg ih
  | sin _ ih =>
    simp only [Expr.evalAlong_sin]
    exact Real.differentiable_sin.comp ih
  | cos _ ih =>
    simp only [Expr.evalAlong_cos]
    exact Real.differentiable_cos.comp ih
  | exp _ ih =>
    simp only [Expr.evalAlong_exp]
    exact Real.differentiable_exp.comp ih

/-- The derivative of evalAlong with respect to coordinate `idx` lies in the
    computed derivative interval from mkDualEnv.

    This is the fundamental n-variable derivative correctness theorem.
    It shows that for any expression, if we differentiate along coordinate `idx`
    while holding all other coordinates fixed according to `ρ`, the derivative
    at any point `x` in the interval `ρ_int idx` lies in the computed interval.

    FULLY PROVED - no sorry, no axioms. -/
theorem evalDual_der_correct_idx (e : Expr) (hsupp : ExprSupported e)
    (ρ_real : Nat → ℝ) (ρ_int : IntervalEnv) (idx : Nat)
    (hρ : ∀ i, ρ_real i ∈ ρ_int i)
    (x : ℝ) (hx : x ∈ ρ_int idx) :
    deriv (Expr.evalAlong e ρ_real idx) x ∈
      (evalDual e (mkDualEnv ρ_int idx)).der := by
  induction hsupp generalizing x with
  | const q =>
    -- d/dt (const) = 0
    simp only [Expr.evalAlong_const', deriv_const, evalDual, DualInterval.const]
    convert IntervalRat.mem_singleton 0 using 1
    norm_cast
  | var i =>
    by_cases h : i = idx
    · -- Active variable: d/dt (t) = 1
      subst h
      simp only [Expr.evalAlong_var_active, evalDual, mkDualEnv, ↓reduceIte,
        DualInterval.varActive, deriv_id]
      convert IntervalRat.mem_singleton 1 using 1
      norm_cast
    · -- Passive variable: d/dt (const) = 0
      simp only [Expr.evalAlong_var_passive _ _ _ h, deriv_const, evalDual, mkDualEnv,
        if_neg h, DualInterval.varPassive]
      convert IntervalRat.mem_singleton 0 using 1
      norm_cast
  | add h₁ h₂ ih₁ ih₂ =>
    have hd₁ := evalAlong_differentiable _ h₁ ρ_real idx
    have hd₂ := evalAlong_differentiable _ h₂ ρ_real idx
    simp only [Expr.evalAlong_add_pi, deriv_add (hd₁ x) (hd₂ x), evalDual, DualInterval.add]
    exact IntervalRat.mem_add (ih₁ x hx) (ih₂ x hx)
  | mul h₁ h₂ ih₁ ih₂ =>
    have hd₁ := evalAlong_differentiable _ h₁ ρ_real idx
    have hd₂ := evalAlong_differentiable _ h₂ ρ_real idx
    simp only [Expr.evalAlong_mul_pi, deriv_mul (hd₁ x) (hd₂ x), evalDual, DualInterval.mul]
    have hmem := updateVar_mem_mkDualEnv_val ρ_real ρ_int idx x hx hρ
    have hval₁ := evalDual_val_correct _ h₁ _ _ hmem
    have hval₂ := evalDual_val_correct _ h₂ _ _ hmem
    exact IntervalRat.mem_add (IntervalRat.mem_mul (ih₁ x hx) hval₂) (IntervalRat.mem_mul hval₁ (ih₂ x hx))
  | neg hs ih =>
    have hd := evalAlong_differentiable _ hs ρ_real idx
    simp only [Expr.evalAlong_neg_pi, deriv.neg, evalDual, DualInterval.neg]
    exact IntervalRat.mem_neg (ih x hx)
  | @sin e' hs ih =>
    have hd := evalAlong_differentiable e' hs ρ_real idx
    simp only [Expr.evalAlong_sin, deriv_sin (hd.differentiableAt), evalDual, DualInterval.sin]
    exact IntervalRat.mem_mul (cos_mem_cosInterval_of_any _ _) (ih x hx)
  | @cos e' hs ih =>
    have hd := evalAlong_differentiable e' hs ρ_real idx
    simp only [Expr.evalAlong_cos, deriv_cos (hd.differentiableAt), evalDual, DualInterval.cos]
    exact IntervalRat.mem_mul (neg_sin_mem_neg_sinInterval _ _) (ih x hx)
  | @exp e' hs ih =>
    have hd := evalAlong_differentiable e' hs ρ_real idx
    simp only [Expr.evalAlong_exp, deriv_exp (hd.differentiableAt), evalDual, DualInterval.exp]
    have hmem := updateVar_mem_mkDualEnv_val ρ_real ρ_int idx x hx hρ
    have hval := evalDual_val_correct e' hs _ _ hmem
    exact IntervalRat.mem_mul (IntervalRat.mem_expInterval hval) (ih x hx)

/-- Convenience theorem: derivInterval correctness for n-variable expressions.
    The derivative of `evalAlong e ρ idx` at any point `x` in the interval
    lies in `derivInterval e ρ_int idx`. -/
theorem derivInterval_correct_idx (e : Expr) (hsupp : ExprSupported e)
    (ρ_real : Nat → ℝ) (ρ_int : IntervalEnv) (idx : Nat)
    (hρ : ∀ i, ρ_real i ∈ ρ_int i)
    (x : ℝ) (hx : x ∈ ρ_int idx) :
    deriv (Expr.evalAlong e ρ_real idx) x ∈ derivInterval e ρ_int idx := by
  simp only [derivInterval, evalWithDeriv]
  exact evalDual_der_correct_idx e hsupp ρ_real ρ_int idx hρ x hx

/-! ### Single-variable expressions -/

/-- Predicate: expression only uses variable index 0.
    This is useful for proving that different environments give the same result
    when they agree at index 0. -/
inductive UsesOnlyVar0 : Expr → Prop where
  | const (q : ℚ) : UsesOnlyVar0 (Expr.const q)
  | var0 : UsesOnlyVar0 (Expr.var 0)
  | add (e₁ e₂ : Expr) (h₁ : UsesOnlyVar0 e₁) (h₂ : UsesOnlyVar0 e₂) : UsesOnlyVar0 (Expr.add e₁ e₂)
  | mul (e₁ e₂ : Expr) (h₁ : UsesOnlyVar0 e₁) (h₂ : UsesOnlyVar0 e₂) : UsesOnlyVar0 (Expr.mul e₁ e₂)
  | neg (e : Expr) (h : UsesOnlyVar0 e) : UsesOnlyVar0 (Expr.neg e)
  | sin (e : Expr) (h : UsesOnlyVar0 e) : UsesOnlyVar0 (Expr.sin e)
  | cos (e : Expr) (h : UsesOnlyVar0 e) : UsesOnlyVar0 (Expr.cos e)
  | exp (e : Expr) (h : UsesOnlyVar0 e) : UsesOnlyVar0 (Expr.exp e)
  | atan (e : Expr) (h : UsesOnlyVar0 e) : UsesOnlyVar0 (Expr.atan e)
  | arsinh (e : Expr) (h : UsesOnlyVar0 e) : UsesOnlyVar0 (Expr.arsinh e)

/-- For expressions using only var 0, evalDual agrees for environments that match at 0 -/
theorem evalDual_congr_at_0 (e : Expr) (h : UsesOnlyVar0 e)
    (ρ₁ ρ₂ : DualEnv) (heq : ρ₁ 0 = ρ₂ 0) :
    evalDual e ρ₁ = evalDual e ρ₂ := by
  induction h generalizing ρ₁ ρ₂ with
  | const q => simp only [evalDual]
  | var0 => simp only [evalDual, heq]
  | add _ _ _ _ ih₁ ih₂ =>
    simp only [evalDual, ih₁ ρ₁ ρ₂ heq, ih₂ ρ₁ ρ₂ heq]
  | mul _ _ _ _ ih₁ ih₂ =>
    simp only [evalDual, ih₁ ρ₁ ρ₂ heq, ih₂ ρ₁ ρ₂ heq]
  | neg _ _ ih =>
    simp only [evalDual, ih ρ₁ ρ₂ heq]
  | sin _ _ ih =>
    simp only [evalDual, ih ρ₁ ρ₂ heq]
  | cos _ _ ih =>
    simp only [evalDual, ih ρ₁ ρ₂ heq]
  | exp _ _ ih =>
    simp only [evalDual, ih ρ₁ ρ₂ heq]
  | atan _ _ ih =>
    simp only [evalDual, ih ρ₁ ρ₂ heq]
  | arsinh _ _ ih =>
    simp only [evalDual, ih ρ₁ ρ₂ heq]

/-- mkDualEnv at index 0 equals varActive at 0 -/
theorem mkDualEnv_at_0 (I : IntervalRat) :
    mkDualEnv (fun _ => I) 0 0 = DualInterval.varActive I := by
  simp only [mkDualEnv, ↓reduceIte]

/-- For expressions using only var 0, derivInterval equals evalWithDeriv1 -/
theorem derivInterval_eq_evalWithDeriv1_of_UsesOnlyVar0 (e : Expr) (h : UsesOnlyVar0 e)
    (I : IntervalRat) :
    derivInterval e (fun _ => I) 0 = (evalWithDeriv1 e I).der := by
  simp only [derivInterval, evalWithDeriv, evalWithDeriv1]
  -- Need to show: (evalDual e (mkDualEnv (fun _ => I) 0)).der = (evalDual e (fun _ => varActive I)).der
  have henv_eq : mkDualEnv (fun _ => I) 0 0 = (fun _ => DualInterval.varActive I) 0 := by
    simp only [mkDualEnv_at_0]
  have heq := evalDual_congr_at_0 e h (mkDualEnv (fun _ => I) 0) (fun _ => DualInterval.varActive I) henv_eq
  rw [heq]

/-- Correctness of single-variable derivative bounds -/
theorem evalWithDeriv1_correct (e : Expr) (hsupp : ExprSupported e)
    (I : IntervalRat) (x : ℝ) (hx : x ∈ I) :
    Expr.eval (fun _ => x) e ∈ (evalWithDeriv1 e I).val ∧
    deriv (fun t => Expr.eval (fun _ => t) e) x ∈ (evalWithDeriv1 e I).der := by
  constructor
  · exact evalDual_val_correct e hsupp (fun _ => x) _ (fun _ => hx)
  · exact evalDual_der_correct e hsupp I x hx

end LeanBound.Numerics
