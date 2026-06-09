/-
Copyright (c) 2024 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import Lean
import LeanCert.Meta.ToExpr
import LeanCert.Meta.ProveSupported
import LeanCert.Core.Expr
import Mathlib.Topology.ContinuousOn
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Automatic Continuity Proof Generation

This module provides metaprogramming infrastructure to automatically generate
`ContinuousOn` proof terms for reified LeanCert expressions.

Given a reified AST `e : LeanCert.Core.Expr`, we construct a proof that
`ContinuousOn (fun x => Expr.eval (fun _ => x) e) (Set.Icc lo hi)`.

## Main definitions

* `ExprContinuousCore` - Predicate for expressions continuous everywhere (excludes inv)
* `exprContinuousCore_continuousOn` - Base theorem: all ExprContinuousCore expressions are continuous
* `mkContinuousCoreProof` - Generate `ExprContinuousCore` proofs from AST structure
* `mkContinuousOnProof` - Generate `ContinuousOn` proofs

## Design

We define `ExprContinuousCore` as a separate predicate from `ExprSupportedCore` because:
- `inv` (1/x) is supported for interval evaluation but NOT continuous at 0
- `ExprContinuousCore` excludes `inv`, so all its constructors are globally continuous

Operations in `ExprContinuousCore`:
- Constants: `continuousOn_const`
- Variables (identity): `continuousOn_id`
- Add, Mul, Neg: preserved by composition
- Sin, Cos, Exp, Sqrt, Sinh, Cosh, Tanh, Erf, named constants:
  continuous everywhere
-/

open Lean Meta Elab Term Command
open LeanCert.Core

-- Use explicit alias to avoid ambiguity with Lean.Expr
abbrev LExpr := LeanCert.Core.Expr

namespace LeanCert.Meta

/-! ## Continuous Expression Predicate

Since `inv` (1/x) is not continuous at 0, we define a separate predicate for
expressions that are continuous everywhere. This excludes `inv` from `ExprSupportedCore`.
-/

/-- Expressions that are continuous everywhere (excludes inv and log).
    This is a subset of ExprSupportedCore used for continuity proofs.
    Note: log is excluded because it is not continuous at 0. -/
inductive ExprContinuousCore : LExpr → Prop where
  | const (q : ℚ) : ExprContinuousCore (Expr.const q)
  | var (idx : Nat) : ExprContinuousCore (Expr.var idx)
  | add {e₁ e₂ : LExpr} : ExprContinuousCore e₁ → ExprContinuousCore e₂ →
      ExprContinuousCore (Expr.add e₁ e₂)
  | mul {e₁ e₂ : LExpr} : ExprContinuousCore e₁ → ExprContinuousCore e₂ →
      ExprContinuousCore (Expr.mul e₁ e₂)
  | neg {e : LExpr} : ExprContinuousCore e → ExprContinuousCore (Expr.neg e)
  | sin {e : LExpr} : ExprContinuousCore e → ExprContinuousCore (Expr.sin e)
  | cos {e : LExpr} : ExprContinuousCore e → ExprContinuousCore (Expr.cos e)
  | exp {e : LExpr} : ExprContinuousCore e → ExprContinuousCore (Expr.exp e)
  | sqrt {e : LExpr} : ExprContinuousCore e → ExprContinuousCore (Expr.sqrt e)
  | sinh {e : LExpr} : ExprContinuousCore e → ExprContinuousCore (Expr.sinh e)
  | cosh {e : LExpr} : ExprContinuousCore e → ExprContinuousCore (Expr.cosh e)
  | tanh {e : LExpr} : ExprContinuousCore e → ExprContinuousCore (Expr.tanh e)
  | erf {e : LExpr} : ExprContinuousCore e → ExprContinuousCore (Expr.erf e)
  | namedConst (c : MathConst) : ExprContinuousCore (Expr.namedConst c)

/-- ExprContinuousCore implies ExprSupportedCore -/
theorem ExprContinuousCore.toSupported {e : LExpr} (h : ExprContinuousCore e) :
    LeanCert.Engine.ExprSupportedCore e := by
  induction h with
  | const q => exact .const q
  | var idx => exact .var idx
  | add _ _ ih1 ih2 => exact .add ih1 ih2
  | mul _ _ ih1 ih2 => exact .mul ih1 ih2
  | neg _ ih => exact .neg ih
  | sin _ ih => exact .sin ih
  | cos _ ih => exact .cos ih
  | exp _ ih => exact .exp ih
  | sqrt _ ih => exact .sqrt ih
  | sinh _ ih => exact .sinh ih
  | cosh _ ih => exact .cosh ih
  | tanh _ ih => exact .tanh ih
  | erf _ ih => exact .erf ih
  | namedConst c => exact .namedConst c

/-! ## Base Continuity Theorem

This theorem proves that all `ExprContinuousCore` expressions evaluate to continuous functions.
We prove this by induction on the structure of `ExprContinuousCore`.
-/

/-- All ExprContinuousCore expressions are continuous on any set.

This is the foundational theorem that allows automatic continuity proof generation.
Since ExprContinuousCore only includes operations that are continuous everywhere
(const, var, add, mul, neg, sin, cos, exp, sqrt, sinh, cosh, tanh, erf,
named constants), the result
follows by structural induction.

NOTE: inv and log are NOT included because they are not continuous at 0. -/
theorem exprContinuousCore_continuousOn (e : LExpr) (hsupp : ExprContinuousCore e)
    {s : Set ℝ} :
    ContinuousOn (fun x => LeanCert.Core.Expr.eval (fun _ => x) e) s := by
  induction hsupp with
  | const c =>
    simp only [LeanCert.Core.Expr.eval]
    exact continuousOn_const
  | var n =>
    -- eval (fun _ => x) (var n) = (fun _ => x) n = x
    simp only [LeanCert.Core.Expr.eval]
    exact continuous_id.continuousOn
  | add _ _ ih1 ih2 =>
    simp only [LeanCert.Core.Expr.eval]
    exact ih1.add ih2
  | mul _ _ ih1 ih2 =>
    simp only [LeanCert.Core.Expr.eval]
    exact ih1.mul ih2
  | neg _ ih =>
    simp only [LeanCert.Core.Expr.eval]
    exact ih.neg
  | sin _ ih =>
    simp only [LeanCert.Core.Expr.eval]
    exact Real.continuous_sin.comp_continuousOn ih
  | cos _ ih =>
    simp only [LeanCert.Core.Expr.eval]
    exact Real.continuous_cos.comp_continuousOn ih
  | exp _ ih =>
    simp only [LeanCert.Core.Expr.eval]
    exact Real.continuous_exp.comp_continuousOn ih
  | sqrt _ ih =>
    simp only [LeanCert.Core.Expr.eval]
    -- sqrt is continuous on [0, ∞) and returns 0 for negative inputs
    -- For ContinuousOn on any set, we use Real.continuous_sqrt
    exact Real.continuous_sqrt.comp_continuousOn ih
  | sinh _ ih =>
    simp only [LeanCert.Core.Expr.eval]
    exact Real.continuous_sinh.comp_continuousOn ih
  | cosh _ ih =>
    simp only [LeanCert.Core.Expr.eval]
    exact Real.continuous_cosh.comp_continuousOn ih
  | tanh _ ih =>
    simp only [LeanCert.Core.Expr.eval]
    -- tanh = sinh / cosh, and cosh > 0 everywhere
    have hcont : Continuous Real.tanh := by
      have h : Real.tanh = fun x => Real.sinh x / Real.cosh x := by
        ext x; exact Real.tanh_eq_sinh_div_cosh x
      rw [h]
      exact Real.continuous_sinh.div Real.continuous_cosh (fun x => ne_of_gt (Real.cosh_pos x))
    exact hcont.comp_continuousOn ih
  | erf _ ih =>
    simp only [LeanCert.Core.Expr.eval]
    have herf_cont : Continuous Real.erf := by
      have hdiff : Differentiable ℝ Real.erf := by
        unfold Real.erf
        apply Differentiable.const_mul
        intro y
        have hcont : Continuous (fun t => Real.exp (-(t^2))) :=
          Real.continuous_exp.comp (continuous_neg.comp (continuous_pow 2))
        exact (hcont.integral_hasStrictDerivAt 0 y).hasStrictFDerivAt.differentiableAt
      exact hdiff.continuous
    exact herf_cont.comp_continuousOn ih
  | namedConst _ =>
    simp only [LeanCert.Core.Expr.eval]
    exact continuousOn_const

/-- Specialized version for Icc intervals (common case for interval_roots) -/
theorem exprContinuousCore_continuousOn_Icc (e : LExpr) (hsupp : ExprContinuousCore e)
    (lo hi : ℝ) :
    ContinuousOn (fun x => LeanCert.Core.Expr.eval (fun _ => x) e) (Set.Icc lo hi) :=
  exprContinuousCore_continuousOn e hsupp

/-- Version taking IntervalRat for convenience -/
theorem exprContinuousCore_continuousOn_interval (e : LExpr) (hsupp : ExprContinuousCore e)
    (I : LeanCert.Core.IntervalRat) :
    ContinuousOn (fun x => LeanCert.Core.Expr.eval (fun _ => x) e) (Set.Icc I.lo I.hi) :=
  exprContinuousCore_continuousOn e hsupp

/-! ### Backward Compatibility: ExprSupportedCore Continuity

These theorems are provided for backward compatibility with code that uses
`ExprSupportedCore`. For expressions with log, a domain validity condition is required.
-/

/-- Domain validity for continuity: ensures log arguments evaluate to positive values.
    For expressions without log, this is always True. -/
def exprContinuousDomainValid (e : LExpr) (s : Set ℝ) : Prop :=
  match e with
  | LeanCert.Core.Expr.const _ => True
  | LeanCert.Core.Expr.var _ => True
  | LeanCert.Core.Expr.add e₁ e₂ => exprContinuousDomainValid e₁ s ∧ exprContinuousDomainValid e₂ s
  | LeanCert.Core.Expr.mul e₁ e₂ => exprContinuousDomainValid e₁ s ∧ exprContinuousDomainValid e₂ s
  | LeanCert.Core.Expr.neg e => exprContinuousDomainValid e s
  | LeanCert.Core.Expr.inv e => exprContinuousDomainValid e s
  | LeanCert.Core.Expr.exp e => exprContinuousDomainValid e s
  | LeanCert.Core.Expr.sin e => exprContinuousDomainValid e s
  | LeanCert.Core.Expr.cos e => exprContinuousDomainValid e s
  | LeanCert.Core.Expr.log e => exprContinuousDomainValid e s ∧
      ∀ x ∈ s, 0 < LeanCert.Core.Expr.eval (fun _ => x) e
  | LeanCert.Core.Expr.atan e => exprContinuousDomainValid e s
  | LeanCert.Core.Expr.arsinh e => exprContinuousDomainValid e s
  | LeanCert.Core.Expr.atanh e => exprContinuousDomainValid e s
  | LeanCert.Core.Expr.sinc e => exprContinuousDomainValid e s
  | LeanCert.Core.Expr.erf e => exprContinuousDomainValid e s
  | LeanCert.Core.Expr.sinh e => exprContinuousDomainValid e s
  | LeanCert.Core.Expr.cosh e => exprContinuousDomainValid e s
  | LeanCert.Core.Expr.tanh e => exprContinuousDomainValid e s
  | LeanCert.Core.Expr.sqrt e => exprContinuousDomainValid e s
  | LeanCert.Core.Expr.namedConst _ => True

/-- Domain validity is trivially true for ExprSupported expressions (which exclude log). -/
theorem exprContinuousDomainValid_of_ExprSupported {e : LExpr}
    (hsupp : LeanCert.Engine.ExprSupported e) {s : Set ℝ} : exprContinuousDomainValid e s := by
  induction hsupp with
  | const _ => trivial
  | var _ => trivial
  | add _ _ ih1 ih2 => exact ⟨ih1, ih2⟩
  | mul _ _ ih1 ih2 => exact ⟨ih1, ih2⟩
  | neg _ ih => exact ih
  | sin _ ih => exact ih
  | cos _ ih => exact ih
  | exp _ ih => exact ih

/-- Domain validity is trivially true for ExprContinuousCore expressions (no log). -/
theorem exprContinuousDomainValid_of_ExprContinuousCore {e : LExpr} (hcont : ExprContinuousCore e)
    {s : Set ℝ} : exprContinuousDomainValid e s := by
  induction hcont with
  | const _ => trivial
  | var _ => trivial
  | add _ _ ih1 ih2 => exact ⟨ih1, ih2⟩
  | mul _ _ ih1 ih2 => exact ⟨ih1, ih2⟩
  | neg _ ih => exact ih
  | sin _ ih => exact ih
  | cos _ ih => exact ih
  | exp _ ih => exact ih
  | sqrt _ ih => exact ih
  | sinh _ ih => exact ih
  | cosh _ ih => exact ih
  | tanh _ ih => exact ih
  | erf _ ih => exact ih
  | namedConst _ => trivial

/-- All ExprSupportedCore expressions are continuous on sets where log arguments are positive.

This theorem exists for backward compatibility with code that uses
`ExprSupportedCore`. For expressions with log, the domain validity condition
ensures the argument evaluates to positive values on s. -/
theorem exprSupportedCore_continuousOn (e : LExpr) (hsupp : LeanCert.Engine.ExprSupportedCore e)
    {s : Set ℝ} (hdom : exprContinuousDomainValid e s) :
    ContinuousOn (fun x => LeanCert.Core.Expr.eval (fun _ => x) e) s := by
  induction hsupp with
  | const c =>
    simp only [LeanCert.Core.Expr.eval]
    exact continuousOn_const
  | var n =>
    simp only [LeanCert.Core.Expr.eval]
    exact continuous_id.continuousOn
  | add _ _ ih1 ih2 =>
    simp only [exprContinuousDomainValid] at hdom
    simp only [LeanCert.Core.Expr.eval]
    exact (ih1 hdom.1).add (ih2 hdom.2)
  | mul _ _ ih1 ih2 =>
    simp only [exprContinuousDomainValid] at hdom
    simp only [LeanCert.Core.Expr.eval]
    exact (ih1 hdom.1).mul (ih2 hdom.2)
  | neg _ ih =>
    simp only [exprContinuousDomainValid] at hdom
    simp only [LeanCert.Core.Expr.eval]
    exact (ih hdom).neg
  | sin _ ih =>
    simp only [exprContinuousDomainValid] at hdom
    simp only [LeanCert.Core.Expr.eval]
    exact Real.continuous_sin.comp_continuousOn (ih hdom)
  | cos _ ih =>
    simp only [exprContinuousDomainValid] at hdom
    simp only [LeanCert.Core.Expr.eval]
    exact Real.continuous_cos.comp_continuousOn (ih hdom)
  | exp _ ih =>
    simp only [exprContinuousDomainValid] at hdom
    simp only [LeanCert.Core.Expr.eval]
    exact Real.continuous_exp.comp_continuousOn (ih hdom)
  | sqrt _ ih =>
    simp only [exprContinuousDomainValid] at hdom
    simp only [LeanCert.Core.Expr.eval]
    exact Real.continuous_sqrt.comp_continuousOn (ih hdom)
  | sinh _ ih =>
    simp only [exprContinuousDomainValid] at hdom
    simp only [LeanCert.Core.Expr.eval]
    exact Real.continuous_sinh.comp_continuousOn (ih hdom)
  | cosh _ ih =>
    simp only [exprContinuousDomainValid] at hdom
    simp only [LeanCert.Core.Expr.eval]
    exact Real.continuous_cosh.comp_continuousOn (ih hdom)
  | tanh _ ih =>
    simp only [exprContinuousDomainValid] at hdom
    simp only [LeanCert.Core.Expr.eval]
    have hcont : Continuous Real.tanh := by
      have h : Real.tanh = fun x => Real.sinh x / Real.cosh x := by
        ext x; exact Real.tanh_eq_sinh_div_cosh x
      rw [h]
      exact Real.continuous_sinh.div Real.continuous_cosh (fun x => ne_of_gt (Real.cosh_pos x))
    exact hcont.comp_continuousOn (ih hdom)
  | erf _ ih =>
    simp only [exprContinuousDomainValid] at hdom
    simp only [LeanCert.Core.Expr.eval]
    -- Real.erf is continuous (it's differentiable, and differentiable implies continuous)
    have herf_cont : Continuous Real.erf := by
      have hdiff : Differentiable ℝ Real.erf := by
        unfold Real.erf
        apply Differentiable.const_mul
        intro y
        have hcont : Continuous (fun t => Real.exp (-(t^2))) :=
          Real.continuous_exp.comp (continuous_neg.comp (continuous_pow 2))
        exact (hcont.integral_hasStrictDerivAt 0 y).hasStrictFDerivAt.differentiableAt
      exact hdiff.continuous
    exact herf_cont.comp_continuousOn (ih hdom)
  | @log arg _ ih =>
    simp only [exprContinuousDomainValid] at hdom
    simp only [LeanCert.Core.Expr.eval]
    -- hdom.1: recursive domain validity for arg
    -- hdom.2: ∀ x ∈ s, 0 < Expr.eval (fun _ => x) arg
    have harg_cont := ih hdom.1
    -- We need continuity of Real.log composed with the argument evaluation
    -- Real.log is continuous on {0}ᶜ, and by hdom.2, arg maps s into positive reals ⊆ {0}ᶜ
    have hs_maps : Set.MapsTo (fun x => LeanCert.Core.Expr.eval (fun _ => x) arg) s {0}ᶜ := by
      intro x hx
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      exact ne_of_gt (hdom.2 x hx)
    exact Real.continuousOn_log.comp harg_cont hs_maps
  | namedConst _ =>
    simp only [LeanCert.Core.Expr.eval]
    exact continuousOn_const

/-- Interval-specialized version of `exprSupportedCore_continuousOn`. -/
theorem exprSupportedCore_continuousOn_interval
    (e : LExpr) (hsupp : LeanCert.Engine.ExprSupportedCore e)
    (I : LeanCert.Core.IntervalRat)
    (hdom : exprContinuousDomainValid e (Set.Icc (I.lo : ℝ) I.hi)) :
    ContinuousOn (fun x => LeanCert.Core.Expr.eval (fun _ => x) e)
      (Set.Icc (I.lo : ℝ) I.hi) :=
  exprSupportedCore_continuousOn e hsupp hdom

/-- Domain-validity certificate for `log x` on a positive interval. -/
theorem exprContinuousDomainValid_log_var_interval
    (idx : Nat) (I : LeanCert.Core.IntervalRat) (hlo : 0 < I.lo) :
    exprContinuousDomainValid (LeanCert.Core.Expr.log (LeanCert.Core.Expr.var idx))
      (Set.Icc (I.lo : ℝ) I.hi) := by
  constructor
  · trivial
  · intro x hx
    simp only [LeanCert.Core.Expr.eval]
    exact lt_of_lt_of_le (by exact_mod_cast hlo) hx.1

/-! ## Metaprogramming: Continuity Proof Generation

Generate proof terms of `ContinuousOn (fun x => Expr.eval (fun _ => x) e) (Set.Icc lo hi)`
by applying `exprContinuousCore_continuousOn_Icc` with an automatically generated
`ExprContinuousCore` proof.

Note: We use `ExprContinuousCore` (not `ExprSupportedCore`) because `inv` is not continuous
everywhere, and `ExprContinuousCore` excludes `inv`.
-/

/-- Generate a proof of `ExprContinuousCore e_ast` by matching on the AST structure.

    This is similar to `mkSupportedCoreProof` but for the `ExprContinuousCore` predicate
    which excludes `inv` (since 1/x is not continuous at 0).

    Supported: const, var, add, mul, neg, sin, cos, exp, sqrt, sinh, cosh,
    tanh, erf, namedConst
    Not supported: inv, log, atan, arsinh, atanh -/
partial def mkContinuousCoreProof (e_ast : Lean.Expr) : MetaM Lean.Expr := do
  -- Get the head constant and arguments
  let fn := e_ast.getAppFn
  let args := e_ast.getAppArgs

  -- Match on AST constructors
  if fn.isConstOf ``LeanCert.Core.Expr.const then
    let q := args[0]!
    mkAppM ``ExprContinuousCore.const #[q]

  else if fn.isConstOf ``LeanCert.Core.Expr.var then
    let idx := args[0]!
    mkAppM ``ExprContinuousCore.var #[idx]

  else if fn.isConstOf ``LeanCert.Core.Expr.add then
    let e₁ := args[0]!
    let e₂ := args[1]!
    let h₁ ← mkContinuousCoreProof e₁
    let h₂ ← mkContinuousCoreProof e₂
    mkAppM ``ExprContinuousCore.add #[h₁, h₂]

  else if fn.isConstOf ``LeanCert.Core.Expr.mul then
    let e₁ := args[0]!
    let e₂ := args[1]!
    let h₁ ← mkContinuousCoreProof e₁
    let h₂ ← mkContinuousCoreProof e₂
    mkAppM ``ExprContinuousCore.mul #[h₁, h₂]

  else if fn.isConstOf ``LeanCert.Core.Expr.neg then
    let e := args[0]!
    let h ← mkContinuousCoreProof e
    mkAppM ``ExprContinuousCore.neg #[h]

  else if fn.isConstOf ``LeanCert.Core.Expr.sin then
    let e := args[0]!
    let h ← mkContinuousCoreProof e
    mkAppM ``ExprContinuousCore.sin #[h]

  else if fn.isConstOf ``LeanCert.Core.Expr.cos then
    let e := args[0]!
    let h ← mkContinuousCoreProof e
    mkAppM ``ExprContinuousCore.cos #[h]

  else if fn.isConstOf ``LeanCert.Core.Expr.exp then
    let e := args[0]!
    let h ← mkContinuousCoreProof e
    mkAppM ``ExprContinuousCore.exp #[h]

  else if fn.isConstOf ``LeanCert.Core.Expr.log then
    throwError "Cannot generate ExprContinuousCore proof for: {e_ast}\n\
                Expression contains `log` which is not continuous at 0.\n\
                Continuity proofs for expressions with log require restricted domains."

  else if fn.isConstOf ``LeanCert.Core.Expr.sqrt then
    let e := args[0]!
    let h ← mkContinuousCoreProof e
    mkAppM ``ExprContinuousCore.sqrt #[h]

  else if fn.isConstOf ``LeanCert.Core.Expr.sinh then
    let e := args[0]!
    let h ← mkContinuousCoreProof e
    mkAppM ``ExprContinuousCore.sinh #[h]

  else if fn.isConstOf ``LeanCert.Core.Expr.cosh then
    let e := args[0]!
    let h ← mkContinuousCoreProof e
    mkAppM ``ExprContinuousCore.cosh #[h]

  else if fn.isConstOf ``LeanCert.Core.Expr.tanh then
    let e := args[0]!
    let h ← mkContinuousCoreProof e
    mkAppM ``ExprContinuousCore.tanh #[h]

  else if fn.isConstOf ``LeanCert.Core.Expr.erf then
    let e := args[0]!
    let h ← mkContinuousCoreProof e
    mkAppM ``ExprContinuousCore.erf #[h]

  else if fn.isConstOf ``LeanCert.Core.Expr.namedConst then
    let c := args[0]!
    mkAppM ``ExprContinuousCore.namedConst #[c]

  else if fn.isConstOf ``LeanCert.Core.Expr.inv then
    throwError "Cannot generate ExprContinuousCore proof for: {e_ast}\n\
                Expression contains `inv` which is not continuous at 0.\n\
                Continuity proofs for expressions with division require restricted domains."

  else
    throwError "Cannot generate ExprContinuousCore proof for: {e_ast}\n\
                This expression contains unsupported operations (atan, arsinh, atanh, sinc, or partial-domain operations)."

/-- Generate a ContinuousOn proof for an expression on an interval.

    Given:
    - `e_ast` : the AST expression (Lean.Expr representing LeanCert.Core.Expr)
    - `interval` : the interval expression (Lean.Expr representing IntervalRat)

    Returns a proof of:
    `ContinuousOn (fun x => Expr.eval (fun _ => x) e) (Set.Icc I.lo I.hi)`

    This works by:
    1. Generating an ExprContinuousCore proof for the AST
    2. Applying exprContinuousCore_continuousOn_interval

    Note: This will fail for expressions containing `inv` since 1/x is not continuous at 0.
-/
def mkContinuousOnProof (e_ast : Lean.Expr) (interval : Lean.Expr) : MetaM Lean.Expr := do
  -- Generate the ExprContinuousCore proof
  let contProof ← mkContinuousCoreProof e_ast
  -- Apply the continuity theorem
  mkAppM ``exprContinuousCore_continuousOn_interval #[e_ast, contProof, interval]

/-- Generate `exprContinuousDomainValid` for restricted-domain expressions.

Currently this supports the common positive-domain root/integration case
`log x` on an `IntervalRat` with positive lower endpoint, and recursively
passes through total constructors. -/
partial def mkContinuousDomainValidProof (e_ast : Lean.Expr) (interval : Lean.Expr) :
    MetaM Lean.Expr := do
  let fn := e_ast.getAppFn
  let args := e_ast.getAppArgs
  if fn.isConstOf ``LeanCert.Core.Expr.const ||
      fn.isConstOf ``LeanCert.Core.Expr.var ||
      fn.isConstOf ``LeanCert.Core.Expr.namedConst then
    return mkConst ``True.intro
  else if fn.isConstOf ``LeanCert.Core.Expr.add ||
      fn.isConstOf ``LeanCert.Core.Expr.mul then
    let h₁ ← mkContinuousDomainValidProof args[0]! interval
    let h₂ ← mkContinuousDomainValidProof args[1]! interval
    mkAppM ``And.intro #[h₁, h₂]
  else if fn.isConstOf ``LeanCert.Core.Expr.neg ||
      fn.isConstOf ``LeanCert.Core.Expr.exp ||
      fn.isConstOf ``LeanCert.Core.Expr.sin ||
      fn.isConstOf ``LeanCert.Core.Expr.cos ||
      fn.isConstOf ``LeanCert.Core.Expr.atan ||
      fn.isConstOf ``LeanCert.Core.Expr.arsinh ||
      fn.isConstOf ``LeanCert.Core.Expr.atanh ||
      fn.isConstOf ``LeanCert.Core.Expr.sinc ||
      fn.isConstOf ``LeanCert.Core.Expr.erf ||
      fn.isConstOf ``LeanCert.Core.Expr.sinh ||
      fn.isConstOf ``LeanCert.Core.Expr.cosh ||
      fn.isConstOf ``LeanCert.Core.Expr.tanh ||
      fn.isConstOf ``LeanCert.Core.Expr.sqrt ||
      fn.isConstOf ``LeanCert.Core.Expr.inv then
    mkContinuousDomainValidProof args[0]! interval
  else if fn.isConstOf ``LeanCert.Core.Expr.log then
    let arg := args[0]!
    let argFn := arg.getAppFn
    let argArgs := arg.getAppArgs
    if argFn.isConstOf ``LeanCert.Core.Expr.var && argArgs.size ≥ 1 then
      let lo ← mkAppM ``IntervalRat.lo #[interval]
      let hloTy ← mkAppM ``LT.lt #[toExpr (0 : ℚ), lo]
      let hlo ← mkDecideProof hloTy
      mkAppM ``exprContinuousDomainValid_log_var_interval #[argArgs[0]!, interval, hlo]
    else
      throwError "Cannot generate restricted-domain continuity proof for log argument: {arg}"
  else
    throwError "Cannot generate restricted-domain continuity proof for: {e_ast}"

/-- Generate a ContinuousOn proof, falling back to restricted-domain continuity
for supported-core expressions such as `log x` on positive intervals. -/
def mkContinuousOnProofWithDomain (e_ast : Lean.Expr) (interval : Lean.Expr) : MetaM Lean.Expr := do
  try
    mkContinuousOnProof e_ast interval
  catch _ =>
    let supportProof ← mkSupportedCoreProof e_ast
    let domainProof ← mkContinuousDomainValidProof e_ast interval
    mkAppM ``exprSupportedCore_continuousOn_interval #[e_ast, supportProof, interval, domainProof]

/-- Alternative: generate ContinuousOn proof with explicit lo/hi bounds -/
def mkContinuousOnProofIcc (e_ast : Lean.Expr) (lo hi : Lean.Expr) : MetaM Lean.Expr := do
  let contProof ← mkContinuousCoreProof e_ast
  mkAppM ``exprContinuousCore_continuousOn_Icc #[e_ast, contProof, lo, hi]

/-! ## Testing Infrastructure -/

/-- Debug command to test continuity proof generation -/
elab "#check_continuous " t:term " on " lo:term ", " hi:term : command => do
  let (ast, _contProof, contType) ← liftTermElabM do
    -- Elaborate the term
    let t ← elabTerm t none
    let t ← instantiateMVars t
    -- Reify to AST
    let ast ← reify t
    -- Elaborate bounds
    let loExpr ← elabTerm lo (some (mkConst ``Real))
    let hiExpr ← elabTerm hi (some (mkConst ``Real))
    -- Generate continuity proof
    let contProof ← mkContinuousOnProofIcc ast loExpr hiExpr
    let contType ← inferType contProof
    return (ast, contProof, contType)
  logInfo m!"AST: {ast}"
  logInfo m!"Continuity proof type: {contType}"

end LeanCert.Meta
