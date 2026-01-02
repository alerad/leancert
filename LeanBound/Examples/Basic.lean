/-
Copyright (c) 2024 LeanBound Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanBound Contributors
-/
import LeanBound.Numerics.IntervalEval
import LeanBound.Numerics.AD

/-!
# Basic Examples

This file demonstrates LeanBound's verified interval arithmetic core.

All examples in this file use only the fully-verified subset of expressions:
const, var, add, mul, neg, sin, cos

The correctness theorems (evalInterval_correct, evalDual_val_correct) are
FULLY PROVED with no sorry, no axioms for this subset.
-/

namespace LeanBound.Examples.Basic

open LeanBound.Core
open LeanBound.Numerics

/-! ### Building supported expressions -/

/-- The expression x² (x squared) -/
def xSq : Expr := Expr.mul (Expr.var 0) (Expr.var 0)

/-- Proof that x² is in the supported subset -/
def xSq_supported : ExprSupported xSq :=
  ExprSupported.mul (ExprSupported.var 0) (ExprSupported.var 0)

/-- The expression x² + 2x + 1 = (x + 1)² -/
def exprSquare : Expr :=
  Expr.add (Expr.add (Expr.mul (Expr.var 0) (Expr.var 0))
                     (Expr.mul (Expr.const 2) (Expr.var 0)))
           (Expr.const 1)

/-- Proof that x² + 2x + 1 is in the supported subset -/
def exprSquare_supported : ExprSupported exprSquare :=
  ExprSupported.add
    (ExprSupported.add
      (ExprSupported.mul (ExprSupported.var 0) (ExprSupported.var 0))
      (ExprSupported.mul (ExprSupported.const 2) (ExprSupported.var 0)))
    (ExprSupported.const 1)

/-- The expression sin(x) + cos(x) -/
def exprSinCos : Expr :=
  Expr.add (Expr.sin (Expr.var 0)) (Expr.cos (Expr.var 0))

/-- Proof that sin(x) + cos(x) is in the supported subset -/
def exprSinCos_supported : ExprSupported exprSinCos :=
  ExprSupported.add
    (ExprSupported.sin (ExprSupported.var 0))
    (ExprSupported.cos (ExprSupported.var 0))

/-! ### Interval construction -/

/-- The unit interval [0, 1] -/
def I01 : IntervalRat := ⟨0, 1, by norm_num⟩

/-- The interval [-1, 1] -/
def symInterval : IntervalRat := ⟨-1, 1, by norm_num⟩

/-- A small interval around 0: [-1/10, 1/10] -/
def smallInterval : IntervalRat := ⟨-1/10, 1/10, by norm_num⟩

/-! ### Interval membership examples -/

example : (1 : ℝ) / 2 ∈ I01 := by
  simp only [IntervalRat.mem_def, I01]
  norm_num

example : (0 : ℝ) ∈ symInterval := by
  simp only [IntervalRat.mem_def, symInterval]
  norm_num

/-! ### Expression evaluation examples -/

/-- Evaluate x² + 2x + 1 at x = 2, should give 9 -/
example : Expr.eval (fun _ => 2) exprSquare = 9 := by
  simp only [exprSquare, Expr.eval_add, Expr.eval_mul, Expr.eval_var, Expr.eval_const]
  norm_num

/-- Evaluate x² at x = 3, should give 9 -/
example : Expr.eval (fun _ => 3) xSq = 9 := by
  simp only [xSq, Expr.eval_mul, Expr.eval_var]
  norm_num

/-! ### Verified interval evaluation -/

/-- Key example: x² evaluated over [0, 1] gives a value in the computed interval.
    This uses the FULLY PROVED evalInterval1_correct theorem. -/
example (x : ℝ) (hx : x ∈ I01) :
    Expr.eval (fun _ => x) xSq ∈ evalInterval1 xSq I01 :=
  evalInterval1_correct xSq xSq_supported x I01 hx

/-- x² + 2x + 1 evaluated over [0, 1] gives a value in the computed interval. -/
example (x : ℝ) (hx : x ∈ I01) :
    Expr.eval (fun _ => x) exprSquare ∈ evalInterval1 exprSquare I01 :=
  evalInterval1_correct exprSquare exprSquare_supported x I01 hx

/-- sin(x) + cos(x) evaluated over [-1, 1] gives a value in the computed interval. -/
example (x : ℝ) (hx : x ∈ symInterval) :
    Expr.eval (fun _ => x) exprSinCos ∈ evalInterval1 exprSinCos symInterval :=
  evalInterval1_correct exprSinCos exprSinCos_supported x symInterval hx

/-! ### Using smart constructors -/

/-- Build x² using smart constructors that carry the support proof -/
def xSq' : { e : Expr // ExprSupported e } :=
  mkMul (mkVar 0) (mkVar 0)

/-- Using smart constructors makes proofs trivial -/
example (x : ℝ) (hx : x ∈ I01) :
    Expr.eval (fun _ => x) xSq'.val ∈ evalInterval1 xSq'.val I01 :=
  evalInterval1_correct xSq'.val xSq'.property x I01 hx

/-! ### Multi-variable example -/

/-- The expression x * y (product of two variables) -/
def exprXY : Expr := Expr.mul (Expr.var 0) (Expr.var 1)

def exprXY_supported : ExprSupported exprXY :=
  ExprSupported.mul (ExprSupported.var 0) (ExprSupported.var 1)

/-- Multi-variable interval environment -/
def ρ_xy : IntervalEnv := fun i => if i = 0 then I01 else symInterval

/-- Verified evaluation with multiple variables -/
example (x y : ℝ) (hx : x ∈ I01) (hy : y ∈ symInterval) :
    Expr.eval (fun i => if i = 0 then x else y) exprXY ∈
    evalInterval exprXY ρ_xy := by
  apply evalInterval_correct exprXY exprXY_supported
  intro i
  simp only [ρ_xy]
  split_ifs with h
  · exact hx
  · exact hy

end LeanBound.Examples.Basic
