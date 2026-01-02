/-
Copyright (c) 2024 LeanBound Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanBound Contributors
-/
import LeanBound.Numerics.AD
import LeanBound.Numerics.IntervalEvalReal

/-!
# Calculus Examples

This file demonstrates automatic differentiation and derivative
bounds using LeanBound.

## Verified AD Examples

The `evalDual_val_correct` theorem is **FULLY PROVED** for the supported
expression subset {const, var, add, mul, neg, sin, cos}. This demonstrates
verified forward-mode automatic differentiation with interval bounds.
-/

namespace LeanBound.Examples.Calculus

open LeanBound.Core
open LeanBound.Numerics

/-! ### Supported expressions for AD -/

/-- The expression x² -/
def exprXSquared : Expr := Expr.mul (Expr.var 0) (Expr.var 0)

/-- Proof that x² is in the supported subset -/
def exprXSquared_supported : ExprSupported exprXSquared :=
  ExprSupported.mul (ExprSupported.var 0) (ExprSupported.var 0)

/-- The expression x³ = x * x * x -/
def exprXCubed : Expr :=
  Expr.mul (Expr.var 0) (Expr.mul (Expr.var 0) (Expr.var 0))

/-- Proof that x³ is supported -/
def exprXCubed_supported : ExprSupported exprXCubed :=
  ExprSupported.mul (ExprSupported.var 0)
    (ExprSupported.mul (ExprSupported.var 0) (ExprSupported.var 0))

/-- The expression sin(x) * cos(x) -/
def exprSinCos : Expr := Expr.mul (Expr.sin (Expr.var 0)) (Expr.cos (Expr.var 0))

/-- Proof that sin(x)*cos(x) is supported -/
def exprSinCos_supported : ExprSupported exprSinCos :=
  ExprSupported.mul
    (ExprSupported.sin (ExprSupported.var 0))
    (ExprSupported.cos (ExprSupported.var 0))

/-! ### Interval environments for AD -/

/-- Unit interval [0, 1] -/
def I01 : IntervalRat := ⟨0, 1, by norm_num⟩

/-- Create a dual environment for differentiating with respect to x -/
def dualEnv01 : DualEnv := mkDualEnv (fun _ => I01) 0

/-! ### Verified value computation -/

/-- Verified: the value component of dual evaluation is correct.
    For any x ∈ [0,1], the value of x² lies in the computed interval.
    This theorem has NO SORRY. -/
theorem xSquared_dual_val_correct (x : ℝ) (hx : x ∈ I01) :
    Expr.eval (fun _ => x) exprXSquared ∈ (evalDual exprXSquared dualEnv01).val := by
  apply evalDual_val_correct exprXSquared exprXSquared_supported
  intro i
  simp only [dualEnv01, mkDualEnv]
  split_ifs
  · exact hx
  · exact hx

/-- Verified: the value component for x³ is correct -/
theorem xCubed_dual_val_correct (x : ℝ) (hx : x ∈ I01) :
    Expr.eval (fun _ => x) exprXCubed ∈ (evalDual exprXCubed dualEnv01).val := by
  apply evalDual_val_correct exprXCubed exprXCubed_supported
  intro i
  simp only [dualEnv01, mkDualEnv]
  split_ifs
  · exact hx
  · exact hx

/-- Verified: the value component for sin(x)*cos(x) is correct -/
theorem sinCos_dual_val_correct (x : ℝ) (hx : x ∈ I01) :
    Expr.eval (fun _ => x) exprSinCos ∈ (evalDual exprSinCos dualEnv01).val := by
  apply evalDual_val_correct exprSinCos exprSinCos_supported
  intro i
  simp only [dualEnv01, mkDualEnv]
  split_ifs
  · exact hx
  · exact hx

/-! ### Point evaluation examples -/

/-- Evaluate x² at a point with its derivative -/
noncomputable def evalXSquaredAt (q : ℚ) : DualInterval :=
  let I := IntervalRat.singleton q
  evalWithDeriv exprXSquared (fun _ => I) 0

/-- Example: x² at x=3 gives value containing 9.
    The value 3² = 9.

    We prove this by applying the general correctness theorem. -/
example : Expr.eval (fun _ => (3 : ℝ)) exprXSquared ∈ (evalXSquaredAt 3).val := by
  -- Use the general theorem: if 3 ∈ singleton(3), then eval at 3 ∈ val
  have h3 : (3 : ℝ) ∈ IntervalRat.singleton (3 : ℚ) := IntervalRat.mem_singleton 3
  apply evalDual_val_correct exprXSquared exprXSquared_supported
  intro i
  simp only [mkDualEnv]
  split_ifs
  · simp only [DualInterval.varActive]; exact h3
  · simp only [DualInterval.varPassive]; exact h3

/-- The eval of x² at 3 is indeed 9 -/
example : Expr.eval (fun _ => (3 : ℝ)) exprXSquared = 9 := by
  simp only [exprXSquared, Expr.eval_mul, Expr.eval_var]; norm_num

/-! ### Verified exp support via IntervalReal

With the new `IntervalReal` (real-endpoint intervals) and `ExprSupportedExt`,
we can now prove facts about expressions containing exp!
-/

/-- The expression exp(x) -/
def exprExp : Expr := Expr.exp (Expr.var 0)

/-- The expression exp(x²) -/
def exprExpXSquared : Expr := Expr.exp (Expr.mul (Expr.var 0) (Expr.var 0))

/-- Proof that exp(x) is in the extended supported subset -/
def exprExp_supportedExt : ExprSupportedExt exprExp :=
  ExprSupportedExt.exp (ExprSupportedExt.var 0)

/-- Proof that exp(x²) is in the extended supported subset -/
def exprExpXSquared_supportedExt : ExprSupportedExt exprExpXSquared :=
  ExprSupportedExt.exp
    (ExprSupportedExt.mul (ExprSupportedExt.var 0) (ExprSupportedExt.var 0))

/-- Real-endpoint unit interval [0, 1] -/
noncomputable def I01Real : IntervalReal := ⟨0, 1, by norm_num⟩

/-- Verified: exp(x) on [0, 1] gives a value in the computed interval.
    This theorem has NO SORRY - exp is now fully supported! -/
theorem exp_interval_correct (x : ℝ) (hx : x ∈ I01Real) :
    Expr.eval (fun _ => x) exprExp ∈ evalIntervalReal1 exprExp I01Real :=
  evalIntervalReal1_correct exprExp exprExp_supportedExt x I01Real hx

/-- Verified: exp(x²) on [0, 1] gives a value in the computed interval.
    This demonstrates chained exp support! -/
theorem expXSquared_interval_correct (x : ℝ) (hx : x ∈ I01Real) :
    Expr.eval (fun _ => x) exprExpXSquared ∈ evalIntervalReal1 exprExpXSquared I01Real :=
  evalIntervalReal1_correct exprExpXSquared exprExpXSquared_supportedExt x I01Real hx

end LeanBound.Examples.Calculus
