/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Engine.Algebra.QPoly

/-!
# Exact polynomial integral certificates

This module recognizes the rational-polynomial fragment of `LeanCert.Core.Expr`
and checks exact definite integrals using executable rational arithmetic.  The
checker is intentionally small: certificate discovery may happen in tactics or
external tooling, while Lean verifies the reflected polynomial and endpoint
evaluation.
-/

namespace LeanCert.Engine

open LeanCert.Core

namespace QPoly

/-- Recognize a single-variable rational polynomial expression. -/
def ofExpr : Expr → Option QPoly
  | .const q => some (constant q)
  | .var 0 => some X
  | .var _ => none
  | .add e₁ e₂ =>
      match ofExpr e₁, ofExpr e₂ with
      | some p₁, some p₂ => some (p₁.add p₂)
      | _, _ => none
  | .mul e₁ e₂ =>
      match ofExpr e₁, ofExpr e₂ with
      | some p₁, some p₂ => some (p₁.mul p₂)
      | _, _ => none
  | .neg e =>
      match ofExpr e with
      | some p => some ((constant (-1)).mul p)
      | none => none
  | .inv (.const q) => if q = 0 then none else some (constant q⁻¹)
  | _ => none

/-- Successful polynomial recognition preserves real semantics. -/
theorem ofExpr_correct {e : Expr} {p : QPoly} (h : ofExpr e = some p) (x : ℝ) :
    Expr.eval (fun _ => x) e = Expr.eval (fun _ => x) p.toExpr := by
  induction e generalizing p with
  | const q =>
      simp only [ofExpr, Option.some.injEq] at h
      subst p
      rw [eval_toExpr, toPoly_constant, Polynomial.aeval_C]
      rfl
  | var i =>
      cases i with
      | zero =>
          simp only [ofExpr, Option.some.injEq] at h
          subst p
          rw [eval_toExpr, toPoly_X, Polynomial.aeval_X]
          rfl
      | succ i => simp [ofExpr] at h
  | add e₁ e₂ ih₁ ih₂ =>
      cases hp₁ : ofExpr e₁ <;> cases hp₂ : ofExpr e₂ <;>
        simp [ofExpr, hp₁, hp₂] at h
      subst p
      rw [Expr.eval_add, ih₁ hp₁, ih₂ hp₂, eval_toExpr, eval_toExpr,
        eval_toExpr, toPoly_add, map_add]
  | mul e₁ e₂ ih₁ ih₂ =>
      cases hp₁ : ofExpr e₁ <;> cases hp₂ : ofExpr e₂ <;>
        simp [ofExpr, hp₁, hp₂] at h
      subst p
      rw [Expr.eval_mul, ih₁ hp₁, ih₂ hp₂, eval_toExpr, eval_toExpr,
        eval_toExpr, toPoly_mul, map_mul]
  | neg e ih =>
      cases hp₁ : ofExpr e <;> simp [ofExpr, hp₁] at h
      subst p
      rw [Expr.eval_neg, ih hp₁, eval_toExpr, eval_toExpr, toPoly_mul,
        toPoly_constant, map_mul, Polynomial.aeval_C]
      norm_num
  | inv e ih =>
      cases e with
      | const q =>
          simp only [ofExpr] at h
          split at h
          · contradiction
          · simp only [Option.some.injEq] at h
            subst p
            rw [Expr.eval_inv, eval_toExpr, toPoly_constant, Polynomial.aeval_C]
            norm_num
      | var i => simp [ofExpr] at h
      | add e₁ e₂ => simp [ofExpr] at h
      | mul e₁ e₂ => simp [ofExpr] at h
      | neg e => simp [ofExpr] at h
      | inv e => simp [ofExpr] at h
      | exp e => simp [ofExpr] at h
      | sin e => simp [ofExpr] at h
      | cos e => simp [ofExpr] at h
      | log e => simp [ofExpr] at h
      | atan e => simp [ofExpr] at h
      | arsinh e => simp [ofExpr] at h
      | atanh e => simp [ofExpr] at h
      | sinc e => simp [ofExpr] at h
      | erf e => simp [ofExpr] at h
      | sinh e => simp [ofExpr] at h
      | cosh e => simp [ofExpr] at h
      | tanh e => simp [ofExpr] at h
      | sqrt e => simp [ofExpr] at h
      | namedConst c => simp [ofExpr] at h
  | exp e ih => simp [ofExpr] at h
  | sin e ih => simp [ofExpr] at h
  | cos e ih => simp [ofExpr] at h
  | log e ih => simp [ofExpr] at h
  | atan e ih => simp [ofExpr] at h
  | arsinh e ih => simp [ofExpr] at h
  | atanh e ih => simp [ofExpr] at h
  | sinc e ih => simp [ofExpr] at h
  | erf e ih => simp [ofExpr] at h
  | sinh e ih => simp [ofExpr] at h
  | cosh e ih => simp [ofExpr] at h
  | tanh e ih => simp [ofExpr] at h
  | sqrt e ih => simp [ofExpr] at h
  | namedConst c => simp [ofExpr] at h

/-- Boolean checker for an exact rational-polynomial definite integral. -/
def checkExactIntegral (e : Expr) (a b value : ℚ) : Bool :=
  match ofExpr e with
  | some p => decide (p.integralRat a b = value)
  | none => false

/-- Golden theorem for exact rational-polynomial integration certificates. -/
theorem integral_eq_of_check (e : Expr) (a b value : ℚ)
    (hcheck : checkExactIntegral e a b value = true) :
    (∫ x in (a : ℝ)..(b : ℝ), Expr.eval (fun _ => x) e) = (value : ℝ) := by
  unfold checkExactIntegral at hcheck
  cases hpoly : ofExpr e with
  | none => simp [hpoly] at hcheck
  | some p =>
      simp only [hpoly, decide_eq_true_eq] at hcheck
      rw [show (fun x : ℝ => Expr.eval (fun _ => x) e) =
          (fun x : ℝ => Expr.eval (fun _ => x) p.toExpr) by
        funext x
        exact ofExpr_correct hpoly x]
      rw [integral_eval_toExpr]
      exact_mod_cast hcheck

end QPoly
end LeanCert.Engine
