/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Engine.Algebra.Bezout

/-!
# Golden theorems for algebraic root certificates

Stable wrappers turn a successful executable Bézout check into the common
semantic goal shapes: separability, squarefreeness, coprimality with the formal
derivative, and simplicity of every real root.
-/

namespace LeanCert.Validity.Algebra

open LeanCert.Core
open LeanCert.Engine

/-- A checked Bézout identity certifies separability. -/
theorem verify_separable (P : QPoly) (cert : BezoutCert)
    (h : bezoutCheck P cert = true) : P.toPoly.Separable :=
  bezoutCheck_sound P cert h

/-- A checked Bézout identity certifies squarefreeness. -/
theorem verify_squarefree (P : QPoly) (cert : BezoutCert)
    (h : bezoutCheck P cert = true) : Squarefree P.toPoly :=
  (verify_separable P cert h).squarefree

/-- A checked Bézout identity certifies that `P` and `P'` are coprime. -/
theorem verify_coprime_deriv (P : QPoly) (cert : BezoutCert)
    (h : bezoutCheck P cert = true) :
    IsCoprime P.toPoly P.toPoly.derivative :=
  (Polynomial.separable_def P.toPoly).mp (verify_separable P cert h)

/-- Every real root of a polynomial with a checked Bézout certificate is
simple, stated using Mathlib polynomial evaluation. -/
theorem verify_real_roots_simple (P : QPoly) (cert : BezoutCert)
    (h : bezoutCheck P cert = true) :
    ∀ x : ℝ, Polynomial.aeval x P.toPoly = 0 →
      Polynomial.aeval x P.toPoly.derivative ≠ 0 := by
  intro x hx
  exact (verify_separable P cert h).aeval_derivative_ne_zero hx

/-- Simplicity in the form consumed by LeanCert's analytic `Expr` layer. -/
theorem verify_toExpr_roots_simple (P : QPoly) (cert : BezoutCert)
    (h : bezoutCheck P cert = true) :
    ∀ x : ℝ, Expr.eval (fun _ => x) P.toExpr = 0 →
      deriv (fun t : ℝ => Expr.eval (fun _ => t) P.toExpr) x ≠ 0 := by
  intro x hx
  rw [QPoly.eval_toExpr] at hx
  rw [QPoly.deriv_eval_toExpr]
  exact verify_real_roots_simple P cert h x hx

end LeanCert.Validity.Algebra
