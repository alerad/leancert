/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Validity.Algebra

/-!
# Exact algebraic certificate regressions

For `P = x^3 - 2`, the integer-coefficient identity

`3 P - x P' = -6`

certifies that every root is simple. The negative cases model corrupted CAS
output by changing a cofactor or the claimed scalar.
-/

namespace LeanCert.Test.AlgebraicBezout

open LeanCert.Engine
open LeanCert.Validity.Algebra

def cubic : QPoly := ⟨#[-2, 0, 0, 1]⟩

def certificate : BezoutCert where
  A := ⟨#[3]⟩
  B := ⟨#[0, -1]⟩
  c := -6

def corruptedCofactor : BezoutCert where
  A := ⟨#[4]⟩
  B := certificate.B
  c := certificate.c

def corruptedScalar : BezoutCert where
  A := certificate.A
  B := certificate.B
  c := 6

def zeroScalar : BezoutCert where
  A := ⟨#[0]⟩
  B := ⟨#[0]⟩
  c := 0

example : bezoutCheck cubic certificate = true := by native_decide
example : bezoutCheck cubic corruptedCofactor = false := by native_decide
example : bezoutCheck cubic corruptedScalar = false := by native_decide
example : bezoutCheck cubic zeroScalar = false := by native_decide

-- Trailing zeros are representational only and are removed before comparison.
example : bezoutCheck ⟨#[-2, 0, 0, 1, 0, 0]⟩ certificate = true := by native_decide

example : cubic.toPoly.Separable := by
  exact verify_separable cubic certificate (by native_decide)

example : Squarefree cubic.toPoly := by
  exact verify_squarefree cubic certificate (by native_decide)

example : IsCoprime cubic.toPoly cubic.toPoly.derivative := by
  exact verify_coprime_deriv cubic certificate (by native_decide)

example (x : ℝ) (hx : Polynomial.aeval x cubic.toPoly = 0) :
    Polynomial.aeval x cubic.toPoly.derivative ≠ 0 := by
  exact verify_real_roots_simple cubic certificate (by native_decide) x hx

example (x : ℝ) (hx : LeanCert.Core.Expr.eval (fun _ => x) cubic.toExpr = 0) :
    deriv (fun t : ℝ => LeanCert.Core.Expr.eval (fun _ => t) cubic.toExpr) x ≠ 0 := by
  exact verify_toExpr_roots_simple cubic certificate (by native_decide) x hx

example : (QPoly.mk #[1, 2, 0, 0]).trim = QPoly.mk #[1, 2] := by native_decide
example : cubic.derivative = QPoly.mk #[0, 0, 3] := by native_decide
example : (QPoly.mk #[1, 1]).mul (QPoly.mk #[-1, 1]) = QPoly.mk #[-1, 0, 1] := by
  native_decide

end LeanCert.Test.AlgebraicBezout
