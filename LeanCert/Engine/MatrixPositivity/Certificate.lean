/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Integer
import Mathlib.Algebra.Order.Star.Real

/-!
# Exact matrix positivity certificates

This module contains the trusted, executable certificate boundary for exact
positive-semidefinite and positive-definite matrix claims. Candidate discovery
is deliberately kept separate: every accepted result follows from one Boolean
checker and the corresponding soundness theorem below.
-/

namespace LeanCert.Engine

open Matrix

/-- An exact rational `L * D * Lᵀ` certificate. -/
structure LDLTCertificate (n : Nat) where
  lower : Matrix (Fin n) (Fin n) ℚ
  diagonal : Fin n → ℚ
  deriving Repr

/-- An exact rational Gram certificate with a dimension-erased row count. -/
structure GramCertificate (n : Nat) where
  rows : Nat
  factor : Matrix (Fin rows) (Fin n) ℚ

/-- Exact certificate forms accepted by the PSD checker. -/
inductive PSDCertificate (n : Nat) where
  | gram (certificate : GramCertificate n)
  | ldlt (certificate : LDLTCertificate n)

def LDLTCertificate.matrix {n : Nat} (certificate : LDLTCertificate n) :
    Matrix (Fin n) (Fin n) ℚ :=
  certificate.lower * Matrix.diagonal certificate.diagonal * certificate.lower.transpose

def GramCertificate.matrix {n : Nat} (certificate : GramCertificate n) :
    Matrix (Fin n) (Fin n) ℚ :=
  certificate.factor.transpose * certificate.factor

def PSDCertificate.matrix {n : Nat} (certificate : PSDCertificate n) :
    Matrix (Fin n) (Fin n) ℚ :=
  match certificate with
  | .gram certificate => certificate.matrix
  | .ldlt certificate => certificate.matrix

/-- Exact entrywise casting of a rational matrix to the reals. -/
noncomputable def ratCastMatrix {m n : Type*} (matrix : Matrix m n ℚ) : Matrix m n ℝ :=
  matrix.map fun value => (value : ℝ)

private theorem ratCastMatrix_mul {l m n : Type*} [Fintype m]
    (left : Matrix l m ℚ) (right : Matrix m n ℚ) :
    ratCastMatrix (left * right) = ratCastMatrix left * ratCastMatrix right := by
  ext i j
  simp [ratCastMatrix, Matrix.mul_apply]

private theorem ratCastMatrix_transpose {m n : Type*} (matrix : Matrix m n ℚ) :
    ratCastMatrix matrix.transpose = (ratCastMatrix matrix).transpose := by
  ext i j
  rfl

private theorem ratCastMatrix_diagonal {n : Type*} [DecidableEq n] (diagonal : n → ℚ) :
    ratCastMatrix (Matrix.diagonal diagonal) =
      Matrix.diagonal (fun i => (diagonal i : ℝ)) := by
  ext i j
  by_cases h : i = j <;> simp [ratCastMatrix, Matrix.diagonal, h]

/-- Check an exact Gram or LDLᵀ PSD certificate. -/
def matrixPSDCheck {n : Nat} (matrix : Matrix (Fin n) (Fin n) ℚ)
    (certificate : PSDCertificate n) : Bool :=
  match certificate with
  | .gram certificate => decide (matrix = certificate.matrix)
  | .ldlt certificate =>
      decide (matrix = certificate.matrix) &&
        decide (∀ i, 0 ≤ certificate.diagonal i)

/-- Check an exact LDLᵀ positive-definiteness certificate. -/
def matrixPosDefCheck {n : Nat} (matrix : Matrix (Fin n) (Fin n) ℚ)
    (certificate : LDLTCertificate n) : Bool :=
  decide (matrix = certificate.matrix) &&
    decide (∀ i, 0 < certificate.diagonal i) &&
    decide (certificate.lower.det ≠ 0)

private theorem ldlt_posSemidef_of_eq {n : Nat}
    (matrix lower : Matrix (Fin n) (Fin n) ℚ) (diagonal : Fin n → ℚ)
    (hmatrix : matrix = lower * Matrix.diagonal diagonal * lower.transpose)
    (hdiagonal : ∀ i, 0 ≤ diagonal i) : (ratCastMatrix matrix).PosSemidef := by
  have hmatrixReal := congrArg ratCastMatrix hmatrix
  have hdiagonalReal : ∀ i, 0 ≤ (diagonal i : ℝ) := fun i => Rat.cast_nonneg.mpr (hdiagonal i)
  have hpositive :=
    (Matrix.PosSemidef.diagonal hdiagonalReal).mul_mul_conjTranspose_same
      (ratCastMatrix lower)
  rw [hmatrixReal]
  rw [ratCastMatrix_mul, ratCastMatrix_mul, ratCastMatrix_diagonal,
    ratCastMatrix_transpose]
  simpa using hpositive

private theorem ldlt_posDef_of_eq {n : Nat}
    (matrix lower : Matrix (Fin n) (Fin n) ℚ) (diagonal : Fin n → ℚ)
    (hmatrix : matrix = lower * Matrix.diagonal diagonal * lower.transpose)
    (hdiagonal : ∀ i, 0 < diagonal i) (hlower : lower.det ≠ 0) :
    (ratCastMatrix matrix).PosDef := by
  have hmatrixReal := congrArg ratCastMatrix hmatrix
  have hdiagonalReal : ∀ i, 0 < (diagonal i : ℝ) := fun i => Rat.cast_pos.mpr (hdiagonal i)
  have hlowerDetReal : (ratCastMatrix lower).det ≠ 0 := by
    have hcast : (lower.det : ℝ) ≠ 0 := (Rat.cast_ne_zero (α := ℝ)).mpr hlower
    simpa only [ratCastMatrix, Rat.cast_det] using hcast
  have hlowerUnit : IsUnit (ratCastMatrix lower) :=
    (ratCastMatrix lower).isUnit_iff_isUnit_det.mpr (isUnit_iff_ne_zero.mpr hlowerDetReal)
  have hinjective : Function.Injective (ratCastMatrix lower).vecMul :=
    Matrix.vecMul_injective_iff_isUnit.mpr hlowerUnit
  have hpositive :=
    (Matrix.PosDef.diagonal hdiagonalReal).mul_mul_conjTranspose_same hinjective
  rw [hmatrixReal]
  rw [ratCastMatrix_mul, ratCastMatrix_mul, ratCastMatrix_diagonal,
    ratCastMatrix_transpose]
  simpa using hpositive

/-- Golden checker theorem for exact rational PSD certificates. -/
theorem matrixPSDCheck_sound {n : Nat} (matrix : Matrix (Fin n) (Fin n) ℚ)
    (certificate : PSDCertificate n) (hcheck : matrixPSDCheck matrix certificate = true) :
    (ratCastMatrix matrix).PosSemidef := by
  cases certificate with
  | gram certificate =>
      have hmatrix : matrix = certificate.matrix := of_decide_eq_true hcheck
      have hmatrixReal := congrArg ratCastMatrix hmatrix
      rw [hmatrixReal]
      change (ratCastMatrix (certificate.factor.transpose * certificate.factor)).PosSemidef
      rw [ratCastMatrix_mul, ratCastMatrix_transpose]
      simpa using
        Matrix.posSemidef_conjTranspose_mul_self (ratCastMatrix certificate.factor)
  | ldlt certificate =>
      simp only [matrixPSDCheck, Bool.and_eq_true, decide_eq_true_eq] at hcheck
      exact ldlt_posSemidef_of_eq matrix certificate.lower certificate.diagonal
        hcheck.1 hcheck.2

/-- Golden checker theorem for exact rational positive-definiteness certificates. -/
theorem matrixPosDefCheck_sound {n : Nat} (matrix : Matrix (Fin n) (Fin n) ℚ)
    (certificate : LDLTCertificate n)
    (hcheck : matrixPosDefCheck matrix certificate = true) :
    (ratCastMatrix matrix).PosDef := by
  simp only [matrixPosDefCheck, Bool.and_eq_true, decide_eq_true_eq] at hcheck
  exact ldlt_posDef_of_eq matrix certificate.lower certificate.diagonal
    hcheck.1.1 hcheck.1.2 hcheck.2

end LeanCert.Engine
