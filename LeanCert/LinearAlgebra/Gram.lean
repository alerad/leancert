/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Finite Gram matrices and exact kernel certificates

These structural theorems cover finite feature representations. They do not
claim support for interval-valued parameters or approximate residual bounds.
-/

namespace LeanCert

/-- The Gram matrix of a finite real feature table. Rows index samples and
columns index features. -/
noncomputable def gramMatrix {samples features : Type*} [Fintype features]
    (feature : Matrix samples features ℝ) : Matrix samples samples ℝ :=
  feature * feature.transpose

/-- Every finite real Gram matrix is positive semidefinite. -/
theorem gramMatrix_posSemidef {samples features : Type*} [Finite samples]
    [Fintype features] (feature : Matrix samples features ℝ) :
    (gramMatrix feature).PosSemidef := by
  simpa [gramMatrix] using Matrix.posSemidef_self_mul_conjTranspose feature

/-- Add a strictly positive diagonal ridge to a finite Gram matrix. -/
noncomputable def regularizedGramMatrix {samples features : Type*}
    [Fintype features] [DecidableEq samples]
    (feature : Matrix samples features ℝ) (ridge : samples → ℝ) :
    Matrix samples samples ℝ :=
  gramMatrix feature + Matrix.diagonal ridge

/-- A pointwise-positive diagonal regularizer turns any finite Gram matrix
into a positive-definite matrix. -/
theorem regularizedGramMatrix_posDef {samples features : Type*}
    [Fintype samples] [Fintype features] [DecidableEq samples]
    (feature : Matrix samples features ℝ) (ridge : samples → ℝ)
    (hridge : ∀ i, 0 < ridge i) :
    (regularizedGramMatrix feature ridge).PosDef := by
  exact Matrix.PosDef.posSemidef_add (gramMatrix_posSemidef feature)
    (Matrix.PosDef.diagonal hridge)

end LeanCert
