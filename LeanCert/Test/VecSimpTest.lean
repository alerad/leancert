/-
Copyright (c) 2024 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Tactic.VecSimp
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Tests for vec_simp, vec_simp!, and dite_simp tactics

This file tests the vector and dite simplification tactics:

* `vec_simp` - Reduces `![a, b, c] ⟨i, proof⟩` to the i-th element
* `vec_simp!` - Aggressive variant that also simplifies `dite` conditions
* `dite_simp` - Standalone tactic for simplifying `dite` with decidable literal conditions
-/

namespace VecSimp.Test

-- Basic indexing with literals
example : (![1, 2, 3] : Fin 3 → ℕ) ⟨0, by omega⟩ = 1 := by vec_simp
example : (![1, 2, 3] : Fin 3 → ℕ) ⟨1, by omega⟩ = 2 := by vec_simp
example : (![1, 2, 3] : Fin 3 → ℕ) ⟨2, by omega⟩ = 3 := by vec_simp

-- Symbolic elements
example (a b c : ℝ) : (![a, b, c] : Fin 3 → ℝ) ⟨0, by omega⟩ = a := by vec_simp
example (a b c : ℝ) : (![a, b, c] : Fin 3 → ℝ) ⟨1, by omega⟩ = b := by vec_simp

-- Longer vectors
example : (![1, 2, 3, 4, 5] : Fin 5 → ℕ) ⟨3, by omega⟩ = 4 := by vec_simp

-- In expressions
example (a b c : ℝ) : (![a, b, c] : Fin 3 → ℝ) ⟨0, by omega⟩ + 1 = a + 1 := by vec_simp

/-! ### Combination with ring -/

variable (a₀ a₁ a₂ : ℝ)

-- Product of indexed elements
example : (![a₀, a₁, a₂] : Fin 3 → ℝ) ⟨0, by omega⟩ * (![a₀, a₁, a₂] : Fin 3 → ℝ) ⟨1, by omega⟩ +
          (![a₀, a₁, a₂] : Fin 3 → ℝ) ⟨1, by omega⟩ * (![a₀, a₁, a₂] : Fin 3 → ℝ) ⟨0, by omega⟩ = 2 * a₀ * a₁ := by
  vec_simp; ring

-- Squared term
example (c : ℝ) :
    (![a₀, a₁, a₂] : Fin 3 → ℝ) ⟨0, by omega⟩ * (![a₀, a₁, a₂] : Fin 3 → ℝ) ⟨0, by omega⟩ - c = a₀^2 - c := by
  vec_simp; ring

end VecSimp.Test

/-! ## Tests for dite_simp -/

namespace DiteSimp.Test

-- Basic dite with ≤ (true case)
example (f : (1 : ℕ) ≤ 2 → ℕ) (g : ¬(1 : ℕ) ≤ 2 → ℕ) :
    (if h : (1 : ℕ) ≤ 2 then f h else g h) = f (by omega) := by
  dite_simp

-- Basic dite with ≤ (false case)
example (f : (3 : ℕ) ≤ 2 → ℕ) (g : ¬(3 : ℕ) ≤ 2 → ℕ) :
    (if h : (3 : ℕ) ≤ 2 then f h else g h) = g (by omega) := by
  dite_simp

-- dite with < (true case)
example (f : (1 : ℕ) < 3 → ℕ) (g : ¬(1 : ℕ) < 3 → ℕ) :
    (if h : (1 : ℕ) < 3 then f h else g h) = f (by omega) := by
  dite_simp

-- dite with < (false case)
example (f : (5 : ℕ) < 3 → ℕ) (g : ¬(5 : ℕ) < 3 → ℕ) :
    (if h : (5 : ℕ) < 3 then f h else g h) = g (by omega) := by
  dite_simp

-- Edge case: equality
example (f : (2 : ℕ) ≤ 2 → ℕ) (g : ¬(2 : ℕ) ≤ 2 → ℕ) :
    (if h : (2 : ℕ) ≤ 2 then f h else g h) = f (by omega) := by
  dite_simp

-- Multiple dite in sequence (replaces the verbose show pattern)
example (f : (1 : ℕ) ≤ 2 → (2 : ℕ) ≤ 2 → ℕ) :
    (if h₁ : (1 : ℕ) ≤ 2 then
      if h₂ : (2 : ℕ) ≤ 2 then f h₁ h₂
      else 0
    else 0) = f (by omega) (by omega) := by
  dite_simp

end DiteSimp.Test

/-! ## Tests for vec_simp! (combined) -/

namespace VecSimpBang.Test

-- Combined: vector indexing inside dite
example :
    (if _ : (1 : ℕ) ≤ 2 then (![1, 2, 3] : Fin 3 → ℕ) ⟨1, by omega⟩ else 0) = 2 := by
  vec_simp!

-- Combined: multiple vectors with dite
example (a b c : ℕ) :
    (if _ : (0 : ℕ) < 1 then (![a, b, c] : Fin 3 → ℕ) ⟨0, by omega⟩ else 0) = a := by
  vec_simp!

-- Combined: nested dite with vector access
example :
    (if _ : (1 : ℕ) ≤ 2 then
      if _ : (2 : ℕ) ≤ 2 then (![10, 20, 30] : Fin 3 → ℕ) ⟨2, by omega⟩
      else 0
    else 0) = 30 := by
  vec_simp!

end VecSimpBang.Test

/-! ## Tests for vec_simp! with matrices -/

namespace MatrixSimp.Test

open Matrix in
def testMatrix : Fin 3 → Fin 3 → ℝ :=
  ![![1, 2, 3], ![4, 5, 6], ![7, 8, 9]]

-- vec_simp! handles matrix + norm_num in one call
example : ∀ i j : Fin 3, testMatrix i j ≤ 9 := by
  intro i j
  fin_cases i <;> fin_cases j
  all_goals vec_simp! [testMatrix]

-- vec_simp! with absolute values
example : ∀ i j : Fin 3, |testMatrix i j| ≤ 9 := by
  intro i j
  fin_cases i <;> fin_cases j
  all_goals vec_simp! [testMatrix]

-- Larger matrix (5x5)
open Matrix in
def bigMatrix : Fin 5 → Fin 5 → ℝ :=
  ![![1, 2, 3, 4, 5],
    ![6, 7, 8, 9, 10],
    ![11, 12, 13, 14, 15],
    ![16, 17, 18, 19, 20],
    ![21, 22, 23, 24, 25]]

example : ∀ i j : Fin 5, bigMatrix i j ≤ 25 := by
  intro i j
  fin_cases i <;> fin_cases j
  all_goals vec_simp! [bigMatrix]

-- Non-square matrix (3x4)
open Matrix in
def rectMatrix : Fin 3 → Fin 4 → ℝ :=
  ![![1, 2, 3, 4],
    ![5, 6, 7, 8],
    ![9, 10, 11, 12]]

example : ∀ i : Fin 3, ∀ j : Fin 4, rectMatrix i j ≤ 12 := by
  intro i j
  fin_cases i <;> fin_cases j
  all_goals vec_simp! [rectMatrix]

end MatrixSimp.Test

/-! ## Tests for Matrix.of notation -/

namespace MatrixOfTest

-- Matrix.of wraps a function as a matrix; Matrix.of_apply reduces (Matrix.of f) i j to f i j
open Matrix in
def matrixViaOf : Matrix (Fin 2) (Fin 2) ℝ := Matrix.of fun i j => (i.val + j.val : ℝ)

-- vec_simp! handles Matrix.of_apply
example : matrixViaOf 0 0 = 0 := by vec_simp! [matrixViaOf]
example : matrixViaOf 0 1 = 1 := by vec_simp! [matrixViaOf]
example : matrixViaOf 1 0 = 1 := by vec_simp! [matrixViaOf]
example : matrixViaOf 1 1 = 2 := by vec_simp! [matrixViaOf]

-- With fin_cases
example : ∀ i j : Fin 2, matrixViaOf i j ≤ 2 := by
  intro i j
  fin_cases i <;> fin_cases j
  all_goals vec_simp! [matrixViaOf]

end MatrixOfTest

/-! ## Tests for vec_simp! with higher-dimensional tensors -/

namespace TensorSimp.Test

-- 3D tensor as array of 2D matrices
open Matrix in
def M0 : Fin 2 → Fin 2 → ℝ := ![![1, 2], ![3, 4]]
open Matrix in
def M1 : Fin 2 → Fin 2 → ℝ := ![![5, 6], ![7, 8]]

open Matrix in
def T3 : Fin 2 → Fin 2 → Fin 2 → ℝ := ![M0, M1]

-- Need to unfold both T3 and the appropriate slice
example : T3 0 0 0 = 1 := by vec_simp! [T3, M0]
example : T3 0 1 1 = 4 := by vec_simp! [T3, M0]
example : T3 1 0 0 = 5 := by vec_simp! [T3, M1]
example : T3 1 1 1 = 8 := by vec_simp! [T3, M1]

-- With Fin.mk indices
example : T3 ⟨0, by omega⟩ ⟨1, by omega⟩ ⟨0, by omega⟩ = 3 := by vec_simp! [T3, M0]
example : T3 ⟨1, by omega⟩ ⟨0, by omega⟩ ⟨1, by omega⟩ = 6 := by vec_simp! [T3, M1]

-- With fin_cases (need all slice definitions)
example : ∀ i j k : Fin 2, T3 i j k ≤ 8 := by
  intro i j k
  fin_cases i <;> fin_cases j <;> fin_cases k
  all_goals vec_simp! [T3, M0, M1]

end TensorSimp.Test
