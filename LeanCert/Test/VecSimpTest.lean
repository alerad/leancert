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

* `vec_simp` - Reduces vector indexing including:
  - `![a, b, c] ⟨i, proof⟩` (Fin.mk indices)
  - `![a, b, c] 2` (numeric literal indices)
  - Lambda tails from matrix column extraction
* `vec_simp!` - Aggressive variant that also simplifies `dite` conditions and abs
* `dite_simp` - Standalone tactic for simplifying `dite` with decidable literal conditions
-/

namespace VecSimp.Test

/-! #### Indexing with Fin.mk -/

example : (![1, 2, 3] : Fin 3 → ℕ) ⟨0, by omega⟩ = 1 := by vec_simp
example : (![1, 2, 3] : Fin 3 → ℕ) ⟨1, by omega⟩ = 2 := by vec_simp
example : (![1, 2, 3] : Fin 3 → ℕ) ⟨2, by omega⟩ = 3 := by vec_simp

-- Symbolic elements
example (a b c : ℝ) : (![a, b, c] : Fin 3 → ℝ) ⟨0, by omega⟩ = a := by vec_simp
example (a b c : ℝ) : (![a, b, c] : Fin 3 → ℝ) ⟨1, by omega⟩ = b := by vec_simp

/-! #### Indexing with numeric literals -/

-- vec_simp now handles numeric literal indices like `2` (not just Fin.mk)
example : (![1, 2, 3] : Fin 3 → ℕ) 0 = 1 := by vec_simp
example : (![1, 2, 3] : Fin 3 → ℕ) 1 = 2 := by vec_simp
example : (![1, 2, 3] : Fin 3 → ℕ) 2 = 3 := by vec_simp

-- Symbolic elements with numeric indices
example (a b c : ℝ) : (![a, b, c] : Fin 3 → ℝ) 0 = a := by vec_simp
example (a b c : ℝ) : (![a, b, c] : Fin 3 → ℝ) 1 = b := by vec_simp
example (a b c : ℝ) : (![a, b, c] : Fin 3 → ℝ) 2 = c := by vec_simp

-- Vectors with rational elements
example : (![0, 1/2, -3/4] : Fin 3 → ℚ) 2 = -3/4 := by vec_simp
example : |(![0, 1/2, -3/4] : Fin 3 → ℚ) 2| = 3/4 := by vec_simp!

/-! #### Raw Matrix.vecCons expressions (not using ![...] notation) -/

-- Direct Matrix.vecCons indexing with explicit tail
example : (Matrix.vecCons (1 : ℕ) ![2, 3]) 0 = 1 := by vec_simp
example : (Matrix.vecCons (1 : ℕ) ![2, 3]) 1 = 2 := by vec_simp
example : (Matrix.vecCons (1 : ℕ) ![2, 3]) 2 = 3 := by vec_simp

-- Nested Matrix.vecCons (explicitly typed)
example : (Matrix.vecCons (0 : ℚ) (Matrix.vecCons (1/2) ![(-3/4)])) 0 = 0 := by vec_simp
example : (Matrix.vecCons (0 : ℚ) (Matrix.vecCons (1/2) ![(-3/4)])) 1 = 1/2 := by vec_simp
example : (Matrix.vecCons (0 : ℚ) (Matrix.vecCons (1/2) ![(-3/4)])) 2 = -3/4 := by vec_simp

-- With absolute value
example : |Matrix.vecCons (0 : ℚ) (Matrix.vecCons (1/2) ![(-3/4)]) 2| = 3/4 := by vec_simp!

/-! #### Lambda tail pattern (from matrix column extraction) -/

-- This pattern arises when 2D matrix indexing creates column vectors with lambda tails
-- e.g., M i 0 across different rows creates: vecCons (M 0 0) (fun i => vecCons (M 1 0) ...)
-- The lambda tail needs special handling in getVecElem

example : (Matrix.vecCons (1 : ℚ)
    (fun (i : Fin 2) => Matrix.vecCons (2 : ℚ) (fun (_ : Fin 1) => (3 : ℚ)) i) : Fin 3 → ℚ) 0 = 1 := by
  vec_simp
example : (Matrix.vecCons (1 : ℚ)
    (fun (i : Fin 2) => Matrix.vecCons (2 : ℚ) (fun (_ : Fin 1) => (3 : ℚ)) i) : Fin 3 → ℚ) 1 = 2 := by
  vec_simp
example : (Matrix.vecCons (1 : ℚ)
    (fun (i : Fin 2) => Matrix.vecCons (2 : ℚ) (fun (_ : Fin 1) => (3 : ℚ)) i) : Fin 3 → ℚ) 2 = 3 := by
  vec_simp

-- With absolute value on lambda tail pattern
example : |(Matrix.vecCons (1 : ℚ)
    (fun (i : Fin 2) => Matrix.vecCons (-2 : ℚ) (fun (_ : Fin 1) => (3 : ℚ)) i) : Fin 3 → ℚ) 1| = 2 := by
  vec_simp!
example : |(Matrix.vecCons (1 : ℚ)
    (fun (i : Fin 2) => Matrix.vecCons (-2 : ℚ) (fun (_ : Fin 1) => (-3 : ℚ)) i) : Fin 3 → ℚ) 2| = 3 := by
  vec_simp!

-- Lambda tail without explicit binder types (inferred from context)
example : |(Matrix.vecCons (1 : ℚ)
    (fun i => Matrix.vecCons (-2 : ℚ) (fun _ => (-3 : ℚ)) i) : Fin 3 → ℚ) 2| = 3 := by
  vec_simp!

-- Nested vecCons after lambda reduction: when looking up index 3 in vecCons head (fun i => vecCons ...),
-- we apply the lambda to Fin.mk 2, reduce, and get vecCons _ _ (Fin.mk 1 _) which needs further extraction
example : (Matrix.vecCons (10 : ℚ)
    (fun i => Matrix.vecCons (20 : ℚ) (fun j => Matrix.vecCons (30 : ℚ) (fun _ => 40) j) i) : Fin 4 → ℚ) 3 = 40 := by
  vec_simp!

/-! ### Inferred dimension (metavariable reduction)

When the outer expression has a type annotation but inner lambdas don't have explicit
binder types, `nExpr` (the dimension in `Fin n`) may be `Nat.succ ?m` rather than a
raw literal. We must `reduce nExpr` before calling `nat?` to convert it to a concrete
literal like `2`.

The tests in "Lambda tail without explicit binder types" above exercise this path.
The key insight: `fun i => ...` without explicit `(i : Fin 2)` causes `inferType` to
return a type with `Fin (Nat.succ ?m)` where the metavariable gets unified later.
-/

-- Type annotation on outer expression, but lambda binders are implicit
-- This exercises the reduce-before-nat? fix
example : (Matrix.vecCons (1 : ℚ)
    (fun i => Matrix.vecCons (2 : ℚ) (fun _ => 3) i) : Fin 3 → ℚ) 1 = 2 := by
  vec_simp!

example : (Matrix.vecCons (1 : ℚ)
    (fun i => Matrix.vecCons (2 : ℚ) (fun _ => 3) i) : Fin 3 → ℚ) 2 = 3 := by
  vec_simp!

-- Deeper nesting with implicit binders
example : (Matrix.vecCons (100 : ℚ)
    (fun i => Matrix.vecCons (200 : ℚ) (fun j => Matrix.vecCons (300 : ℚ) (fun _ => 400) j) i) : Fin 4 → ℚ) 2 = 300 := by
  vec_simp!

-- Longer vectors with Fin.mk
example : (![1, 2, 3, 4, 5] : Fin 5 → ℕ) ⟨3, by omega⟩ = 4 := by vec_simp

-- Longer vectors with numeric indices
example : (![1, 2, 3, 4, 5] : Fin 5 → ℕ) 3 = 4 := by vec_simp
example : (![1, 2, 3, 4, 5] : Fin 5 → ℕ) 4 = 5 := by vec_simp

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

-- Column extraction test: accessing column 0 across all rows
-- This tests the lambda tail handling in getVecElem
open Matrix in
def colTestMatrix : Fin 3 → Fin 3 → ℚ :=
  ![![1, 2, 3], ![-4, 5, 6], ![7, -8, 9]]

-- Direct column 0 access at each row
example : colTestMatrix 0 0 = 1 := by vec_simp! [colTestMatrix]
example : colTestMatrix 1 0 = -4 := by vec_simp! [colTestMatrix]
example : colTestMatrix 2 0 = 7 := by vec_simp! [colTestMatrix]

-- With absolute values on column 0
example : |colTestMatrix 1 0| = 4 := by vec_simp! [colTestMatrix]
example : |colTestMatrix 2 1| = 8 := by vec_simp! [colTestMatrix]

-- All column 0 elements via fin_cases
example : ∀ i : Fin 3, |colTestMatrix i 0| ≤ 7 := by
  intro i
  fin_cases i
  all_goals vec_simp! [colTestMatrix]

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

/-! ## Tests for vec_simp! [defs] consistency with vec_simp!

Both variants should have the same capabilities - the `[defs]` variant just also
unfolds the given definitions first. This tests that the Mathlib fallback lemmas
(cons_val_zero, cons_val_one, head_cons) work in both variants. -/

namespace VecSimpDefConsistency.Test

-- A simple defined matrix
open Matrix in
def simpleM : Fin 3 → Fin 3 → ℚ := ![![1, 2, 3], ![4, 5, 6], ![7, 8, 9]]

-- Tests that vec_simp! [defs] handles all index positions like vec_simp! does
-- These use the Mathlib fallback lemmas when needed
example : simpleM 0 0 = 1 := by vec_simp! [simpleM]
example : simpleM 0 1 = 2 := by vec_simp! [simpleM]
example : simpleM 0 2 = 3 := by vec_simp! [simpleM]
example : simpleM 1 0 = 4 := by vec_simp! [simpleM]
example : simpleM 1 1 = 5 := by vec_simp! [simpleM]
example : simpleM 1 2 = 6 := by vec_simp! [simpleM]
example : simpleM 2 0 = 7 := by vec_simp! [simpleM]
example : simpleM 2 1 = 8 := by vec_simp! [simpleM]
example : simpleM 2 2 = 9 := by vec_simp! [simpleM]

-- With Fin.mk indices (tests both dsimproc and fallback lemmas work)
example : simpleM ⟨0, by omega⟩ ⟨0, by omega⟩ = 1 := by vec_simp! [simpleM]
example : simpleM ⟨1, by omega⟩ ⟨1, by omega⟩ = 5 := by vec_simp! [simpleM]
example : simpleM ⟨2, by omega⟩ ⟨2, by omega⟩ = 9 := by vec_simp! [simpleM]

-- vec_simp! [defs] with dite conditions (tests decide config works)
example : (if _ : (1 : ℕ) ≤ 2 then simpleM 0 0 else 0) = 1 := by vec_simp! [simpleM]
example : (if _ : (1 : ℕ) ≤ 2 then simpleM 1 1 else 0) = 5 := by vec_simp! [simpleM]

-- vec_simp! [defs] with absolute values
open Matrix in
def signedM : Fin 2 → Fin 2 → ℚ := ![![-1, 2], ![-3, 4]]

example : |signedM 0 0| = 1 := by vec_simp! [signedM]
example : |signedM 1 0| = 3 := by vec_simp! [signedM]

-- Combined: dite + abs + matrix definition
example : (if _ : (1 : ℕ) ≤ 2 then |signedM 0 0| else 0) = 1 := by vec_simp! [signedM]

end VecSimpDefConsistency.Test
