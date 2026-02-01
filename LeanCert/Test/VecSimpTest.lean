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

* `vec_simp` - Reduces vector indexing (Fin.mk and numeric literal indices)
* `vec_simp!` - + dite conditions, abs, norm_num
* `dite_simp` - Simplifies `dite` with decidable literal conditions
-/

namespace VecSimp.Test

/-! ### Basic indexing -/

example : (![1, 2, 3] : Fin 3 → ℕ) ⟨2, by omega⟩ = 3 := by vec_simp       -- Fin.mk
example (a b c : ℝ) : (![a, b, c] : Fin 3 → ℝ) 1 = b := by vec_simp       -- numeric literal, symbolic
example : |(![0, 1/2, -3/4] : Fin 3 → ℚ) 2| = 3/4 := by vec_simp!         -- with abs

/-! ### Raw Matrix.vecCons with nested structure -/

example : |Matrix.vecCons (0 : ℚ) (Matrix.vecCons (1/2) ![(-3/4)]) 2| = 3/4 := by vec_simp!

/-! ### Lambda tail pattern (from matrix column extraction) -/

example : |(Matrix.vecCons (1 : ℚ)
    (fun i => Matrix.vecCons (-2 : ℚ) (fun _ => (-3 : ℚ)) i) : Fin 3 → ℚ) 2| = 3 := by
  vec_simp!

/-! ### Nested vecCons after lambda reduction (inferred dimension) -/

example : (Matrix.vecCons (10 : ℚ)
    (fun i => Matrix.vecCons (20 : ℚ) (fun j => Matrix.vecCons (30 : ℚ) (fun _ => 40) j) i) : Fin 4 → ℚ) 3 = 40 := by
  vec_simp!

/-! ### Longer vectors -/

example : (![1, 2, 3, 4, 5] : Fin 5 → ℕ) 4 = 5 := by vec_simp

/-! ### Combination with ring -/

variable (a₀ a₁ a₂ : ℝ)

example : (![a₀, a₁, a₂] : Fin 3 → ℝ) ⟨0, by omega⟩ * (![a₀, a₁, a₂] : Fin 3 → ℝ) ⟨1, by omega⟩ +
          (![a₀, a₁, a₂] : Fin 3 → ℝ) ⟨1, by omega⟩ * (![a₀, a₁, a₂] : Fin 3 → ℝ) ⟨0, by omega⟩ = 2 * a₀ * a₁ := by
  vec_simp; ring

end VecSimp.Test

/-! ## Tests for dite_simp -/

namespace DiteSimp.Test

example (f : (1 : ℕ) ≤ 2 → ℕ) (g : ¬(1 : ℕ) ≤ 2 → ℕ) :
    (if h : (1 : ℕ) ≤ 2 then f h else g h) = f (by omega) := by dite_simp  -- true case

example (f : (3 : ℕ) ≤ 2 → ℕ) (g : ¬(3 : ℕ) ≤ 2 → ℕ) :
    (if h : (3 : ℕ) ≤ 2 then f h else g h) = g (by omega) := by dite_simp  -- false case

example (f : (1 : ℕ) ≤ 2 → (2 : ℕ) ≤ 2 → ℕ) :
    (if h₁ : (1 : ℕ) ≤ 2 then if h₂ : (2 : ℕ) ≤ 2 then f h₁ h₂ else 0 else 0) =
    f (by omega) (by omega) := by dite_simp  -- nested

end DiteSimp.Test

/-! ## Tests for vec_simp! (dite + vector combined) -/

namespace VecSimpBang.Test

example : (if _ : (1 : ℕ) ≤ 2 then
      if _ : (2 : ℕ) ≤ 2 then (![10, 20, 30] : Fin 3 → ℕ) ⟨2, by omega⟩ else 0
    else 0) = 30 := by vec_simp!  -- nested dite with vector

end VecSimpBang.Test

/-! ## Tests for vec_simp! with named matrices -/

namespace MatrixSimp.Test

open Matrix in
def colTestMatrix : Fin 3 → Fin 3 → ℚ := ![![1, 2, 3], ![-4, 5, 6], ![7, -8, 9]]

example : |colTestMatrix 1 0| = 4 := by vec_simp! [colTestMatrix]  -- with abs

example : ∀ i : Fin 3, |colTestMatrix i 0| ≤ 7 := by
  intro i; fin_cases i; all_goals vec_simp! [colTestMatrix]

end MatrixSimp.Test

/-! ## Tests for Matrix.of notation and fixed-point iteration -/

namespace MatrixOfTest

open Matrix in
def matrixViaOf : Matrix (Fin 2) (Fin 2) ℝ := Matrix.of fun i j => (i.val + j.val : ℝ)

example : matrixViaOf 1 1 = 2 := by vec_simp! [matrixViaOf]

/-! ### Fixed-point iteration: Matrix.of_apply after vecConsFinMk

When Matrix.of wraps a matrix literal, we need multiple rounds of simplification.
The fail_if_no_progress pattern achieves this fixed-point iteration. -/

open Matrix in
def wrappedOf (M : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of fun i j => M i j + 1

-- Single wrapping: Matrix.of_apply once, then vecConsFinMk
example : wrappedOf ![![1, 2], ![3, 4]] 1 1 = 5 := by vec_simp! [wrappedOf]

-- Double wrapping: needs two rounds of Matrix.of_apply
open Matrix in
def doubleWrappedOf (M : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of fun i j => (Matrix.of fun i' j' => M i' j' + 1) i j + 1

example : doubleWrappedOf ![![1, 2], ![3, 4]] 0 0 = 3 := by vec_simp! [doubleWrappedOf]

end MatrixOfTest

/-! ## Tests for 3D tensors -/

namespace TensorSimp.Test

open Matrix in
def M0 : Fin 2 → Fin 2 → ℝ := ![![1, 2], ![3, 4]]
open Matrix in
def M1 : Fin 2 → Fin 2 → ℝ := ![![5, 6], ![7, 8]]
open Matrix in
def T3 : Fin 2 → Fin 2 → Fin 2 → ℝ := ![M0, M1]

example : T3 ⟨1, by omega⟩ ⟨0, by omega⟩ ⟨1, by omega⟩ = 6 := by vec_simp! [T3, M1]  -- Fin.mk

example : ∀ i j k : Fin 2, T3 i j k ≤ 8 := by
  intro i j k; fin_cases i <;> fin_cases j <;> fin_cases k; all_goals vec_simp! [T3, M0, M1]

end TensorSimp.Test

/-! ## Tests for dite + abs combined -/

namespace DiteAbsCombined.Test

open Matrix in
def signedM : Fin 2 → Fin 2 → ℚ := ![![-1, 2], ![-3, 4]]

example : (if _ : (1 : ℕ) ≤ 2 then |signedM 0 0| else 0) = 1 := by vec_simp! [signedM]

end DiteAbsCombined.Test
