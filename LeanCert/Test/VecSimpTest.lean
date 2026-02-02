/-
Copyright (c) 2024 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Tactic.VecSimp
import LeanCert.Tactic.FinSumExpand
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Tests for vec_simp and vec_simp! tactics

* `vec_simp` - Reduces vector indexing (Fin.mk and numeric literal indices)
* `vec_simp!` - + dite conditions, abs, norm_num
-/

namespace VecSimp.Test

/-! ### Basic indexing -/

example : (![1, 2, 3] : Fin 3 → ℕ) ⟨2, by omega⟩ = 3 := by vec_simp       -- Fin.mk
example (a b c : ℝ) : (![a, b, c] : Fin 3 → ℝ) 1 = b := by vec_simp       -- numeric literal
example : |(![0, 1/2, -3/4] : Fin 3 → ℚ) 2| = 3/4 := by vec_simp!         -- with abs (ℚ)

/-! ### Longer vectors -/

example : (![1, 2, 3, 4, 5] : Fin 5 → ℕ) 4 = 5 := by vec_simp

/-! ### Combination with ring -/

variable (a₀ a₁ a₂ : ℝ)

example : (![a₀, a₁, a₂] : Fin 3 → ℝ) ⟨0, by omega⟩ * (![a₀, a₁, a₂] : Fin 3 → ℝ) ⟨1, by omega⟩ +
          (![a₀, a₁, a₂] : Fin 3 → ℝ) ⟨1, by omega⟩ * (![a₀, a₁, a₂] : Fin 3 → ℝ) ⟨0, by omega⟩ = 2 * a₀ * a₁ := by
  vec_simp; ring

end VecSimp.Test

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

/-! ## Bug fix tests: |vecCons ... idx| inside matrix column norms

These tests target a specific bug where `|vecCons h (fun i => ...) idx|` wasn't being
reduced. The issue was that abs lemmas need to be in the SAME simp call as vecConsFinMk
so simp can descend into the `|...|` and reduce the inner vecCons.

Key patterns that triggered the bug:
1. Lambda tail: `fun i => vecCons ...` (from matrix column extraction)
2. Last index: accessing the deepest element (most recursion through tail)
3. Inside abs: `|vecCons ...|` where abs "hides" the vecCons from simp
4. Real numbers: `ℝ` where `decide` can't prove positivity (need norm_num)

See design-notes.txt for full explanation.
-/

namespace AbsVecConsBugFix.Test

/-! ### Lambda tail pattern (from matrix column extraction)

When extracting a matrix column, the tail becomes a lambda:
`![a, b, c] i` unfolds to `vecCons a (fun i => vecCons b (fun _ => c) i) i`
-/

-- Basic lambda tail with abs (ℚ - works with decide)
example : |(Matrix.vecCons (1 : ℚ)
    (fun i => Matrix.vecCons (-2) (fun _ => (-3)) i) : Fin 3 → ℚ) 2| = 3 := by
  vec_simp!

-- Lambda tail with abs (ℝ - needs norm_num for positivity)
example : |(Matrix.vecCons (1/2 : ℝ)
    (fun i => Matrix.vecCons (-1/4) (fun _ => (3/8)) i) : Fin 3 → ℝ) 2| = 3/8 := by
  vec_simp!

-- Test each index to ensure all positions work
example : |(Matrix.vecCons (1/2 : ℝ)
    (fun i => Matrix.vecCons (-1/4) (fun _ => (3/8)) i) : Fin 3 → ℝ) 0| = 1/2 := by vec_simp!
example : |(Matrix.vecCons (1/2 : ℝ)
    (fun i => Matrix.vecCons (-1/4) (fun _ => (3/8)) i) : Fin 3 → ℝ) 1| = 1/4 := by vec_simp!
example : |(Matrix.vecCons (1/2 : ℝ)
    (fun i => Matrix.vecCons (-1/4) (fun _ => (3/8)) i) : Fin 3 → ℝ) 2| = 3/8 := by vec_simp!

/-! ### finsum_expand! integration

After finsum_expand! expands a Fin sum, we often have |vecCons ...| expressions.
finsum_expand! now uses vec_index_simp_with_dite internally to handle these.
-/

-- finsum_expand! alone should fully reduce
example : |(Matrix.vecCons (1/2 : ℝ)
    (fun i => Matrix.vecCons (-1/4) (fun _ => (3/8)) i) : Fin 3 → ℝ) 2| = 3/8 := by
  finsum_expand!

-- finsum_expand! alone is sufficient (vec_simp! would be redundant)
example : |(Matrix.vecCons (1/2 : ℝ)
    (fun i => Matrix.vecCons (-1/4) (fun _ => (3/8)) i) : Fin 3 → ℝ) 2| = 3/8 := by
  finsum_expand!

/-! ### Inequality context (like matrix norm bounds)

The original bug appeared when proving `∑ i, |A i j| * ν^i ≤ bound`.
After sum expansion, expressions like `|vecCons ...| * ν^2` need reduction.
-/

-- In an inequality with multiplication (like colNorm_le)
example : 1/2 + (1/4 * (1/4) +
    |(Matrix.vecCons (1/2 : ℝ)
        (fun i => Matrix.vecCons (-1/4) (fun _ => (3/8)) i) : Fin 3 → ℝ) 2| * (1/16)) ≤ 1 := by
  finsum_expand!  -- fully reduces vecCons and abs

/-! ### Matrix definition pattern

Replicate the structure from Example_7_7: a 3x3 lower triangular matrix with
entries defined via separate defs, then accessed column-wise.
-/

open Matrix in
-- Lower triangular matrix (simplified from Example_7_7)
noncomputable def L_diag : ℝ := 1/2
noncomputable def L_sub1 : ℝ := -1/4
noncomputable def L_sub2 : ℝ := 3/8

open Matrix in
noncomputable def L_mat : Matrix (Fin 3) (Fin 3) ℝ :=
  of ![![L_diag, 0, 0],
       ![L_sub1, L_diag, 0],
       ![L_sub2, L_sub1, L_diag]]

-- Column 0 access: this is the pattern that was failing
example : ∀ i : Fin 3, |L_mat i 0| ≤ 1 := by
  intro i
  unfold L_mat L_diag L_sub1 L_sub2
  fin_cases i <;> vec_simp!

-- With finsum_expand! alone (like colNorm_le proof) - now sufficient
example : ∀ i : Fin 3, |L_mat i 0| ≤ 1 := by
  intro i
  unfold L_mat L_diag L_sub1 L_sub2
  fin_cases i <;> finsum_expand!

end AbsVecConsBugFix.Test

/-! ## Tests for dite + abs combined -/

namespace DiteAbsCombined.Test

open Matrix in
def signedM : Fin 2 → Fin 2 → ℚ := ![![-1, 2], ![-3, 4]]

example : (if _ : (1 : ℕ) ≤ 2 then |signedM 0 0| else 0) = 1 := by vec_simp! [signedM]

end DiteAbsCombined.Test
