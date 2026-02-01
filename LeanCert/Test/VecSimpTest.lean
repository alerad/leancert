/-
Copyright (c) 2024 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Tactic.VecSimp
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

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
