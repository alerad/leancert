/-
Copyright (c) 2024 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Tactic.VecSimp
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

/-!
# Tests for vec_simp tactic

Verifies that `vec_simp` reduces `![a, b, c] ⟨i, proof⟩` to the i-th element.
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
