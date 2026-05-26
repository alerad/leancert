/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/

import LeanCert.QProduct

/-!
# Basic q-product examples
-/

open LeanCert.QProduct

example : finiteIntegralRat (∅ : Finset Nat) = 1 := by
  native_decide

example : finiteIntegralRat ({2} : Finset Nat) = 2 / 3 := by
  native_decide

example : finiteIntegralRat ({2, 3} : Finset Nat) = 7 / 12 := by
  native_decide

example : F ({2, 3} : Finset Nat) = (7 : ℝ) / 12 := by
  have h : finiteIntegralRat ({2, 3} : Finset Nat) = 7 / 12 := by
    native_decide
  rw [← finiteIntegralRat_correct]
  rw [h]
  norm_num

example :
    ((7 / 12 : ℚ) : ℝ) ≤ F ({2, 3} : Finset Nat) ∧
    F ({2, 3} : Finset Nat) ≤ ((7 / 12 : ℚ) : ℝ) :=
  verify_finiteIntegral_interval ({2, 3} : Finset Nat) (7 / 12) (7 / 12) (by native_decide)

example :
    F ({2, 3, 5} : Finset Nat) ≤ F ({2, 3} : Finset Nat) := by
  apply F_antitone
  intro n hn
  simp at hn ⊢
  rcases hn with rfl | rfl <;> simp
