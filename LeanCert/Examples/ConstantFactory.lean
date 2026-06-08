/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/

import LeanCert.ConstantFactory.IntervalBank

/-!
# ConstantFactory examples
-/

open LeanCert.ConstantFactory
open LeanCert.QProduct

example :
    observerIntegralRat ({2} : Finset Nat) ({3} : Finset Nat) = 7 / 12 := by
  native_decide

example :
    F ({2, 3} : Finset Nat) = ((7 / 12 : ℚ) : ℝ) := by
  have h :
      (observerIntegralRat ({2} : Finset Nat) ({3} : Finset Nat) : ℝ) =
        F (({2} : Finset Nat) ∪ ({3} : Finset Nat)) := by
    exact observerIntegralRat_eq_F_union ({2} : Finset Nat) ({3} : Finset Nat)
      (by simp)
  have hrat : observerIntegralRat ({2} : Finset Nat) ({3} : Finset Nat) = 7 / 12 := by
    native_decide
  have hset : (({2} : Finset Nat) ∪ ({3} : Finset Nat)) = ({2, 3} : Finset Nat) := by
    ext n
    simp
  rw [← hset, ← h, hrat]

example :
    ((7 / 12 : ℚ) : ℝ) ≤ F (({2} : Finset Nat) ∪ ({3} : Finset Nat)) ∧
      F (({2} : Finset Nat) ∪ ({3} : Finset Nat)) ≤ ((7 / 12 : ℚ) : ℝ) :=
  verify_constantFactory_interval ({2} : Finset Nat) ({3} : Finset Nat)
    (7 / 12) (7 / 12) (by native_decide)

example :
    F (({2} : Finset Nat) ∪ ({3} : Finset Nat)) ∈
      observerInterval ({3} : Finset Nat)
        (exactKernelIntervalBank ({2} : Finset Nat)) := by
  exact F_union_mem_observerInterval (by simp)
    (exactKernelIntervalBank ({2} : Finset Nat))
