/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Ring.Parity
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Data.Finset.Powerset

/-!
# Finite q-product integrals

This module contains the exact finite algebra behind product-integral invariants

`F_S = ∫ u in 0..1, ∏ n ∈ S, (1 - u^n)`.

The computable side is rational: finite products are expanded over the powerset,
then monomials are integrated exactly.
-/

namespace LeanCert.QProduct

open scoped BigOperators

/-- Finite q-product profile associated to an exponent set. -/
noncomputable def qProd (S : Finset Nat) (u : ℝ) : ℝ :=
  ∏ n ∈ S, (1 - u ^ n)

/-- The real product-integral invariant. -/
noncomputable def F (S : Finset Nat) : ℝ :=
  ∫ u in (0 : ℝ)..1, qProd S u

/-- The signed powerset coefficient attached to a subset. -/
def subsetSign (A : Finset Nat) : ℚ :=
  if Even A.card then 1 else -1

/-- Sum of exponents in a finite subset. -/
def subsetWeight (A : Finset Nat) : Nat :=
  ∑ n ∈ A, n

/-- Exact rational value of the finite product integral. -/
def finiteIntegralRat (S : Finset Nat) : ℚ :=
  ∑ A ∈ S.powerset, subsetSign A / ((subsetWeight A + 1 : Nat) : ℚ)

/-- Exact rational value of the `k`th monomial moment of the finite product profile. -/
def momentRat (S : Finset Nat) (k : Nat) : ℚ :=
  ∑ A ∈ S.powerset, subsetSign A / ((subsetWeight A + k + 1 : Nat) : ℚ)

/-- The real `k`th monomial moment of the finite product profile. -/
noncomputable def moment (S : Finset Nat) (k : Nat) : ℝ :=
  ∫ u in (0 : ℝ)..1, qProd S u * u ^ k

@[simp] theorem subsetWeight_empty : subsetWeight ∅ = 0 := by
  simp [subsetWeight]

@[simp] theorem subsetSign_empty : subsetSign ∅ = 1 := by
  simp [subsetSign]

@[simp] theorem qProd_empty (u : ℝ) : qProd ∅ u = 1 := by
  simp [qProd]

@[simp] theorem F_empty : F ∅ = 1 := by
  simp [F, qProd]

/-- `subsetSign` as a real coefficient is `(-1)^card`. -/
theorem subsetSign_cast_eq (A : Finset Nat) :
    (subsetSign A : ℝ) = (-1 : ℝ) ^ A.card := by
  unfold subsetSign
  by_cases h : Even A.card
  · simp [h]
  · have hodd : Odd A.card := Nat.not_even_iff_odd.mp h
    simp [h, hodd.neg_one_pow]

/-- Product expansion over the powerset. -/
theorem qProd_powerset_expand (S : Finset Nat) (u : ℝ) :
    qProd S u =
      ∑ A ∈ S.powerset, (subsetSign A : ℝ) * u ^ subsetWeight A := by
  classical
  unfold qProd subsetWeight
  rw [Finset.prod_sub]
  apply Finset.sum_congr rfl
  intro A hA
  rw [subsetSign_cast_eq]
  have hprod_one : (∏ x ∈ S \ A, (1 : ℝ)) = 1 := by simp
  simp [hprod_one]
  exact Finset.prod_pow_eq_pow_sum A id u

private theorem integral_pow_zero_one (n : Nat) :
    ∫ u in (0 : ℝ)..1, u ^ n = (1 : ℝ) / (n + 1) := by
  simp [integral_pow (a := (0 : ℝ)) (b := 1) (n := n)]

/-- Semantic correctness of the exact rational finite product integral. -/
theorem finiteIntegralRat_correct (S : Finset Nat) :
    (finiteIntegralRat S : ℝ) = F S := by
  classical
  unfold finiteIntegralRat F
  simp_rw [qProd_powerset_expand]
  rw [intervalIntegral.integral_finsetSum]
  · simp_rw [Rat.cast_sum]
    apply Finset.sum_congr rfl
    intro A hA
    rw [intervalIntegral.integral_const_mul]
    rw [integral_pow_zero_one]
    simp only [Rat.cast_div, Rat.cast_natCast]
    norm_num
    rw [div_eq_mul_inv]
  · intro A hA
    exact (continuous_const.mul (continuous_id.pow (subsetWeight A))).intervalIntegrable 0 1

/-- Semantic correctness of the exact rational moment formula. -/
theorem momentRat_correct (S : Finset Nat) (k : Nat) :
    (momentRat S k : ℝ) = moment S k := by
  classical
  unfold momentRat moment
  simp_rw [qProd_powerset_expand]
  simp_rw [Finset.sum_mul]
  rw [intervalIntegral.integral_finsetSum]
  · simp_rw [Rat.cast_sum]
    apply Finset.sum_congr rfl
    intro A hA
    have hintegrand :
        (fun u : ℝ => (subsetSign A : ℝ) * u ^ subsetWeight A * u ^ k) =
          fun u : ℝ => (subsetSign A : ℝ) * u ^ (subsetWeight A + k) := by
      funext u
      rw [mul_assoc, ← pow_add]
    rw [hintegrand]
    rw [intervalIntegral.integral_const_mul]
    rw [integral_pow_zero_one]
    simp only [Rat.cast_div, Rat.cast_natCast]
    norm_num
    rw [div_eq_mul_inv]
  · intro A hA
    have hc : Continuous fun u : ℝ => (subsetSign A : ℝ) * (u ^ subsetWeight A * u ^ k) :=
      (continuous_const : Continuous fun _ : ℝ => (subsetSign A : ℝ)).mul
      ((continuous_id.pow (subsetWeight A)).mul (continuous_id.pow k))
    simpa [mul_assoc] using hc.intervalIntegrable 0 1

end LeanCert.QProduct
