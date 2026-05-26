/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/

import LeanCert.QProduct.Finite
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.Finset.Image
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.Algebra.Monoid

/-!
# Stability lemmas for finite q-product integrals

This file proves the elementary order facts used by the directed-limit theory:
on `[0,1]`, every positive exponent factor `1 - u^n` lies in `[0,1]`, so finite
products are nonnegative, bounded by one, and antitone in the exponent set.
-/

namespace LeanCert.QProduct

open scoped BigOperators
open MeasureTheory

theorem pow_mem_unit_interval {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) 1) (n : Nat) :
    u ^ n ∈ Set.Icc (0 : ℝ) 1 := by
  exact ⟨pow_nonneg hu.1 n, pow_le_one₀ hu.1 hu.2⟩

/-- The finite product profile is nonnegative on `[0,1]`. -/
theorem qProd_nonneg (S : Finset Nat) {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ qProd S u := by
  classical
  unfold qProd
  apply Finset.prod_nonneg
  intro n hn
  exact sub_nonneg.mpr (pow_mem_unit_interval hu n).2

/-- The finite product profile is bounded by one on `[0,1]`. -/
theorem qProd_le_one (S : Finset Nat) {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    qProd S u ≤ 1 := by
  classical
  unfold qProd
  apply Finset.prod_le_one
  · intro n hn
    exact sub_nonneg.mpr (pow_mem_unit_interval hu n).2
  · intro n hn
    exact sub_le_self 1 (pow_nonneg hu.1 n)

/-- Adding positive exponents can only lower the profile on `[0,1]`. -/
theorem qProd_antitone_pointwise {S T : Finset Nat}
    (hST : S ⊆ T)
    {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    qProd T u ≤ qProd S u := by
  classical
  have hsplit :
      qProd T u = qProd S u * (∏ n ∈ T \ S, (1 - u ^ n)) := by
    unfold qProd
    rw [← Finset.prod_sdiff hST]
    ring
  rw [hsplit]
  have hS_nonneg : 0 ≤ qProd S u := qProd_nonneg S hu
  have htail_le : (∏ n ∈ T \ S, (1 - u ^ n)) ≤ 1 :=
    qProd_le_one (T \ S) hu
  have htail_nonneg : 0 ≤ (∏ n ∈ T \ S, (1 - u ^ n)) :=
    qProd_nonneg (T \ S) hu
  calc
    qProd S u * (∏ n ∈ T \ S, (1 - u ^ n))
        ≤ qProd S u * 1 := mul_le_mul_of_nonneg_left htail_le hS_nonneg
    _ = qProd S u := mul_one _

/-- Product-integral values are nonnegative. -/
theorem F_nonneg (S : Finset Nat) : 0 ≤ F S := by
  unfold F
  have hInt : IntervalIntegrable (fun u => qProd S u) volume (0 : ℝ) 1 := by
    classical
    unfold qProd
    apply Continuous.intervalIntegrable
    exact continuous_finset_prod S fun n hn =>
      continuous_const.sub (continuous_id.pow n)
  apply intervalIntegral.integral_nonneg (by norm_num : (0 : ℝ) ≤ 1)
  intro u hu
  exact qProd_nonneg S hu

/-- Product-integral values are at most one. -/
theorem F_le_one (S : Finset Nat) : F S ≤ 1 := by
  unfold F
  have hInt : IntervalIntegrable (fun u => qProd S u) volume (0 : ℝ) 1 := by
    classical
    unfold qProd
    apply Continuous.intervalIntegrable
    exact continuous_finset_prod S fun n hn =>
      continuous_const.sub (continuous_id.pow n)
  have hConst : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume (0 : ℝ) 1 := by
    exact continuous_const.intervalIntegrable 0 1
  have hle := intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1) hInt hConst
    (fun u hu => qProd_le_one S hu)
  simpa using hle

/-- The product-integral invariant is antitone under inclusion. -/
theorem F_antitone {S T : Finset Nat}
    (hST : S ⊆ T) :
    F T ≤ F S := by
  unfold F
  have hTInt : IntervalIntegrable (fun u => qProd T u) volume (0 : ℝ) 1 := by
    classical
    unfold qProd
    apply Continuous.intervalIntegrable
    exact continuous_finset_prod T fun n hn =>
      continuous_const.sub (continuous_id.pow n)
  have hSInt : IntervalIntegrable (fun u => qProd S u) volume (0 : ℝ) 1 := by
    classical
    unfold qProd
    apply Continuous.intervalIntegrable
    exact continuous_finset_prod S fun n hn =>
      continuous_const.sub (continuous_id.pow n)
  exact intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1) hTInt hSInt
    (fun u hu => qProd_antitone_pointwise hST hu)

/-- Finite Weierstrass product inequality on `[0,1]`:
`1 - ∏ (1 - x_i) ≤ ∑ x_i`. -/
theorem one_sub_prod_one_sub_le_sum {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    (h0 : ∀ i ∈ s, 0 ≤ x i) (h1 : ∀ i ∈ s, x i ≤ 1) :
    1 - (∏ i ∈ s, (1 - x i)) ≤ ∑ i ∈ s, x i := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | insert a s ha ih =>
      have h0s : ∀ i ∈ s, 0 ≤ x i := fun i hi => h0 i (Finset.mem_insert_of_mem hi)
      have h1s : ∀ i ∈ s, x i ≤ 1 := fun i hi => h1 i (Finset.mem_insert_of_mem hi)
      have hprod_nonneg : 0 ≤ ∏ i ∈ s, (1 - x i) := by
        apply Finset.prod_nonneg
        intro i hi
        exact sub_nonneg.mpr (h1s i hi)
      have hprod_le_one : (∏ i ∈ s, (1 - x i)) ≤ 1 := by
        apply Finset.prod_le_one
        · intro i hi
          exact sub_nonneg.mpr (h1s i hi)
        · intro i hi
          exact sub_le_self 1 (h0s i hi)
      have hxa_nonneg : 0 ≤ x a := h0 a (by simp)
      have hxa_le : x a ≤ 1 := h1 a (by simp)
      rw [Finset.prod_insert ha, Finset.sum_insert ha]
      calc
        1 - ((1 - x a) * ∏ i ∈ s, (1 - x i))
            = (1 - ∏ i ∈ s, (1 - x i)) +
              x a * ∏ i ∈ s, (1 - x i) := by ring
        _ ≤ (∑ i ∈ s, x i) + x a * ∏ i ∈ s, (1 - x i) :=
              by simpa [add_comm, add_left_comm, add_assoc] using
                add_le_add_right (ih h0s h1s) (x a * ∏ i ∈ s, (1 - x i))
        _ ≤ (∑ i ∈ s, x i) + x a := by
              simpa [add_comm, add_left_comm, add_assoc] using
                add_le_add_left (mul_le_of_le_one_right hxa_nonneg hprod_le_one)
                  (∑ i ∈ s, x i)
        _ = x a + ∑ i ∈ s, x i := by ring

/-- Pointwise common-prefix tail bound. -/
theorem qProd_sub_le_commonPrefix_sum {R S T : Finset Nat}
    (hRS : R ⊆ S) (hST : S ⊆ T)
    {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    qProd S u - qProd T u ≤ qProd R u * ∑ q ∈ T \ S, u ^ q := by
  classical
  have hsplitT : qProd T u = qProd S u * (∏ q ∈ T \ S, (1 - u ^ q)) := by
    unfold qProd
    rw [← Finset.prod_sdiff hST]
    ring
  have hPS_nonneg : 0 ≤ qProd S u := qProd_nonneg S hu
  have hPR_nonneg : 0 ≤ qProd R u := qProd_nonneg R hu
  have hPS_le_PR : qProd S u ≤ qProd R u := qProd_antitone_pointwise hRS hu
  have htail_le :
      1 - (∏ q ∈ T \ S, (1 - u ^ q)) ≤ ∑ q ∈ T \ S, u ^ q := by
    apply one_sub_prod_one_sub_le_sum
    · intro q hq
      exact (pow_mem_unit_interval hu q).1
    · intro q hq
      exact (pow_mem_unit_interval hu q).2
  have htail_nonneg :
      0 ≤ 1 - (∏ q ∈ T \ S, (1 - u ^ q)) := by
    exact sub_nonneg.mpr (qProd_le_one (T \ S) hu)
  rw [hsplitT]
  calc
    qProd S u - qProd S u * (∏ q ∈ T \ S, (1 - u ^ q))
        = qProd S u * (1 - ∏ q ∈ T \ S, (1 - u ^ q)) := by ring
    _ ≤ qProd R u * (1 - ∏ q ∈ T \ S, (1 - u ^ q)) :=
        mul_le_mul_of_nonneg_right hPS_le_PR htail_nonneg
    _ ≤ qProd R u * ∑ q ∈ T \ S, u ^ q :=
        mul_le_mul_of_nonneg_left htail_le hPR_nonneg

/-- Odd exponent tails beginning at `5` telescope against the factor `1 - u^2`. -/
theorem odd_tail_telescope_bound (M : Nat) {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    (1 - u ^ 2) * (∑ j ∈ Finset.range (M + 1), u ^ (5 + 2 * j)) ≤ u ^ 5 := by
  have hsum :
      (∑ j ∈ Finset.range (M + 1), u ^ (5 + 2 * j)) =
        u ^ 5 * ∑ j ∈ Finset.range (M + 1), (u ^ 2) ^ j := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [pow_add, pow_mul]
  rw [mul_comm]
  rw [hsum, mul_assoc, geom_sum_mul_neg]
  calc
    u ^ 5 * (1 - (u ^ 2) ^ (M + 1)) ≤ u ^ 5 * 1 := by
      apply mul_le_mul_of_nonneg_left
      · have hnonneg : 0 ≤ (u ^ 2) ^ (M + 1) := pow_nonneg (sq_nonneg u) _
        linarith
      · exact pow_nonneg hu.1 5
    _ = u ^ 5 := by ring

/-- Any finite set of odd exponents at least `5` and bounded by `M` is dominated
by the full odd geometric tail beginning at `5`. -/
theorem odd_tail_sum_le_geom (A : Finset Nat) (M : Nat)
    {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) 1)
    (hodd : ∀ q ∈ A, Odd q) (h5 : ∀ q ∈ A, 5 ≤ q) (hM : ∀ q ∈ A, q < M + 1) :
    ∑ q ∈ A, u ^ q ≤ ∑ j ∈ Finset.range (M + 1), u ^ (5 + 2 * j) := by
  classical
  let G : Finset Nat := (Finset.range (M + 1)).image (fun j => 5 + 2 * j)
  have hsub : A ⊆ G := by
    intro q hq
    rcases hodd q hq with ⟨k, hk⟩
    have hq5 := h5 q hq
    have hqM := hM q hq
    subst q
    refine Finset.mem_image.mpr ?_
    refine ⟨k - 2, ?_, ?_⟩
    · simp only [Finset.mem_range]
      omega
    · omega
  have hsum_subset : ∑ q ∈ A, u ^ q ≤ ∑ q ∈ G, u ^ q := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hsub
    intro q hqG hqA
    exact pow_nonneg hu.1 q
  have hG :
      (∑ q ∈ G, u ^ q) = ∑ j ∈ Finset.range (M + 1), u ^ (5 + 2 * j) := by
    unfold G
    rw [Finset.sum_image]
    intro a ha b hb h
    simp only at h
    omega
  exact hsum_subset.trans_eq hG

end LeanCert.QProduct
