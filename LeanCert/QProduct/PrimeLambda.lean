/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/

import LeanCert.QProduct.Stability
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.IntervalCases

/-!
# Prime-indexed q-product truncations

This file introduces the finite prime truncations and the directed prime limit as
an infimum over the truncation values.  The tail-sandwich certificates live on
top of these definitions.
-/

namespace LeanCert.QProduct

open scoped BigOperators

private theorem nat_prime_two : Nat.Prime 2 := by native_decide
private theorem nat_prime_three : Nat.Prime 3 := by native_decide
private theorem nat_not_prime_zero : ¬ Nat.Prime 0 := by native_decide
private theorem nat_not_prime_one : ¬ Nat.Prime 1 := by native_decide
private theorem nat_not_prime_four : ¬ Nat.Prime 4 := by native_decide

/-- Prime exponents up to `N`. -/
def primesLE (N : Nat) : Finset Nat :=
  (Finset.range (N + 1)).filter Nat.Prime

/-- Exact rational value of the prime truncation integral. -/
def primeFRat (N : Nat) : ℚ :=
  finiteIntegralRat (primesLE N)

/-- Prime q-product directed limit, represented as the infimum of truncations. -/
noncomputable def primeLambda : ℝ :=
  sInf (Set.range fun N : Nat => (primeFRat N : ℝ))

theorem primesLE_subset {N M : Nat} (hNM : N ≤ M) :
    primesLE N ⊆ primesLE M := by
  intro p hp
  simp only [primesLE, Finset.mem_filter, Finset.mem_range] at hp ⊢
  exact ⟨Nat.lt_succ_of_le (Nat.le_trans (Nat.lt_succ_iff.mp hp.1) hNM), hp.2⟩

/-- Prime truncation values are antitone in the cutoff. -/
theorem primeFRat_antitone {N M : Nat} (hNM : N ≤ M) :
    (primeFRat M : ℝ) ≤ (primeFRat N : ℝ) := by
  unfold primeFRat
  rw [finiteIntegralRat_correct, finiteIntegralRat_correct]
  exact F_antitone (primesLE_subset hNM)

/-- The limit is bounded above by every finite prime truncation. -/
theorem primeLambda_le_trunc (N : Nat) :
    primeLambda ≤ (primeFRat N : ℝ) := by
  unfold primeLambda
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro x ⟨M, rfl⟩
    change 0 ≤ (finiteIntegralRat (primesLE M) : ℝ)
    rw [finiteIntegralRat_correct]
    exact F_nonneg (primesLE M)
  · exact ⟨N, rfl⟩

/-- Any rational lower bound valid for every finite prime truncation is valid
for the directed prime limit. -/
theorem primeLambda_lower_of_forall (lo : ℚ)
    (hlo : ∀ N : Nat, (lo : ℝ) ≤ (primeFRat N : ℝ)) :
    (lo : ℝ) ≤ primeLambda := by
  unfold primeLambda
  apply le_csInf
  · exact Set.range_nonempty _
  · rintro x ⟨N, rfl⟩
    exact hlo N

/-- Boolean upper certificate for the prime limit using one truncation. -/
def checkPrimeLambdaUpper (N : Nat) (hi : ℚ) : Bool :=
  decide (primeFRat N ≤ hi)

/-- Golden theorem for prime-limit upper certificates. -/
theorem verify_primeLambda_upper (N : Nat) (hi : ℚ)
    (hcheck : checkPrimeLambdaUpper N hi = true) :
    primeLambda ≤ (hi : ℝ) := by
  simp only [checkPrimeLambdaUpper, decide_eq_true_eq] at hcheck
  exact le_trans (primeLambda_le_trunc N) (by exact_mod_cast hcheck)

/-- Combined prime-limit interval theorem. The lower side is supplied as a
mathematical tail proof; the upper side is checked exactly by computation. -/
theorem verify_primeLambda_interval_of_forall (N : Nat) (lo hi : ℚ)
    (hlo : ∀ M : Nat, (lo : ℝ) ≤ (primeFRat M : ℝ))
    (hcheck : checkPrimeLambdaUpper N hi = true) :
    (lo : ℝ) ≤ primeLambda ∧ primeLambda ≤ (hi : ℝ) :=
  ⟨primeLambda_lower_of_forall lo hlo, verify_primeLambda_upper N hi hcheck⟩

private theorem primesLE_three :
    primesLE 3 = ({2, 3} : Finset Nat) := by
  ext q
  constructor
  · intro hq
    simp only [primesLE, Finset.mem_filter, Finset.mem_range] at hq
    have hq_le : q ≤ 3 := Nat.lt_succ_iff.mp hq.1
    have hp : Nat.Prime q := hq.2
    interval_cases q
    · exact False.elim (nat_not_prime_zero hp)
    · exact False.elim (nat_not_prime_one hp)
    · simp
    · simp
  · intro hq
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl
    · simp [primesLE, nat_prime_two]
    · simp [primesLE, nat_prime_three]

private theorem primesLE_lt_five_subset_three {M : Nat} (hM : M < 5) :
    primesLE M ⊆ primesLE 3 := by
  intro q hq
  simp only [primesLE, Finset.mem_filter, Finset.mem_range] at hq
  rw [primesLE_three]
  have hq5 : q < 5 := by omega
  have hp : Nat.Prime q := hq.2
  interval_cases q
  · exact False.elim (nat_not_prime_zero hp)
  · exact False.elim (nat_not_prime_one hp)
  · simp
  · simp
  · exact False.elim (nat_not_prime_four hp)

private theorem prime_tail_pointwise_three {M : Nat} (hM : 5 ≤ M)
    {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    qProd (primesLE 3) u - qProd (primesLE M) u ≤ qProd ({3} : Finset Nat) u * u ^ 5 := by
  classical
  let A := primesLE M \ primesLE 3
  have hST : primesLE 3 ⊆ primesLE M := primesLE_subset (by omega)
  have hbase := qProd_sub_le_commonPrefix_sum (R := primesLE 3) (S := primesLE 3)
    (T := primesLE M) (by intro q hq; exact hq) hST hu
  have hodd : ∀ q ∈ A, Odd q := by
    intro q hq
    have hq' : q ∈ primesLE M ∧ q ∉ primesLE 3 := by
      simpa only [A, Finset.mem_sdiff] using hq
    have hqM' : q < M + 1 ∧ Nat.Prime q := by
      simpa only [primesLE, Finset.mem_filter, Finset.mem_range] using hq'.1
    have hp : Nat.Prime q := by
      exact hqM'.2
    apply hp.odd_of_ne_two
    intro h2
    apply hq'.2
    rw [h2, primesLE_three]
    simp
  have h5 : ∀ q ∈ A, 5 ≤ q := by
    intro q hq
    have hq' : q ∈ primesLE M ∧ q ∉ primesLE 3 := by
      simpa only [A, Finset.mem_sdiff] using hq
    have hqM' : q < M + 1 ∧ Nat.Prime q := by
      simpa only [primesLE, Finset.mem_filter, Finset.mem_range] using hq'.1
    by_contra hlt
    have hq5 : q < 5 := by omega
    have hq_mem3 : q ∈ primesLE 3 := by
      rw [primesLE_three]
      have hp : Nat.Prime q := hqM'.2
      interval_cases q
      · exact False.elim (nat_not_prime_zero hp)
      · exact False.elim (nat_not_prime_one hp)
      · simp
      · simp
      · exact False.elim (nat_not_prime_four hp)
    exact hq'.2 hq_mem3
  have hA_M : ∀ q ∈ A, q < M + 1 := by
    intro q hq
    have hq' : q ∈ primesLE M ∧ q ∉ primesLE 3 := by
      simpa only [A, Finset.mem_sdiff] using hq
    have hqM' : q < M + 1 ∧ Nat.Prime q := by
      simpa only [primesLE, Finset.mem_filter, Finset.mem_range] using hq'.1
    exact hqM'.1
  have hsum_le := odd_tail_sum_le_geom A M hu hodd h5 hA_M
  have hgeom := odd_tail_telescope_bound M hu
  have h1u2_nonneg : 0 ≤ 1 - u ^ 2 := sub_nonneg.mpr (pow_mem_unit_interval hu 2).2
  have htail : (1 - u ^ 2) * (∑ q ∈ A, u ^ q) ≤ u ^ 5 := by
    calc
      (1 - u ^ 2) * (∑ q ∈ A, u ^ q)
          ≤ (1 - u ^ 2) * (∑ j ∈ Finset.range (M + 1), u ^ (5 + 2 * j)) :=
            mul_le_mul_of_nonneg_left hsum_le h1u2_nonneg
      _ ≤ u ^ 5 := hgeom
  have hq3 : qProd (primesLE 3) u = (1 - u ^ 2) * (1 - u ^ 3) := by
    rw [primesLE_three]
    simp [qProd]
  have hsingle3 : qProd ({3} : Finset Nat) u = 1 - u ^ 3 := by
    simp [qProd]
  have hfactor_nonneg : 0 ≤ 1 - u ^ 3 := sub_nonneg.mpr (pow_mem_unit_interval hu 3).2
  calc
    qProd (primesLE 3) u - qProd (primesLE M) u
        ≤ qProd (primesLE 3) u * ∑ q ∈ primesLE M \ primesLE 3, u ^ q := hbase
    _ = (1 - u ^ 3) * ((1 - u ^ 2) * ∑ q ∈ A, u ^ q) := by
        simp only [A]
        rw [hq3]
        ring
    _ ≤ (1 - u ^ 3) * u ^ 5 := mul_le_mul_of_nonneg_left htail hfactor_nonneg
    _ = qProd ({3} : Finset Nat) u * u ^ 5 := by rw [hsingle3]

private theorem qProd_intervalIntegrable (S : Finset Nat) :
    IntervalIntegrable (fun u => qProd S u) MeasureTheory.volume (0 : ℝ) 1 := by
  classical
  unfold qProd
  apply Continuous.intervalIntegrable
  exact continuous_finset_prod S fun n hn =>
    continuous_const.sub (continuous_id.pow n)

/-- The elementary finite odd-tail certificate: every prime truncation is at least `19/36`. -/
theorem primeFRat_lower_nineteen_thirtysix (M : Nat) :
    ((19 / 36 : ℚ) : ℝ) ≤ (primeFRat M : ℝ) := by
  by_cases hM : M < 5
  · have hsubset : primesLE M ⊆ primesLE 3 := primesLE_lt_five_subset_three hM
    have hmono : F (primesLE 3) ≤ F (primesLE M) := F_antitone hsubset
    unfold primeFRat
    change ((19 / 36 : ℚ) : ℝ) ≤ (finiteIntegralRat (primesLE M) : ℝ)
    rw [finiteIntegralRat_correct]
    have hF3 : F (primesLE 3) = ((7 / 12 : ℚ) : ℝ) := by
      rw [← finiteIntegralRat_correct]
      have hval : finiteIntegralRat (primesLE 3) = 7 / 12 := by native_decide
      exact_mod_cast hval
    have hmono' : ((7 / 12 : ℚ) : ℝ) ≤ F (primesLE M) := by
      simpa [hF3] using hmono
    norm_num at hmono' ⊢
    linarith
  · have hM5 : 5 ≤ M := by omega
    have hsub_int :
        F (primesLE 3) - F (primesLE M) ≤ moment ({3} : Finset Nat) 5 := by
      unfold F moment
      have hInt3 := qProd_intervalIntegrable (primesLE 3)
      have hIntM := qProd_intervalIntegrable (primesLE M)
      have hIntSub := hInt3.sub hIntM
      have hIntB : IntervalIntegrable
          (fun u : ℝ => qProd ({3} : Finset Nat) u * u ^ 5)
          MeasureTheory.volume (0 : ℝ) 1 := by
        apply Continuous.intervalIntegrable
        exact (by
          classical
          unfold qProd
          exact (continuous_finset_prod ({3} : Finset Nat) fun n hn =>
            continuous_const.sub (continuous_id.pow n)).mul (continuous_id.pow 5))
      have hle := intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1)
        hIntSub hIntB (fun u hu => prime_tail_pointwise_three hM5 hu)
      rwa [intervalIntegral.integral_sub hInt3 hIntM] at hle
    unfold primeFRat
    rw [finiteIntegralRat_correct]
    have hF3 : F (primesLE 3) = ((7 / 12 : ℚ) : ℝ) := by
      rw [← finiteIntegralRat_correct]
      have hval : finiteIntegralRat (primesLE 3) = 7 / 12 := by native_decide
      exact_mod_cast hval
    have hmom : moment ({3} : Finset Nat) 5 = ((1 / 18 : ℚ) : ℝ) := by
      rw [← momentRat_correct]
      have hval : momentRat ({3} : Finset Nat) 5 = 1 / 18 := by native_decide
      exact_mod_cast hval
    rw [hF3, hmom] at hsub_int
    norm_num at hsub_int ⊢
    linarith

/-- Certified qualitative lower bound for the prime directed limit. -/
theorem primeLambda_lower_nineteen_thirtysix :
    ((19 / 36 : ℚ) : ℝ) ≤ primeLambda :=
  primeLambda_lower_of_forall (19 / 36) primeFRat_lower_nineteen_thirtysix

theorem primeLambda_gt_half : (1 : ℝ) / 2 < primeLambda := by
  have h := primeLambda_lower_nineteen_thirtysix
  norm_num at h ⊢
  linarith

end LeanCert.QProduct
