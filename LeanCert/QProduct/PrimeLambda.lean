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

`primeLambda` is defined as the infimum of the finite-truncation values. The
identification with the infinite prime-product integral
`∫₀¹ ∏'_p (1 - u^p) du` is proved in `QProduct.InfiniteProduct`
(`primeLambda_eq_integral_tprod`), so certified enclosures of `primeLambda`
are enclosures of the analytic constant.
-/

namespace LeanCert.QProduct

open scoped BigOperators

private theorem nat_prime_two : Nat.Prime 2 := Nat.prime_two
private theorem nat_prime_three : Nat.Prime 3 := Nat.prime_three
private theorem nat_not_prime_zero : ¬ Nat.Prime 0 := Nat.not_prime_zero
private theorem nat_not_prime_one : ¬ Nat.Prime 1 := Nat.not_prime_one
private theorem nat_not_prime_four : ¬ Nat.Prime 4 := by decide

/-- Prime exponents up to `N`. -/
def primesLE (N : Nat) : Finset Nat :=
  (Finset.range (N + 1)).filter Nat.Prime

/-- Exact rational value of the prime truncation integral. -/
def primeFRat (N : Nat) : ℚ :=
  finiteIntegralRat (primesLE N)

/-- Exact rational error integral used in the prime-limit sandwich:
`∫ u^m ∏_{p ≤ N, p ≠ 2} (1 - u^p) du`. -/
def primeSandwichErrorRat (N m : Nat) : ℚ :=
  momentRat ((primesLE N).filter (fun p => p ≠ 2)) m

/-- Exact rational lower endpoint for the prime-limit sandwich. -/
def primeSandwichLowerRat (N m : Nat) : ℚ :=
  primeFRat N - primeSandwichErrorRat N m

/-- Pointwise lower-envelope function used in the prime sandwich. -/
noncomputable def primeSandwichLowerFun (N m : Nat) (u : ℝ) : ℝ :=
  qProd (primesLE N) u - qProd ((primesLE N).filter (fun p => p ≠ 2)) u * u ^ m

/-- Prime q-product directed limit, defined as the infimum of the
finite-truncation values `primeFRat N`.

The truncations are antitone (`primeFRat_antitone`) and bounded below by `0`,
so this infimum coincides with the limit of the truncation sequence, and by
`primeLambda_eq_integral_tprod` (in `QProduct.InfiniteProduct`) it equals the
integral of the infinite prime product `∫₀¹ ∏'_p (1 - u^p) du`. -/
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

/-- Golden theorem for prime-limit upper certificates.

The checker verifies an upper bound for one finite prime truncation. Antitonicity
then makes the same rational an upper bound for the directed prime limit. -/
theorem verify_primeLambda_upper (N : Nat) (hi : ℚ)
    (hcheck : checkPrimeLambdaUpper N hi = true) :
    primeLambda ≤ (hi : ℝ) := by
  simp only [checkPrimeLambdaUpper, decide_eq_true_eq] at hcheck
  exact le_trans (primeLambda_le_trunc N) (by exact_mod_cast hcheck)

/-- Combined prime-limit interval bridge. The lower side is supplied as a
mathematical tail proof; the upper side is checked exactly by computation. This
is intentionally not a purely boolean certificate, because lower bounds for the
directed limit need a tail argument. -/
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
  exact continuous_finsetProd S fun n hn =>
    continuous_const.sub (continuous_id.pow n)

/-- Exact evaluation of the two-prime truncation integral, axiom-free
    (powerset sum expanded via `Finset.sum_powerset_insert` + `norm_num`). -/
private lemma finiteIntegralRat_primesLE_three :
    finiteIntegralRat (primesLE 3) = 7 / 12 := by
  rw [primesLE_three, show ({2, 3} : Finset Nat) = insert 2 {3} from rfl]
  unfold finiteIntegralRat
  rw [Finset.sum_powerset_insert (by norm_num),
      show ({3} : Finset Nat) = insert 3 ∅ from rfl,
      Finset.sum_powerset_insert (by norm_num),
      Finset.sum_powerset_insert (by norm_num),
      Finset.powerset_empty]
  simp [subsetSign, subsetWeight]
  norm_num

/-- Exact evaluation of the `{3}`-moment at `k = 5`, axiom-free. -/
private lemma momentRat_three_five : momentRat ({3} : Finset Nat) 5 = 1 / 18 := by
  unfold momentRat
  rw [show ({3} : Finset Nat) = insert 3 ∅ from rfl,
      Finset.sum_powerset_insert (by norm_num), Finset.powerset_empty]
  simp [subsetSign, subsetWeight]
  norm_num

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
      have hval : finiteIntegralRat (primesLE 3) = 7 / 12 :=
        finiteIntegralRat_primesLE_three
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
        exact by
          classical
          unfold qProd
          exact (continuous_finsetProd ({3} : Finset Nat) fun n hn =>
            continuous_const.sub (continuous_id.pow n)).mul (continuous_id.pow 5)
      have hle := intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1)
        hIntSub hIntB (fun u hu => prime_tail_pointwise_three hM5 hu)
      rwa [intervalIntegral.integral_sub hInt3 hIntM] at hle
    unfold primeFRat
    rw [finiteIntegralRat_correct]
    have hF3 : F (primesLE 3) = ((7 / 12 : ℚ) : ℝ) := by
      rw [← finiteIntegralRat_correct]
      have hval : finiteIntegralRat (primesLE 3) = 7 / 12 :=
        finiteIntegralRat_primesLE_three
      exact_mod_cast hval
    have hmom : moment ({3} : Finset Nat) 5 = ((1 / 18 : ℚ) : ℝ) := by
      rw [← momentRat_correct]
      have hval : momentRat ({3} : Finset Nat) 5 = 1 / 18 := momentRat_three_five
      exact_mod_cast hval
    rw [hF3, hmom] at hsub_int
    norm_num at hsub_int ⊢
    linarith

theorem prime_odd_of_gt_two {p : Nat} (hp : Nat.Prime p) (hp2 : 2 < p) : Odd p := by
  rcases Nat.Prime.eq_two_or_odd hp with hp_eq | hp_odd
  · omega
  · exact Nat.odd_iff.mpr hp_odd

theorem odd_ge_form {m p : Nat} (hm : Odd m) (hp : Odd p) (hmp : m ≤ p) :
    ∃ k, p = m + 2 * k := by
  rcases hm with ⟨a, ha⟩
  rcases hp with ⟨b, hb⟩
  refine ⟨b - a, ?_⟩
  omega

theorem telescope_odd_sum_bound_from {m : Nat} (hm : Odd m) (S : Finset Nat)
    (hS : ∀ p ∈ S, Odd p ∧ m ≤ p)
    {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    (1 - u ^ 2) * ∑ p ∈ S, u ^ p ≤ u ^ m := by
  classical
  let f : Nat → Nat := fun p => (p - m) / 2
  have hodd : ∀ p ∈ S, Odd p := fun p hp => (hS p hp).1
  have hge : ∀ p ∈ S, m ≤ p := fun p hp => (hS p hp).2
  have hform : ∀ p ∈ S, p = m + 2 * f p := by
    intro p hp
    obtain ⟨k, hk⟩ := odd_ge_form hm (hodd p hp) (hge p hp)
    have hf : f p = k := by
      change (p - m) / 2 = k
      omega
    rw [hf, hk]
  let K := S.image f
  have hsum_eq : ∑ p ∈ S, u ^ p = ∑ k ∈ K, u ^ (m + 2 * k) := by
    unfold K
    have hrewrite : ∑ p ∈ S, u ^ p = ∑ p ∈ S, u ^ (m + 2 * f p) := by
      apply Finset.sum_congr rfl
      intro p hp
      exact congrArg (fun e => u ^ e) (hform p hp)
    rw [hrewrite]
    rw [Finset.sum_image]
    intro p hp q hq hf
    have hpform := hform p hp
    have hqform := hform q hq
    omega
  rw [hsum_eq]
  by_cases hK : K = ∅
  · simp [hK, pow_nonneg hu.1 m]
  · obtain ⟨M, hM⟩ := Finset.exists_max_image K id (Finset.nonempty_of_ne_empty hK)
    let n := M + 1
    have hK_sub : K ⊆ Finset.range n := by
      intro k hk
      simp only [Finset.mem_range]
      have hkM := hM.2 k hk
      simp only [id] at hkM
      exact Nat.lt_add_one_of_le hkM
    have hsum_le :
        ∑ k ∈ K, u ^ (m + 2 * k) ≤
          ∑ k ∈ Finset.range n, u ^ (m + 2 * k) :=
      Finset.sum_le_sum_of_subset_of_nonneg hK_sub
        (fun _ _ _ => pow_nonneg hu.1 _)
    have htel :
        (1 - u ^ 2) * (∑ k ∈ Finset.range n, u ^ (m + 2 * k)) =
          u ^ m - u ^ (m + 2 * n) := by
      induction n with
      | zero => simp
      | succ n ih =>
          rw [Finset.sum_range_succ, mul_add, ih]
          have h1 :
              (1 - u ^ 2) * u ^ (m + 2 * n) =
                u ^ (m + 2 * n) - u ^ (m + 2 * n) * u ^ 2 := by
            ring
          rw [h1, ← pow_add]
          ring_nf
    have h1u2_nonneg : 0 ≤ 1 - u ^ 2 :=
      sub_nonneg.mpr (pow_mem_unit_interval hu 2).2
    calc
      (1 - u ^ 2) * ∑ k ∈ K, u ^ (m + 2 * k)
          ≤ (1 - u ^ 2) * ∑ k ∈ Finset.range n, u ^ (m + 2 * k) :=
            mul_le_mul_of_nonneg_left hsum_le h1u2_nonneg
      _ = u ^ m - u ^ (m + 2 * n) := htel
      _ ≤ u ^ m := by
        have hnonneg : 0 ≤ u ^ (m + 2 * n) := pow_nonneg hu.1 _
        linarith

theorem primeSandwichLowerFun_pointwise_of_tail_ge {N m : Nat}
    (hN : 2 ≤ N) (hm : Odd m)
    (htail_ge : ∀ p, Nat.Prime p → N < p → m ≤ p)
    (S : Finset Nat)
    (hbase : primesLE N ⊆ S) (hS_primes : ∀ p ∈ S, Nat.Prime p)
    {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    primeSandwichLowerFun N m u ≤ qProd S u := by
  classical
  let B := primesLE N
  let O := B.filter (fun p => p ≠ 2)
  let T := S \ B
  let R := qProd O u
  have hsplit : qProd S u = qProd B u * qProd T u := by
    unfold qProd T B
    rw [← Finset.prod_union Finset.disjoint_sdiff]
    congr 1
    exact (Finset.union_sdiff_of_subset hbase).symm
  have hB2 : 2 ∈ B := by
    simp only [B, primesLE, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, nat_prime_two⟩
  have hB_eq : B = insert 2 O := by
    ext p
    by_cases hp : p = 2
    · subst hp
      simp [O, hB2]
    · simp [O, hp]
  have hP_eq : qProd B u = (1 - u ^ 2) * R := by
    rw [hB_eq]
    unfold R O qProd
    simp
  have hR_nonneg : 0 ≤ R := by
    unfold R
    exact qProd_nonneg O hu
  have hmain : (1 - u ^ 2) * (1 - qProd T u) ≤ u ^ m := by
    have h_weier : 1 - qProd T u ≤ ∑ p ∈ T, u ^ p := by
      unfold qProd
      simpa using one_sub_prod_one_sub_le_sum T (fun q => u ^ q)
        (fun q _hq => (pow_mem_unit_interval hu q).1)
        (fun q _hq => (pow_mem_unit_interval hu q).2)
    have h_tail : ∀ p ∈ T, Odd p ∧ m ≤ p := by
      intro p hp
      have hpS : p ∈ S := (Finset.mem_sdiff.mp hp).1
      have hp_notB : p ∉ B := (Finset.mem_sdiff.mp hp).2
      have hp_prime : Nat.Prime p := hS_primes p hpS
      have hp_gt : N < p := by
        by_contra hle
        push Not at hle
        have hpB : p ∈ B := by
          simp only [B, primesLE, Finset.mem_filter, Finset.mem_range]
          exact ⟨Nat.lt_succ_of_le hle, hp_prime⟩
        exact hp_notB hpB
      have hp_odd : Odd p := prime_odd_of_gt_two hp_prime (lt_of_le_of_lt hN hp_gt)
      exact ⟨hp_odd, htail_ge p hp_prime hp_gt⟩
    have h_bound :
        (1 - u ^ 2) * ∑ p ∈ T, u ^ p ≤ u ^ m :=
      telescope_odd_sum_bound_from hm T h_tail hu
    have h1u2_nonneg : 0 ≤ 1 - u ^ 2 :=
      sub_nonneg.mpr (pow_mem_unit_interval hu 2).2
    exact (mul_le_mul_of_nonneg_left h_weier h1u2_nonneg).trans h_bound
  unfold primeSandwichLowerFun
  change qProd B u - R * u ^ m ≤ qProd S u
  rw [hsplit, hP_eq]
  have hscalar : (1 - u ^ 2) - u ^ m ≤ (1 - u ^ 2) * qProd T u := by
    nlinarith [hmain]
  calc
    (1 - u ^ 2) * R - R * u ^ m
        = ((1 - u ^ 2) - u ^ m) * R := by ring
    _ ≤ ((1 - u ^ 2) * qProd T u) * R :=
        mul_le_mul_of_nonneg_right hscalar hR_nonneg
    _ = (1 - u ^ 2) * R * qProd T u := by ring

theorem primeSandwichLowerFun_le_prime_truncation_of_tail_ge {N m : Nat}
    (hN : 2 ≤ N) (hm : Odd m)
    (htail_ge : ∀ p, Nat.Prime p → N < p → m ≤ p)
    (M : Nat) {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    primeSandwichLowerFun N m u ≤ qProd (primesLE M) u := by
  classical
  let S := primesLE M ∪ primesLE N
  have hpoint : primeSandwichLowerFun N m u ≤ qProd S u := by
    apply primeSandwichLowerFun_pointwise_of_tail_ge hN hm htail_ge
    · exact Finset.subset_union_right
    · intro p hp
      rcases Finset.mem_union.mp hp with hpM | hpN
      · exact (by
          have hpM' : p < M + 1 ∧ Nat.Prime p := by
            simpa only [primesLE, Finset.mem_filter, Finset.mem_range] using hpM
          exact hpM'.2)
      · exact (by
          have hpN' : p < N + 1 ∧ Nat.Prime p := by
            simpa only [primesLE, Finset.mem_filter, Finset.mem_range] using hpN
          exact hpN'.2)
    · exact hu
  exact hpoint.trans (qProd_antitone_pointwise Finset.subset_union_left hu)

private theorem primeSandwichLowerFun_intervalIntegrable (N m : Nat) :
    IntervalIntegrable (fun u => primeSandwichLowerFun N m u)
      MeasureTheory.volume (0 : ℝ) 1 := by
  unfold primeSandwichLowerFun
  apply Continuous.intervalIntegrable
  exact (by
    classical
    exact (continuous_finsetProd (primesLE N) fun n hn =>
      continuous_const.sub (continuous_id.pow n)).sub
      ((continuous_finsetProd ((primesLE N).filter (fun p => p ≠ 2)) fun n hn =>
        continuous_const.sub (continuous_id.pow n)).mul (continuous_id.pow m)))

theorem integral_primeSandwichLowerFun_eq_rat (N m : Nat) :
    (∫ u in (0 : ℝ)..1, primeSandwichLowerFun N m u) =
      (primeSandwichLowerRat N m : ℝ) := by
  unfold primeSandwichLowerFun primeSandwichLowerRat primeSandwichErrorRat primeFRat
  rw [intervalIntegral.integral_sub]
  · change F (primesLE N) - moment ((primesLE N).filter (fun p => p ≠ 2)) m =
      (((finiteIntegralRat (primesLE N) - momentRat ((primesLE N).filter (fun p => p ≠ 2)) m) : ℚ) : ℝ)
    rw [← finiteIntegralRat_correct, ← momentRat_correct]
    norm_num
  · exact qProd_intervalIntegrable (primesLE N)
  · apply Continuous.intervalIntegrable
    exact (by
      classical
      exact (continuous_finsetProd ((primesLE N).filter (fun p => p ≠ 2)) fun n hn =>
        continuous_const.sub (continuous_id.pow n)).mul (continuous_id.pow m))

theorem primeSandwichLowerRat_le_truncation_of_tail_ge {N m : Nat}
    (hN : 2 ≤ N) (hm : Odd m)
    (htail_ge : ∀ p, Nat.Prime p → N < p → m ≤ p)
    (M : Nat) :
    (primeSandwichLowerRat N m : ℝ) ≤ (primeFRat M : ℝ) := by
  have hle :
      (∫ u in (0 : ℝ)..1, primeSandwichLowerFun N m u) ≤ F (primesLE M) := by
    unfold F
    exact intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1)
      (primeSandwichLowerFun_intervalIntegrable N m)
      (qProd_intervalIntegrable (primesLE M))
      (fun u hu => primeSandwichLowerFun_le_prime_truncation_of_tail_ge hN hm htail_ge M hu)
  rw [integral_primeSandwichLowerFun_eq_rat] at hle
  unfold primeFRat
  rw [finiteIntegralRat_correct]
  exact hle

theorem primeSandwichLowerRat_le_lambda_of_tail_ge {N m : Nat}
    (hN : 2 ≤ N) (hm : Odd m)
    (htail_ge : ∀ p, Nat.Prime p → N < p → m ≤ p) :
    (primeSandwichLowerRat N m : ℝ) ≤ primeLambda :=
  primeLambda_lower_of_forall (primeSandwichLowerRat N m)
    (primeSandwichLowerRat_le_truncation_of_tail_ge hN hm htail_ge)

/-- Prime product-integral sandwich in exact rational form. -/
theorem primeLambda_rational_sandwich {N m : Nat}
    (hN : 2 ≤ N) (hm : Odd m)
    (htail_ge : ∀ p, Nat.Prime p → N < p → m ≤ p) :
    (primeSandwichLowerRat N m : ℝ) ≤ primeLambda ∧
      primeLambda ≤ (primeFRat N : ℝ) :=
  ⟨primeSandwichLowerRat_le_lambda_of_tail_ge hN hm htail_ge,
    primeLambda_le_trunc N⟩

theorem primeLambda_sandwich {N m : Nat}
    (hN : 2 ≤ N) (hm : Odd m)
    (htail_ge : ∀ p, Nat.Prime p → N < p → m ≤ p) :
    (primeFRat N : ℝ) - (primeSandwichErrorRat N m : ℝ) ≤ primeLambda ∧
      primeLambda ≤ (primeFRat N : ℝ) := by
  simpa [primeSandwichLowerRat] using primeLambda_rational_sandwich hN hm htail_ge

theorem primeSandwichErrorRat_three_five :
    primeSandwichErrorRat 3 5 = 1 / 18 := by
  unfold primeSandwichErrorRat
  rw [show (primesLE 3).filter (fun p => p ≠ 2) = ({3} : Finset Nat) by decide]
  exact momentRat_three_five

theorem primeSandwichLowerRat_three_five :
    primeSandwichLowerRat 3 5 = 19 / 36 := by
  unfold primeSandwichLowerRat primeFRat
  rw [finiteIntegralRat_primesLE_three, primeSandwichErrorRat_three_five]
  norm_num

theorem primeSandwichLowerRat_three_five_le_lambda :
    (primeSandwichLowerRat 3 5 : ℝ) ≤ primeLambda := by
  apply primeSandwichLowerRat_le_lambda_of_tail_ge (N := 3) (m := 5) (by norm_num) (by decide)
  intro p hp_prime hp_gt
  have hp_ge4 : 4 ≤ p := Nat.succ_le_of_lt hp_gt
  rcases Nat.lt_or_eq_of_le hp_ge4 with hp4 | hp4
  · exact Nat.succ_le_of_lt hp4
  · exfalso
    rw [← hp4] at hp_prime
    exact nat_not_prime_four hp_prime

/-- Certified qualitative lower bound for the prime directed limit. -/
theorem primeLambda_lower_nineteen_thirtysix :
    ((19 / 36 : ℚ) : ℝ) ≤ primeLambda :=
  primeLambda_lower_of_forall (19 / 36) primeFRat_lower_nineteen_thirtysix

theorem primeLambda_gt_half : (1 : ℝ) / 2 < primeLambda := by
  have h := primeLambda_lower_nineteen_thirtysix
  norm_num at h ⊢
  linarith

end LeanCert.QProduct
