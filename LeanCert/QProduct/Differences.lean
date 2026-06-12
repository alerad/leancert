/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.QProduct.Stability

/-!
# Difference calculus for finite q-product integrals

Removing an exponent from `F S = ∫₀¹ ∏_{n∈S}(1-uⁿ) du` changes the value by
exactly a moment of the remaining product, and mixed second differences are
moments at the *sum* of the removed exponents:

* `F_erase_sub_eq_moment` :
  `F (S.erase c) - F S = moment (S.erase c) c`
* `F_second_difference_eq_moment` :
  `F S - F (S.erase c) - F (S.erase d) + F ((S.erase c).erase d)
     = moment ((S.erase c).erase d) (c + d)`

Both right-hand sides are nonnegative, so single-exponent removals only
increase the integral (`F_erase_sub_nonneg`), removals of smaller exponents
increase it more (`moment_antitone_exponent`), and the family of differences
is discretely convex (`F_second_difference_nonneg`). The second difference
depends on the removed pair only through `c + d`, which is the analytic
source of the subset-sum expansion of `F`.

These identities support self-bounding tail estimates for directed-limit
certificates: consecutive truncation increments are moments, and moment
monotonicity converts observed increments into certified tail majorants.
-/

namespace LeanCert.QProduct

open MeasureTheory intervalIntegral

/-- `qProd` is continuous (duplicated here to keep this file independent of
the infinite-product development). -/
private theorem qProd_continuous' (S : Finset Nat) :
    Continuous fun u : ℝ => qProd S u := by
  unfold qProd
  exact continuous_finsetProd S fun n _ => continuous_const.sub (continuous_pow n)

private theorem qProd_intervalIntegrable (S : Finset Nat) :
    IntervalIntegrable (fun u => qProd S u) volume (0:ℝ) 1 :=
  (qProd_continuous' S).intervalIntegrable 0 1

private theorem qProd_mul_pow_intervalIntegrable (S : Finset Nat) (k : Nat) :
    IntervalIntegrable (fun u => qProd S u * u ^ k) volume (0:ℝ) 1 :=
  ((qProd_continuous' S).mul (continuous_pow k)).intervalIntegrable 0 1

/-- Moments of q-products are nonnegative. -/
theorem moment_nonneg (S : Finset Nat) (k : Nat) : 0 ≤ moment S k := by
  unfold moment
  apply intervalIntegral.integral_nonneg (by norm_num)
  intro u hu
  exact mul_nonneg (qProd_nonneg S hu) (pow_nonneg hu.1 k)

/-- Moments are antitone in the exponent. -/
theorem moment_antitone_exponent (S : Finset Nat) {k l : Nat} (hkl : k ≤ l) :
    moment S l ≤ moment S k := by
  unfold moment
  apply intervalIntegral.integral_mono_on (by norm_num)
    (qProd_mul_pow_intervalIntegrable S l) (qProd_mul_pow_intervalIntegrable S k)
  intro u hu
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_of_le_one hu.1 hu.2 hkl) (qProd_nonneg S hu)

/-- Removing the factor of an exponent `c ∈ S` splits the product. -/
theorem qProd_erase_mul {S : Finset Nat} {c : Nat} (hc : c ∈ S) (u : ℝ) :
    qProd S u = (1 - u ^ c) * qProd (S.erase c) u := by
  unfold qProd
  exact (Finset.mul_prod_erase S _ hc).symm

/-- **First difference = moment.** Removing one exponent raises the integral
by exactly the corresponding moment of the remaining product. -/
theorem F_erase_sub_eq_moment {S : Finset Nat} {c : Nat} (hc : c ∈ S) :
    F (S.erase c) - F S = moment (S.erase c) c := by
  unfold F moment
  rw [← intervalIntegral.integral_sub (qProd_intervalIntegrable (S.erase c))
    (qProd_intervalIntegrable S)]
  apply intervalIntegral.integral_congr
  intro u _
  show qProd (S.erase c) u - qProd S u = qProd (S.erase c) u * u ^ c
  rw [qProd_erase_mul hc]
  ring

/-- Single-exponent removal never decreases the integral. -/
theorem F_erase_sub_nonneg {S : Finset Nat} {c : Nat} (hc : c ∈ S) :
    0 ≤ F (S.erase c) - F S := by
  rw [F_erase_sub_eq_moment hc]
  exact moment_nonneg _ _

/-- **Second difference = moment at the sum.** The mixed second difference of
removals depends on the removed pair `{c, d}` only through `c + d`. -/
theorem F_second_difference_eq_moment {S : Finset Nat} {c d : Nat}
    (hc : c ∈ S) (hd : d ∈ S) (hcd : c ≠ d) :
    F S - F (S.erase c) - F (S.erase d) + F ((S.erase c).erase d) =
      moment ((S.erase c).erase d) (c + d) := by
  have hd' : d ∈ S.erase c := Finset.mem_erase.mpr ⟨(Ne.symm hcd), hd⟩
  have hc' : c ∈ S.erase d := Finset.mem_erase.mpr ⟨hcd, hc⟩
  have hcomm : (S.erase d).erase c = (S.erase c).erase d := by
    ext x
    simp only [Finset.mem_erase]
    tauto
  unfold F moment
  rw [← intervalIntegral.integral_sub (qProd_intervalIntegrable S)
        (qProd_intervalIntegrable (S.erase c)),
      ← intervalIntegral.integral_sub
        ((qProd_intervalIntegrable S).sub (qProd_intervalIntegrable (S.erase c)))
        (qProd_intervalIntegrable (S.erase d)),
      ← intervalIntegral.integral_add
        (((qProd_intervalIntegrable S).sub
            (qProd_intervalIntegrable (S.erase c))).sub
          (qProd_intervalIntegrable (S.erase d)))
        (qProd_intervalIntegrable ((S.erase c).erase d))]
  apply intervalIntegral.integral_congr
  intro u _
  show qProd S u - qProd (S.erase c) u - qProd (S.erase d) u +
      qProd ((S.erase c).erase d) u =
    qProd ((S.erase c).erase d) u * u ^ (c + d)
  have h1 : qProd S u = (1 - u ^ c) * ((1 - u ^ d) * qProd ((S.erase c).erase d) u) := by
    rw [qProd_erase_mul hc, qProd_erase_mul hd']
  have h2 : qProd (S.erase c) u = (1 - u ^ d) * qProd ((S.erase c).erase d) u :=
    qProd_erase_mul hd' u
  have h3 : qProd (S.erase d) u = (1 - u ^ c) * qProd ((S.erase c).erase d) u := by
    rw [qProd_erase_mul hc', hcomm]
  simp only [h1, h2, h3, pow_add]
  ring

/-- Discrete convexity: mixed second differences are nonnegative. -/
theorem F_second_difference_nonneg {S : Finset Nat} {c d : Nat}
    (hc : c ∈ S) (hd : d ∈ S) (hcd : c ≠ d) :
    0 ≤ F S - F (S.erase c) - F (S.erase d) + F ((S.erase c).erase d) := by
  rw [F_second_difference_eq_moment hc hd hcd]
  exact moment_nonneg _ _

/-- The second difference factors through the sum of the removed exponents:
two removal pairs over the same base with equal sums produce identical second
differences. -/
theorem F_second_difference_factors_through_sum {S : Finset Nat}
    {c d c' d' : Nat} (hc : c ∈ S) (hd : d ∈ S) (hcd : c ≠ d)
    (hc' : c' ∈ S) (hd' : d' ∈ S) (hcd' : c' ≠ d')
    (hbase : (S.erase c).erase d = (S.erase c').erase d')
    (hsum : c + d = c' + d') :
    F S - F (S.erase c) - F (S.erase d) + F ((S.erase c).erase d) =
      F S - F (S.erase c') - F (S.erase d') + F ((S.erase c').erase d') := by
  rw [F_second_difference_eq_moment hc hd hcd,
    F_second_difference_eq_moment hc' hd' hcd', hbase, hsum]

/-! ### Geometric tail collapse

A retained factor `(1 - u)` (respectively `(1 - u²)`) damps the geometric sum
of all missing exponents at once: the gap between a truncation and any finer
truncation collapses to a single moment of the truncation with the damping
exponent removed. This is the engine for computable tail majorants in
directed-limit certificates over arbitrary exponent systems. -/

private theorem one_sub_mul_geom_sum_Ico {u : ℝ} (m : Nat) :
    ∀ {n : Nat}, m ≤ n →
      (1 - u) * ∑ q ∈ Finset.Ico m n, u ^ q = u ^ m - u ^ n := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
      rw [Finset.sum_Ico_succ_top hn]
      ring_nf
      ring_nf at ih
      linarith [ih]

/-- A damped geometric sum over distinct exponents at least `m` is at most
`u ^ m` on `[0, 1]`. -/
theorem one_sub_mul_sum_pow_le {A : Finset Nat} {m : Nat}
    (hm : ∀ q ∈ A, m ≤ q) {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    (1 - u) * ∑ q ∈ A, u ^ q ≤ u ^ m := by
  rcases A.eq_empty_or_nonempty with rfl | hA
  · simpa using pow_nonneg hu.1 m
  · set M := A.max' hA with hM
    have hsub : A ⊆ Finset.Ico m (M + 1) := by
      intro q hq
      exact Finset.mem_Ico.mpr ⟨hm q hq, Nat.lt_succ_of_le (A.le_max' q hq)⟩
    have hmono : ∑ q ∈ A, u ^ q ≤ ∑ q ∈ Finset.Ico m (M + 1), u ^ q :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun q _ _ => pow_nonneg hu.1 q)
    have hmM : m ≤ M + 1 :=
      le_trans (hm _ (A.max'_mem hA)) (Nat.le_succ M)
    calc (1 - u) * ∑ q ∈ A, u ^ q
        ≤ (1 - u) * ∑ q ∈ Finset.Ico m (M + 1), u ^ q :=
          mul_le_mul_of_nonneg_left hmono (by linarith [hu.2])
      _ = u ^ m - u ^ (M + 1) := one_sub_mul_geom_sum_Ico m hmM
      _ ≤ u ^ m := by linarith [pow_nonneg hu.1 (M + 1)]

/-- Pointwise tail collapse with the `1`-damper: if `1 ∈ S ⊆ T` and every
exponent of `T` missing from `S` is at least `m`, the truncation gap is
bounded by the `m`-th moment integrand of `S.erase 1`. -/
theorem qProd_sub_le_erase_one_pow {S T : Finset Nat} (h1 : 1 ∈ S)
    (hST : S ⊆ T) {m : Nat} (hm : ∀ q ∈ T, q ∉ S → m ≤ q)
    {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    qProd S u - qProd T u ≤ qProd (S.erase 1) u * u ^ m := by
  have hsplit : qProd S u = (1 - u ^ 1) * qProd (S.erase 1) u :=
    qProd_erase_mul h1 u
  have hbase := qProd_sub_le_commonPrefix_sum (R := S) (S := S) (T := T)
    (subset_refl S) hST hu
  have hdamp : (1 - u) * ∑ q ∈ T \ S, u ^ q ≤ u ^ m :=
    one_sub_mul_sum_pow_le (fun q hq => hm q (Finset.mem_sdiff.mp hq).1
      (Finset.mem_sdiff.mp hq).2) hu
  have hP := qProd_nonneg (S.erase 1) hu
  have hsum_nonneg : 0 ≤ ∑ q ∈ T \ S, u ^ q :=
    Finset.sum_nonneg fun q _ => pow_nonneg hu.1 q
  calc qProd S u - qProd T u
      ≤ qProd S u * ∑ q ∈ T \ S, u ^ q := hbase
    _ = qProd (S.erase 1) u * ((1 - u) * ∑ q ∈ T \ S, u ^ q) := by
        rw [hsplit]
        ring_nf
    _ ≤ qProd (S.erase 1) u * u ^ m :=
        mul_le_mul_of_nonneg_left hdamp hP

/-- Pointwise tail collapse with the `2`-damper: as above with `2 ∈ S`, at
the cost of a factor `2`. -/
theorem qProd_sub_le_erase_two_pow {S T : Finset Nat} (h2 : 2 ∈ S)
    (hST : S ⊆ T) {m : Nat} (hm : ∀ q ∈ T, q ∉ S → m ≤ q)
    {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    qProd S u - qProd T u ≤ 2 * (qProd (S.erase 2) u * u ^ m) := by
  have hsplit : qProd S u = (1 - u ^ 2) * qProd (S.erase 2) u :=
    qProd_erase_mul h2 u
  have hbase := qProd_sub_le_commonPrefix_sum (R := S) (S := S) (T := T)
    (subset_refl S) hST hu
  have hdamp : (1 - u) * ∑ q ∈ T \ S, u ^ q ≤ u ^ m :=
    one_sub_mul_sum_pow_le (fun q hq => hm q (Finset.mem_sdiff.mp hq).1
      (Finset.mem_sdiff.mp hq).2) hu
  have hP := qProd_nonneg (S.erase 2) hu
  have hsum_nonneg : 0 ≤ ∑ q ∈ T \ S, u ^ q :=
    Finset.sum_nonneg fun q _ => pow_nonneg hu.1 q
  have h1u : (0:ℝ) ≤ 1 + u := by linarith [hu.1]
  have hfac : (1 - u ^ 2) = (1 + u) * (1 - u) := by ring
  calc qProd S u - qProd T u
      ≤ qProd S u * ∑ q ∈ T \ S, u ^ q := hbase
    _ = (1 + u) * qProd (S.erase 2) u * ((1 - u) * ∑ q ∈ T \ S, u ^ q) := by
        rw [hsplit, hfac]
        ring
    _ ≤ (1 + u) * qProd (S.erase 2) u * u ^ m := by
        apply mul_le_mul_of_nonneg_left hdamp
        exact mul_nonneg h1u hP
    _ ≤ 2 * (qProd (S.erase 2) u * u ^ m) := by
        have hu2 : (1:ℝ) + u ≤ 2 := by linarith [hu.2]
        have hmom : 0 ≤ qProd (S.erase 2) u * u ^ m :=
          mul_nonneg hP (pow_nonneg hu.1 m)
        nlinarith [hmom, hu2]

/-- **Tail collapse, integral form (1-damper).** Any finer truncation is
within one computable moment of the current one. -/
theorem F_sub_le_moment_of_one_mem {S T : Finset Nat} (h1 : 1 ∈ S)
    (hST : S ⊆ T) {m : Nat} (hm : ∀ q ∈ T, q ∉ S → m ≤ q) :
    F S - F T ≤ moment (S.erase 1) m := by
  unfold F moment
  rw [← intervalIntegral.integral_sub (qProd_intervalIntegrable S)
    (qProd_intervalIntegrable T)]
  apply intervalIntegral.integral_mono_on (by norm_num)
    ((qProd_intervalIntegrable S).sub (qProd_intervalIntegrable T))
    (qProd_mul_pow_intervalIntegrable (S.erase 1) m)
  intro u hu
  exact qProd_sub_le_erase_one_pow h1 hST hm hu

/-- **Tail collapse, integral form (2-damper).** -/
theorem F_sub_le_two_mul_moment_of_two_mem {S T : Finset Nat} (h2 : 2 ∈ S)
    (hST : S ⊆ T) {m : Nat} (hm : ∀ q ∈ T, q ∉ S → m ≤ q) :
    F S - F T ≤ 2 * moment (S.erase 2) m := by
  have hint : IntervalIntegrable
      (fun u => 2 * (qProd (S.erase 2) u * u ^ m)) volume (0:ℝ) 1 :=
    (qProd_mul_pow_intervalIntegrable (S.erase 2) m).const_mul 2
  unfold F moment
  rw [← intervalIntegral.integral_sub (qProd_intervalIntegrable S)
    (qProd_intervalIntegrable T), ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_mono_on (by norm_num)
    ((qProd_intervalIntegrable S).sub (qProd_intervalIntegrable T)) hint
  intro u hu
  exact qProd_sub_le_erase_two_pow h2 hST hm hu

end LeanCert.QProduct
