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

end LeanCert.QProduct
