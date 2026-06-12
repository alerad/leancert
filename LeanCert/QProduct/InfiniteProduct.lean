/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.QProduct.PrimeLambda
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# The analytic bridge: `primeLambda` is the prime product integral

`primeLambda` is defined as the infimum of the truncation values
`primeFRat N`. This file identifies it with the integral of the infinite
prime product:

  `primeLambda = ∫ u in 0..1, ∏' p : Nat.Primes, (1 - u ^ (p : ℕ))`.

The proof has three parts:

1. pointwise, for `0 ≤ u < 1`, the finite products `qProd (primesLE N) u`
   converge to the infinite product (multipliability via comparison with the
   geometric series);
2. dominated convergence (dominating function `1`) passes the limit through
   the integral;
3. the truncation integrals are antitone and bounded below, so they converge
   to their infimum, which is `primeLambda` by definition; limits are unique.

Consequently every certified enclosure of `primeLambda` in this development
is an enclosure of the analytic constant.
-/

namespace LeanCert.QProduct

open Filter MeasureTheory intervalIntegral Set
open scoped Topology

/-- `qProd S` is continuous. -/
theorem qProd_continuous (S : Finset Nat) : Continuous fun u : ℝ => qProd S u := by
  unfold qProd
  exact continuous_finsetProd S fun n _ => continuous_const.sub (continuous_pow n)

/-- The prime-indicator geometric coefficients are summable for `0 ≤ u < 1`. -/
theorem summable_primeIndicator_pow {u : ℝ} (h0 : 0 ≤ u) (h1 : u < 1) :
    Summable fun n : ℕ => if Nat.Prime n then -(u ^ n) else 0 := by
  have hgeom : Summable fun n : ℕ => u ^ n := summable_geometric_of_lt_one h0 h1
  refine Summable.of_abs (hgeom.of_nonneg_of_le (fun n => abs_nonneg _) fun n => ?_)
  by_cases hn : Nat.Prime n
  · simp [hn, abs_of_nonneg (pow_nonneg h0 n)]
  · simp [hn, pow_nonneg h0 n]

/-- Pointwise convergence of the finite prime products to the infinite
product, for `0 ≤ u < 1`. -/
theorem qProd_primesLE_tendsto_tprod {u : ℝ} (h0 : 0 ≤ u) (h1 : u < 1) :
    Tendsto (fun N => qProd (primesLE N) u) atTop
      (𝓝 (∏' p : Nat.Primes, (1 - u ^ (p : ℕ)))) := by
  classical
  set h : ℕ → ℝ := fun n => if Nat.Prime n then 1 - u ^ n else 1 with hh
  have hfh : (fun n : ℕ => 1 + (if Nat.Prime n then -(u ^ n) else 0)) = h := by
    funext n
    by_cases hn : Nat.Prime n <;> simp [hh, hn, sub_eq_add_neg]
  have hM : Multipliable h := by
    rw [← hfh]
    exact Real.multipliable_one_add_of_summable (summable_primeIndicator_pow h0 h1)
  -- tprod over ℕ of `h` equals the tprod over the primes.
  have htp : ∏' n : ℕ, h n = ∏' p : Nat.Primes, (1 - u ^ (p : ℕ)) := by
    have hind :
        h = Set.mulIndicator {n : ℕ | Nat.Prime n} (fun n => 1 - u ^ n) := by
      funext n
      by_cases hn : Nat.Prime n <;>
        simp [hh, hn, Set.mem_setOf_eq]
    rw [hind, ← tprod_subtype {n : ℕ | Nat.Prime n} (fun n => 1 - u ^ n)]
    rfl
  -- partial products over `range (N+1)` are the truncations.
  have hrange : ∀ N, ∏ i ∈ Finset.range (N + 1), h i = qProd (primesLE N) u := by
    intro N
    unfold qProd primesLE
    rw [Finset.prod_filter]
  have htends := hM.hasProd.tendsto_prod_nat
  rw [htp] at htends
  have hshift :
      Tendsto (fun N : ℕ => ∏ i ∈ Finset.range (N + 1), h i) atTop
        (𝓝 (∏' p : Nat.Primes, (1 - u ^ (p : ℕ)))) :=
    htends.comp (tendsto_add_atTop_nat 1)
  simpa [hrange] using hshift

/-- Dominated convergence: the truncation integrals converge to the integral
of the infinite product. -/
theorem tendsto_primeFRat_integral_tprod :
    Tendsto (fun N => (primeFRat N : ℝ)) atTop
      (𝓝 (∫ u in (0:ℝ)..1, ∏' p : Nat.Primes, (1 - u ^ (p : ℕ)))) := by
  have hcast : ∀ N, (primeFRat N : ℝ) = F (primesLE N) := by
    intro N
    unfold primeFRat
    rw [finiteIntegralRat_correct]
  have hF : ∀ N, F (primesLE N) =
      ∫ u in Set.Ioc (0:ℝ) 1, qProd (primesLE N) u := by
    intro N
    unfold F
    exact integral_of_le (by norm_num)
  have hG : (∫ u in (0:ℝ)..1, ∏' p : Nat.Primes, (1 - u ^ (p : ℕ))) =
      ∫ u in Set.Ioc (0:ℝ) 1, ∏' p : Nat.Primes, (1 - u ^ (p : ℕ)) :=
    integral_of_le (by norm_num)
  rw [funext hcast]
  simp only [hF, hG]
  -- dominated convergence over `volume.restrict (Ioc 0 1)` with bound `1`.
  apply MeasureTheory.tendsto_integral_of_dominated_convergence
    (bound := fun _ : ℝ => (1 : ℝ))
  · exact fun N => ((qProd_continuous (primesLE N)).aestronglyMeasurable).restrict
  · exact MeasureTheory.integrableOn_const measure_Ioc_lt_top.ne
  · intro N
    refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioc).mpr
      (Filter.Eventually.of_forall fun u hu => ?_)
    have hu' : u ∈ Set.Icc (0:ℝ) 1 := ⟨hu.1.le, hu.2⟩
    have h0 := qProd_nonneg (primesLE N) hu'
    have h1 := qProd_le_one (primesLE N) hu'
    rw [Real.norm_eq_abs, abs_of_nonneg h0]
    exact h1
  · -- a.e. pointwise convergence: everywhere on `Ioc 0 1` except `u = 1`.
    have hmem : ∀ᵐ u ∂(volume.restrict (Set.Ioc (0:ℝ) 1)),
        u ∈ Set.Ioc (0:ℝ) 1 := ae_restrict_mem measurableSet_Ioc
    have hne : ∀ᵐ u : ℝ ∂volume, u ≠ (1:ℝ) := by
      have hz : volume ({(1:ℝ)} : Set ℝ) = 0 := measure_singleton _
      have := MeasureTheory.measure_eq_zero_iff_ae_notMem.mp hz
      exact this.mono fun u hu => by simpa using hu
    have hne' : ∀ᵐ u ∂(volume.restrict (Set.Ioc (0:ℝ) 1)), u ≠ (1:ℝ) :=
      hne.filter_mono (MeasureTheory.ae_mono Measure.restrict_le_self)
    filter_upwards [hmem, hne'] with u hu hu1
    exact qProd_primesLE_tendsto_tprod hu.1.le (lt_of_le_of_ne hu.2 hu1)

/-- The truncation integrals converge to `primeLambda`. -/
theorem tendsto_primeFRat_primeLambda :
    Tendsto (fun N => (primeFRat N : ℝ)) atTop (𝓝 primeLambda) := by
  have hanti : Antitone fun N => (primeFRat N : ℝ) := fun a b hab =>
    primeFRat_antitone hab
  have hbdd : BddBelow (Set.range fun N => (primeFRat N : ℝ)) := by
    refine ⟨0, ?_⟩
    rintro x ⟨M, rfl⟩
    show (0:ℝ) ≤ (primeFRat M : ℝ)
    unfold primeFRat
    rw [finiteIntegralRat_correct]
    unfold F
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro u hu
    exact qProd_nonneg _ hu
  exact tendsto_atTop_ciInf hanti hbdd

/-- **The analytic bridge**: the directed prime limit equals the integral of
the infinite prime product. Every certified enclosure of `primeLambda` is an
enclosure of this analytic constant. -/
theorem primeLambda_eq_integral_tprod :
    primeLambda = ∫ u in (0:ℝ)..1, ∏' p : Nat.Primes, (1 - u ^ (p : ℕ)) :=
  tendsto_nhds_unique tendsto_primeFRat_primeLambda tendsto_primeFRat_integral_tprod

end LeanCert.QProduct
