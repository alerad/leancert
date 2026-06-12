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
# The analytic bridge: directed q-product limits are infinite-product integrals

For any decidable exponent predicate `A : ℕ → Prop`, the truncation integrals
`F ((range (N+1)).filter A)` are antitone and bounded below, and their
infimum equals the integral of the infinite product:

  `sInf (range fun N => F (truncations)) =
     ∫ u in 0..1, ∏' n : {n // A n}, (1 - u ^ n)`.

The proof: pointwise, for `0 ≤ u < 1`, the finite products converge to the
infinite product (multipliability by comparison with the geometric series);
dominated convergence (dominating function `1`) passes the limit through the
integral; antitone bounded sequences converge to their infimum; limits are
unique.

Instances: the prime predicate gives `primeLambda_eq_integral_tprod`, so
every certified enclosure of `primeLambda` is an enclosure of the analytic
constant `∫₀¹ ∏'_p (1 - u^p) du`; the positive-exponent predicate gives the
all-exponents (Sandham) integral, OEIS A258232.
-/

namespace LeanCert.QProduct

open Filter MeasureTheory intervalIntegral Set
open scoped Topology

/-- `qProd S` is continuous. -/
theorem qProd_continuous (S : Finset Nat) : Continuous fun u : ℝ => qProd S u := by
  unfold qProd
  exact continuous_finsetProd S fun n _ => continuous_const.sub (continuous_pow n)

section General

variable (A : ℕ → Prop) [DecidablePred A]

/-- The indicator geometric coefficients of a predicate are summable for
`0 ≤ u < 1`. -/
theorem summable_indicator_pow {u : ℝ} (h0 : 0 ≤ u) (h1 : u < 1) :
    Summable fun n : ℕ => if A n then -(u ^ n) else 0 := by
  have hgeom : Summable fun n : ℕ => u ^ n := summable_geometric_of_lt_one h0 h1
  refine Summable.of_abs (hgeom.of_nonneg_of_le (fun n => abs_nonneg _) fun n => ?_)
  by_cases hn : A n
  · simp [hn, abs_of_nonneg (pow_nonneg h0 n)]
  · simp [hn, pow_nonneg h0 n]

/-- Pointwise convergence of the filtered finite products to the infinite
product, for `0 ≤ u < 1`. -/
theorem qProd_filter_tendsto_tprod {u : ℝ} (h0 : 0 ≤ u) (h1 : u < 1) :
    Tendsto (fun N => qProd ((Finset.range (N + 1)).filter A) u) atTop
      (𝓝 (∏' n : {n : ℕ // A n}, (1 - u ^ (n : ℕ)))) := by
  classical
  set h : ℕ → ℝ := fun n => if A n then 1 - u ^ n else 1 with hh
  have hfh : (fun n : ℕ => 1 + (if A n then -(u ^ n) else 0)) = h := by
    funext n
    by_cases hn : A n <;> simp [hh, hn, sub_eq_add_neg]
  have hM : Multipliable h := by
    rw [← hfh]
    exact Real.multipliable_one_add_of_summable (summable_indicator_pow A h0 h1)
  have htp : ∏' n : ℕ, h n = ∏' n : {n : ℕ // A n}, (1 - u ^ (n : ℕ)) := by
    have hind : h = Set.mulIndicator {n : ℕ | A n} (fun n => 1 - u ^ n) := by
      funext n
      by_cases hn : A n <;> simp [hh, hn, Set.mem_setOf_eq]
    rw [hind, ← tprod_subtype {n : ℕ | A n} (fun n => 1 - u ^ n)]
    rfl
  have hrange : ∀ N, ∏ i ∈ Finset.range (N + 1), h i =
      qProd ((Finset.range (N + 1)).filter A) u := by
    intro N
    unfold qProd
    rw [Finset.prod_filter]
  have htends := hM.hasProd.tendsto_prod_nat
  rw [htp] at htends
  have hshift :
      Tendsto (fun N : ℕ => ∏ i ∈ Finset.range (N + 1), h i) atTop
        (𝓝 (∏' n : {n : ℕ // A n}, (1 - u ^ (n : ℕ)))) :=
    htends.comp (tendsto_add_atTop_nat 1)
  simpa [hrange] using hshift

/-- Dominated convergence: the filtered truncation integrals converge to the
integral of the infinite product. -/
theorem tendsto_F_filter_integral_tprod :
    Tendsto (fun N => F ((Finset.range (N + 1)).filter A)) atTop
      (𝓝 (∫ u in (0:ℝ)..1, ∏' n : {n : ℕ // A n}, (1 - u ^ (n : ℕ)))) := by
  have hF : ∀ N, F ((Finset.range (N + 1)).filter A) =
      ∫ u in Set.Ioc (0:ℝ) 1, qProd ((Finset.range (N + 1)).filter A) u := by
    intro N
    unfold F
    exact integral_of_le (by norm_num)
  have hG : (∫ u in (0:ℝ)..1, ∏' n : {n : ℕ // A n}, (1 - u ^ (n : ℕ))) =
      ∫ u in Set.Ioc (0:ℝ) 1, ∏' n : {n : ℕ // A n}, (1 - u ^ (n : ℕ)) :=
    integral_of_le (by norm_num)
  simp only [hF, hG]
  apply MeasureTheory.tendsto_integral_of_dominated_convergence
    (bound := fun _ : ℝ => (1 : ℝ))
  · exact fun N => ((qProd_continuous _).aestronglyMeasurable).restrict
  · exact MeasureTheory.integrableOn_const measure_Ioc_lt_top.ne
  · intro N
    refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioc).mpr
      (Filter.Eventually.of_forall fun u hu => ?_)
    have hu' : u ∈ Set.Icc (0:ℝ) 1 := ⟨hu.1.le, hu.2⟩
    rw [Real.norm_eq_abs, abs_of_nonneg (qProd_nonneg _ hu')]
    exact qProd_le_one _ hu'
  · have hmem : ∀ᵐ u ∂(volume.restrict (Set.Ioc (0:ℝ) 1)),
        u ∈ Set.Ioc (0:ℝ) 1 := ae_restrict_mem measurableSet_Ioc
    have hne : ∀ᵐ u : ℝ ∂volume, u ≠ (1:ℝ) := by
      have hz : volume ({(1:ℝ)} : Set ℝ) = 0 := measure_singleton _
      have := MeasureTheory.measure_eq_zero_iff_ae_notMem.mp hz
      exact this.mono fun u hu => by simpa using hu
    have hne' : ∀ᵐ u ∂(volume.restrict (Set.Ioc (0:ℝ) 1)), u ≠ (1:ℝ) :=
      hne.filter_mono (MeasureTheory.ae_mono Measure.restrict_le_self)
    filter_upwards [hmem, hne'] with u hu hu1
    exact qProd_filter_tendsto_tprod A hu.1.le (lt_of_le_of_ne hu.2 hu1)

/-- The filtered truncation integrals converge to their infimum. -/
theorem tendsto_F_filter_sInf :
    Tendsto (fun N => F ((Finset.range (N + 1)).filter A)) atTop
      (𝓝 (sInf (Set.range fun N => F ((Finset.range (N + 1)).filter A)))) := by
  have hanti : Antitone fun N => F ((Finset.range (N + 1)).filter A) := by
    intro a b hab
    apply F_antitone
    intro q hq
    simp only [Finset.mem_filter, Finset.mem_range] at hq ⊢
    exact ⟨by omega, hq.2⟩
  have hbdd : BddBelow (Set.range fun N => F ((Finset.range (N + 1)).filter A)) := by
    refine ⟨0, ?_⟩
    rintro x ⟨M, rfl⟩
    exact F_nonneg _
  exact tendsto_atTop_ciInf hanti hbdd

/-- **The analytic bridge, general form**: for any decidable exponent
predicate, the directed limit of the truncation integrals equals the integral
of the infinite product. -/
theorem sInf_F_filter_eq_integral_tprod :
    sInf (Set.range fun N => F ((Finset.range (N + 1)).filter A)) =
      ∫ u in (0:ℝ)..1, ∏' n : {n : ℕ // A n}, (1 - u ^ (n : ℕ)) :=
  tendsto_nhds_unique (tendsto_F_filter_sInf A) (tendsto_F_filter_integral_tprod A)

end General

/-! ### Instance: the prime predicate -/

private theorem primeFRat_cast_eq (N : ℕ) :
    (primeFRat N : ℝ) = F ((Finset.range (N + 1)).filter Nat.Prime) := by
  unfold primeFRat
  rw [finiteIntegralRat_correct]
  rfl

private theorem primeFRat_funext :
    (fun N => (primeFRat N : ℝ)) =
      fun N => F ((Finset.range (N + 1)).filter Nat.Prime) :=
  funext primeFRat_cast_eq

/-- The truncation integrals converge to `primeLambda`. -/
theorem tendsto_primeFRat_primeLambda :
    Tendsto (fun N => (primeFRat N : ℝ)) atTop (𝓝 primeLambda) := by
  unfold primeLambda
  rw [primeFRat_funext]
  exact tendsto_F_filter_sInf Nat.Prime

/-- Dominated convergence for the prime truncations. -/
theorem tendsto_primeFRat_integral_tprod :
    Tendsto (fun N => (primeFRat N : ℝ)) atTop
      (𝓝 (∫ u in (0:ℝ)..1, ∏' p : Nat.Primes, (1 - u ^ (p : ℕ)))) := by
  rw [primeFRat_funext]
  exact tendsto_F_filter_integral_tprod Nat.Prime

/-- **The analytic bridge**: the directed prime limit equals the integral of
the infinite prime product. Every certified enclosure of `primeLambda` is an
enclosure of this analytic constant. -/
theorem primeLambda_eq_integral_tprod :
    primeLambda = ∫ u in (0:ℝ)..1, ∏' p : Nat.Primes, (1 - u ^ (p : ℕ)) :=
  tendsto_nhds_unique tendsto_primeFRat_primeLambda tendsto_primeFRat_integral_tprod

/-! ### Instance: all positive exponents (Sandham's integral, OEIS A258232) -/

private theorem filter_pos_eq_Icc (N : ℕ) :
    (Finset.range (N + 1)).filter (fun n => 0 < n) = Finset.Icc 1 N := by
  ext q
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
  omega

/-- The all-exponents instance of the bridge: the directed limit of
`F {1, …, N}` is Sandham's integral `∫₀¹ ∏_{n ≥ 1} (1 - uⁿ) du`
(OEIS A258232). -/
theorem sInf_F_Icc_eq_integral_tprod :
    sInf (Set.range fun N => F (Finset.Icc 1 N)) =
      ∫ u in (0:ℝ)..1, ∏' n : {n : ℕ // 0 < n}, (1 - u ^ (n : ℕ)) := by
  have h := sInf_F_filter_eq_integral_tprod (fun n => 0 < n)
  simpa [funext fun N => congrArg F (filter_pos_eq_Icc N)] using h

end LeanCert.QProduct
