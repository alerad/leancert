import LeanCert.Analysis.DBN.TimePolynomialApproximation
import LeanCert.Analysis.DBN.RealZeroTimes

/-! A four-point inequality forced by real-only zeros. -/
namespace LeanCert.Analysis.DBN
open Complex Polynomial Set Filter
open scoped Topology

theorem four_point_factor {a : ℝ} (ha : 0 ≤ a) :
    (1+4*a)^6 ≤ (1+9*a)*(1+a)^15 := by
  have he : (1+9*a)*(1+a)^15 - (1+4*a)^6 =
      9*a^16 + 136*a^15 + 960*a^14 + 4200*a^13 + 12740*a^12 +
      28392*a^11 + 48048*a^10 + 62920*a^9 + 64350*a^8 +
      51480*a^7 + 27936*a^6 + 9144*a^5 + 1620*a^4 + 120*a^3 := by ring
  have : 0 ≤ (1+9*a)*(1+a)^15 - (1+4*a)^6 := by rw [he]; positivity
  linarith

theorem four_point_multiset (s : Multiset ℝ) (hs : ∀ a ∈ s, 0 ≤ a) :
    ((s.map (fun a => 1+4*a)).prod)^6 ≤
      (s.map (fun a => 1+9*a)).prod * ((s.map (fun a => 1+a)).prod)^15 := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons a s ih =>
    have ha := hs a (by simp)
    have hs' : ∀ a ∈ s, 0 ≤ a := fun a h => hs a (by simp [h])
    have h := mul_le_mul (four_point_factor ha) (ih hs')
      (pow_nonneg (Multiset.prod_nonneg (by simpa using
        (show ∀ a ∈ s, 0 ≤ 1+4*a from fun a h => by have := hs' a h; positivity))) _)
      (by positivity)
    simpa only [Multiset.map_cons, Multiset.prod_cons, mul_pow, mul_assoc,
      mul_left_comm, mul_comm] using h

private theorem normSq_root_factor (y : ℝ) {r : ℂ} (hr : r.im = 0) :
    normSq (1 - r⁻¹ * ((y : ℂ)*I)) = 1 + y^2 * (r.re⁻¹)^2 := by
  have he : r = (r.re : ℂ) := by simpa [hr] using (Complex.re_add_im r).symm
  rw [he]
  simp [normSq_apply, Complex.mul_re, Complex.mul_im]
  <;> ring

private theorem roots_real (t : ℝ) (ht : t ∈ realZeroTimes) (n : ℕ)
    {r : ℂ} (hr : r ∈ TimeApproximation.HZeroRoots t n) : r.im = 0 := by
  obtain ⟨p, _, rfl⟩ := Multiset.mem_map.mp hr
  apply ht
  by_contra h
  have hd := Complex.Hadamard.divisorZeroIndex₀_val_mem_divisor_support p
  rw [Complex.Hadamard.divisor_univ_eq_analyticOrderNatAt_int (H_entire t)] at hd
  simp [analyticOrderNatAt, ((H_entire t).analyticAt _).analyticOrderAt_eq_zero.mpr h] at hd

private theorem polynomial_normSq (t : ℝ) (ht : t ∈ realZeroTimes) (n : ℕ) (y : ℝ) :
    normSq ((TimeApproximation.HZeroPolynomial t n).eval ((y : ℂ)*I)) =
      normSq (H t 0) *
        ((TimeApproximation.HZeroRoots t n).map (fun r => 1+y^2*(r.re⁻¹)^2)).prod := by
  simp only [TimeApproximation.HZeroPolynomial, eval_mul, eval_C, normSq_mul,
    eval_multiset_prod, Multiset.map_map, Function.comp_def, eval_sub, eval_one,
    eval_mul, eval_C, eval_X, map_multiset_prod]
  congr 1
  apply congrArg Multiset.prod
  apply Multiset.map_congr rfl
  intro r hr
  exact normSq_root_factor y (roots_real t ht n hr)

/-- A necessary inequality at imaginary arguments for a good time. -/
theorem H_four_point_normSq (t : ℝ) (ht : t ∈ realZeroTimes) (y : ℝ) :
    (normSq (H t 0))^10 * (normSq (H t ((2*y : ℝ)*I)))^6 ≤
      normSq (H t ((3*y : ℝ)*I)) * (normSq (H t ((y : ℂ)*I)))^15 := by
  have hp (n : ℕ) :
      (normSq (H t 0))^10 *
          (normSq ((TimeApproximation.HZeroPolynomial t n).eval ((2*y : ℝ)*I)))^6 ≤
      normSq ((TimeApproximation.HZeroPolynomial t n).eval ((3*y : ℝ)*I)) *
          (normSq ((TimeApproximation.HZeroPolynomial t n).eval ((y : ℂ)*I)))^15 := by
    let s := (TimeApproximation.HZeroRoots t n).map (fun r => y^2*(r.re⁻¹)^2)
    have h := four_point_multiset s (by
      intro a ha; obtain ⟨r, _, rfl⟩ := Multiset.mem_map.mp ha; positivity)
    have h' := mul_le_mul_of_nonneg_left h
      (show 0 ≤ (normSq (H t 0))^16 by positivity)
    rw [polynomial_normSq t ht n (2*y), polynomial_normSq t ht n (3*y),
      polynomial_normSq t ht n y]
    simp only [s, Multiset.map_map, Function.comp_def, mul_pow] at h' ⊢
    convert h' using 1 <;> first | rfl | ring_nf
  have hc (w : ℂ) := Complex.continuous_normSq.continuousAt.tendsto.comp
    ((TimeApproximation.HZeroPolynomial_convergence t).tendstoLocallyUniformlyOn.tendsto_at (mem_univ w))
  exact le_of_tendsto_of_tendsto
    (tendsto_const_nhds.mul ((hc _).pow 6))
    ((hc _).mul ((hc _).pow 15)) (Eventually.of_forall hp)

end LeanCert.Analysis.DBN
