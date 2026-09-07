import LeanCert.Analysis.DBN.Hadamard
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.Tactic

/-! Removing the exponential prefactor from the actual H_0 factorization. -/
namespace LeanCert.Analysis.DBN
open Complex Complex.Hadamard Polynomial

/-- Every genus-one factor is normalized to have derivative zero at the origin. -/
theorem H_zero_canonicalProduct_deriv_zero :
    deriv (divisorCanonicalProduct 1 (H 0) Set.univ) 0 = 0 := by
  have h := logDeriv_divisorCanonicalProduct_one_eq_tsum H_zero_inverse_square_summable
    (z := 0) (fun p => (divisorZeroIndex₀_val_ne_zero p).symm)
    (divisorCanonicalProduct_ne_zero_at_zero 1 (H 0) Set.univ)
  simpa [logDeriv] using h

theorem H_zero_deriv_zero : deriv (H 0) 0 = 0 := by
  have hd := ((H_entire 0 (-(0 : ℂ))).hasDerivAt).comp (h := fun z : ℂ => -z) 0 (hasDerivAt_neg (0 : ℂ))
  have he : (fun z : ℂ => H 0 (-z)) = H 0 := funext (H_even 0)
  simp only [Function.comp_def] at hd
  rw [he] at hd
  have h := hd.unique ((H_entire 0 (0 : ℂ)).hasDerivAt)
  simp only [neg_zero, mul_neg, mul_one] at h
  linear_combination -h / 2

/-- The entire linear exponential prefactor is constant, not merely nonvanishing. -/
theorem H_zero_eq_normalized_canonicalProduct (z : ℂ) :
    H 0 z = H 0 0 * divisorCanonicalProduct 1 (H 0) Set.univ z := by
  obtain ⟨P, hP, hfac⟩ := H_zero_hadamard
  obtain ⟨a, b, rfl⟩ := P.exists_eq_X_add_C_of_natDegree_le_one (natDegree_le_of_degree_le hP)
  simp only [eval_add, eval_mul, eval_C, eval_X] at hfac
  have hQ := differentiable_divisorCanonicalProduct_univ 1 (H 0) H_zero_inverse_square_summable
  have hder := (((hasDerivAt_id (0 : ℂ)).const_mul a).add_const b).cexp.mul ((hQ 0).hasDerivAt)
  have he : (fun z : ℂ => Complex.exp (a*z+b) * divisorCanonicalProduct 1 (H 0) Set.univ z) = H 0 :=
    funext (fun z => (hfac z).symm)
  simp only [Pi.mul_def, id_eq] at hder
  rw [he] at hder
  have hd := hder.deriv
  rw [H_zero_deriv_zero] at hd
  simp only [H_zero_canonicalProduct_deriv_zero, divisorCanonicalProduct_zero, mul_zero,
    zero_add, mul_one, add_zero] at hd
  have ha : a = 0 := (mul_eq_zero.mp hd.symm).resolve_left (Complex.exp_ne_zero b)
  have h0 := hfac 0
  simp only [mul_zero, zero_add, divisorCanonicalProduct_zero, mul_one] at h0
  simpa only [ha, zero_mul, zero_add, ← h0] using hfac z

/-- The canonical product inherits evenness once its prefactor is removed. -/
theorem H_zero_canonicalProduct_even (z : ℂ) :
    divisorCanonicalProduct 1 (H 0) Set.univ (-z) =
      divisorCanonicalProduct 1 (H 0) Set.univ z := by
  apply mul_left_cancel₀ (H_zero_ne_zero 0)
  rw [← H_zero_eq_normalized_canonicalProduct, ← H_zero_eq_normalized_canonicalProduct, H_even]

/-- A negation-invariant finite root multiset has zero reciprocal sum. -/
theorem reciprocal_sum_eq_zero (roots : Multiset ℂ)
    (hn : roots.map Neg.neg = roots) : (roots.map (fun r => r⁻¹)).sum = 0 := by
  have h := congrArg (fun s : Multiset ℂ => (s.map (fun r => r⁻¹)).sum) hn
  simp only [Multiset.map_map, Function.comp_def, inv_neg, Multiset.sum_map_neg] at h
  linear_combination -h / 2

/-- Finite canonical products over balanced roots are genuine polynomials. -/
theorem balanced_canonicalProduct_eq_polynomial (roots : Multiset ℂ)
    (hn : roots.map Neg.neg = roots) (z : ℂ) :
    (roots.map (fun r => weierstrassFactor 1 (z/r))).prod =
      (roots.map (fun r => (1 : ℂ[X]) - C r⁻¹ * X)).prod.eval z := by
  have hw (w : ℂ) : weierstrassFactor 1 w = (1-w)*Complex.exp w := by
    simp [weierstrassFactor, partialLogSum_succ]
  simp only [hw, Multiset.prod_map_mul]
  have he : (roots.map (fun r => Complex.exp (z/r))).prod = 1 := by
    rw [show roots.map (fun r => Complex.exp (z/r)) =
      (roots.map (fun r => z/r)).map Complex.exp by rw [Multiset.map_map]; rfl,
      ← Complex.exp_multiset_sum]
    have hs : (roots.map (fun r => z/r)).sum = z*(roots.map (fun r => r⁻¹)).sum := by
      simp only [div_eq_mul_inv, Multiset.sum_map_mul_left]
    rw [hs, reciprocal_sum_eq_zero roots hn, mul_zero, Complex.exp_zero]
  rw [he, mul_one]
  simp only [eval_multiset_prod, Multiset.map_map, Function.comp_def, eval_sub, eval_one,
    eval_mul, eval_C, eval_X, div_eq_mul_inv, mul_comm]

/-- The actual zero multiplicities agree at opposite points. -/
theorem H_zero_analyticOrder_neg (z : ℂ) :
    analyticOrderAt (H 0) (-z) = analyticOrderAt (H 0) z := by
  have h := analyticOrderAt_comp_of_deriv_ne_zero (f := H 0) (g := fun w : ℂ => -w)
    (z₀ := z) (by fun_prop) (by simp)
  have he : (H 0 ∘ fun w : ℂ => -w) = H 0 := funext (H_even 0)
  rw [he] at h
  exact h.symm

/-- Normalized finite root polynomials have no spurious zeros. -/
theorem finite_rootPolynomial_zero_iff (roots : Multiset ℂ)
    (hr : ∀ r ∈ roots, r ≠ 0) (z : ℂ) :
    (roots.map (fun r => (1 : ℂ[X]) - C r⁻¹ * X)).prod.eval z = 0 ↔ z ∈ roots := by
  simp only [eval_multiset_prod, Multiset.map_map, Function.comp_def, eval_sub, eval_one,
    eval_mul, eval_C, eval_X, Multiset.prod_eq_zero_iff, Multiset.mem_map]
  constructor
  · rintro ⟨r, hmem, he⟩
    have hmul : r⁻¹*z = 1 := by linear_combination -he
    have hz : z = r := by
      have h := congrArg (fun w : ℂ => r*w) hmul
      simpa [← mul_assoc, hr r hmem] using h
    simpa [hz] using hmem
  · intro hz
    exact ⟨z, hz, by simp [hr z hz]⟩

/-- Conjugation-balanced finite roots yield real coefficients. -/
theorem finite_rootPolynomial_conj (roots : Multiset ℂ)
    (hc : roots.map (starRingEnd ℂ) = roots) :
    ((roots.map (fun r => (1 : ℂ[X]) - C r⁻¹ * X)).prod).map (starRingEnd ℂ) =
      (roots.map (fun r => (1 : ℂ[X]) - C r⁻¹ * X)).prod := by
  have h := congrArg (fun s : Multiset ℂ => (s.map (fun r => (1 : ℂ[X]) - C r⁻¹ * X)).prod) hc
  simpa only [Polynomial.map_multiset_prod, Multiset.map_map, Function.comp_def, Polynomial.map_sub,
    Polynomial.map_one, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X, map_inv₀] using h

/-- Finite root polynomials are normalized at zero, including the empty cutoff. -/
theorem finite_rootPolynomial_at_zero (roots : Multiset ℂ) :
    (roots.map (fun r => (1 : ℂ[X]) - C r⁻¹ * X)).prod.eval 0 = 1 := by
  simp [eval_multiset_prod]

/-- Zero-strip control transfers to the finite root polynomial without slack. -/
theorem finite_rootPolynomial_strip (roots : Multiset ℂ)
    (hr : ∀ r ∈ roots, r ≠ 0) {b : ℝ}
    (hb : ∀ r ∈ roots, r.im^2 ≤ b^2) {z : ℂ}
    (hz : (roots.map (fun r => (1 : ℂ[X]) - C r⁻¹ * X)).prod.eval z = 0) :
    z.im^2 ≤ b^2 := hb z ((finite_rootPolynomial_zero_iff roots hr z).mp hz)

end LeanCert.Analysis.DBN
