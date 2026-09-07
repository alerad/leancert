import LeanCert.Analysis.DBN.CanonicalProduct
import LeanCert.Analysis.DBN.XiIdentity
import Mathlib.Analysis.Calculus.Deriv.Star

/-! Symmetric, multiplicity-preserving polynomial cutoffs of the actual H₀ divisor. -/
namespace LeanCert.Analysis.DBN
open Complex Complex.Hadamard Polynomial Filter Set
open scoped Topology ComplexConjugate

private theorem deriv_conj_symmetric {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hc : ∀ z, f (conj z) = conj (f z)) (z : ℂ) :
    deriv f (conj z) = conj (deriv f z) := by
  have h := (hf z).hasDerivAt.conj_conj
  have he : conj ∘ f ∘ conj = f := by ext w; simp [Function.comp_def, hc]
  rw [he] at h
  exact h.deriv

theorem H_zero_iteratedDeriv_conj (n : ℕ) (z : ℂ) :
    iteratedDeriv n (H 0) (conj z) = conj (iteratedDeriv n (H 0) z) := by
  induction n generalizing z with
  | zero => exact H_conj 0 z
  | succ n ih =>
    rw [iteratedDeriv_succ]
    have hd : ∀ n : ℕ, Differentiable ℂ (iteratedDeriv n (H 0)) := by
      intro n
      induction n with
      | zero => exact H_entire 0
      | succ n ih => rw [iteratedDeriv_succ]; exact ih.deriv
    exact deriv_conj_symmetric (hd n) ih z

theorem H_zero_analyticOrder_conj (z : ℂ) :
    analyticOrderAt (H 0) (conj z) = analyticOrderAt (H 0) z := by
  have hfin := analyticOrderAt_ne_top_of_exists_ne_zero (H_entire 0) ⟨0, H_zero_ne_zero 0⟩ z
  rw [← Nat.cast_analyticOrderNatAt hfin]
  rw [analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero ((H_entire 0).analyticAt _)]
  have h := (analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero
    ((H_entire 0).analyticAt z)).mp (Nat.cast_analyticOrderNatAt hfin).symm
  simpa [H_zero_iteratedDeriv_conj] using h

private theorem H_zero_divisor_neg (z : ℂ) :
    MeromorphicOn.divisor (H 0) univ (-z) = MeromorphicOn.divisor (H 0) univ z := by
  simp only [divisor_univ_eq_analyticOrderNatAt_int (H_entire 0),
    analyticOrderNatAt, H_zero_analyticOrder_neg]

private theorem H_zero_divisor_conj (z : ℂ) :
    MeromorphicOn.divisor (H 0) univ (conj z) = MeromorphicOn.divisor (H 0) univ z := by
  simp only [divisor_univ_eq_analyticOrderNatAt_int (H_entire 0),
    analyticOrderNatAt, H_zero_analyticOrder_conj]

abbrev HZeroIndex := divisorZeroIndex₀ (H 0) univ

private def indexNeg (p : HZeroIndex) : HZeroIndex :=
  ⟨⟨-p.val.1, ⟨p.val.2.val, by simpa only [H_zero_divisor_neg] using p.val.2.isLt⟩⟩,
    neg_ne_zero.mpr p.property⟩

private def indexConj (p : HZeroIndex) : HZeroIndex :=
  ⟨⟨conj p.val.1, ⟨p.val.2.val, by simpa only [H_zero_divisor_conj] using p.val.2.isLt⟩⟩,
    (_root_.map_ne_zero (starRingEnd ℂ)).mpr p.property⟩

private theorem indexNeg_involutive : Function.Involutive indexNeg := by
  rintro ⟨⟨z, k⟩, hz⟩
  apply Subtype.ext
  apply Sigma.ext (neg_neg z)
  exact (Fin.heq_ext_iff (by simp [indexNeg])).mpr rfl

private theorem indexConj_involutive : Function.Involutive indexConj := by
  rintro ⟨⟨z, k⟩, hz⟩
  apply Subtype.ext
  apply Sigma.ext (Complex.conj_conj z)
  exact (Fin.heq_ext_iff (by simp [indexConj])).mpr rfl

/-- All divisor indices of radius at most n, retaining each multiplicity label. -/
noncomputable def HZeroCutoff (n : ℕ) : Finset HZeroIndex :=
  (divisorZeroIndex₀_norm_le_finite (f := H 0) (n : ℝ) (subset_univ _)).toFinset

@[simp] theorem mem_HZeroCutoff (n : ℕ) (p : HZeroIndex) :
    p ∈ HZeroCutoff n ↔ ‖divisorZeroIndex₀_val p‖ ≤ n := by
  simp [HZeroCutoff]

theorem HZeroCutoff_tendsto : Tendsto HZeroCutoff atTop atTop := by
  apply tendsto_atTop.mpr
  intro s
  have h : ∀ p ∈ s, ∀ᶠ n : ℕ in atTop, p ∈ HZeroCutoff n := by
    intro p _
    obtain ⟨n, hn⟩ := exists_nat_ge ‖divisorZeroIndex₀_val p‖
    filter_upwards [eventually_ge_atTop n] with m hm
    exact (mem_HZeroCutoff m p).mpr (hn.trans (by exact_mod_cast hm))
  simpa only [Finset.subset_iff] using (s.eventually_all.mpr h)

private theorem cutoff_map (n : ℕ) (e : HZeroIndex → HZeroIndex)
    (hi : Function.Involutive e)
    (hn : ∀ p, ‖divisorZeroIndex₀_val (e p)‖ = ‖divisorZeroIndex₀_val p‖) :
    (HZeroCutoff n).map ⟨e, hi.injective⟩ = HZeroCutoff n := by
  ext p
  simp only [Finset.mem_map, Function.Embedding.coeFn_mk, mem_HZeroCutoff]
  constructor
  · rintro ⟨q, hq, rfl⟩; rwa [hn]
  · intro hp; exact ⟨e p, by rwa [hn], hi p⟩

noncomputable def HZeroRoots (n : ℕ) : Multiset ℂ :=
  (HZeroCutoff n).val.map divisorZeroIndex₀_val

theorem HZeroRoots_neg (n : ℕ) : (HZeroRoots n).map Neg.neg = HZeroRoots n := by
  have h := congrArg (fun s : Finset HZeroIndex => s.val.map divisorZeroIndex₀_val)
    (cutoff_map n indexNeg indexNeg_involutive (by intro p; exact norm_neg _))
  simpa only [HZeroRoots, Finset.map_val, Multiset.map_map, Function.comp_def,
    Function.Embedding.coeFn_mk, indexNeg] using h

theorem HZeroRoots_conj (n : ℕ) : (HZeroRoots n).map (starRingEnd ℂ) = HZeroRoots n := by
  have h := congrArg (fun s : Finset HZeroIndex => s.val.map divisorZeroIndex₀_val)
    (cutoff_map n indexConj indexConj_involutive (by intro p; exact Complex.norm_conj _))
  simpa only [HZeroRoots, Finset.map_val, Multiset.map_map, Function.comp_def,
    Function.Embedding.coeFn_mk, indexConj] using h

theorem HZeroRoots_ne_zero (n : ℕ) : ∀ r ∈ HZeroRoots n, r ≠ 0 := by
  intro r hr
  obtain ⟨p, _, rfl⟩ := Multiset.mem_map.mp hr
  exact divisorZeroIndex₀_val_ne_zero p

theorem HZeroRoots_strip (n : ℕ) : ∀ r ∈ HZeroRoots n, r.im ^ 2 ≤ 1 := by
  intro r hr
  obtain ⟨p, _, rfl⟩ := Multiset.mem_map.mp hr
  have hz : H 0 (divisorZeroIndex₀_val p) = 0 := by
    by_contra h
    have hd := divisorZeroIndex₀_val_mem_divisor_support p
    rw [divisor_univ_eq_analyticOrderNatAt_int (H_entire 0)] at hd
    simp [analyticOrderNatAt, ((H_entire 0).analyticAt _).analyticOrderAt_eq_zero.mpr h] at hd
  have h := H_zero_strip hz
  have := (abs_le.mp h)
  nlinarith

noncomputable def HZeroPolynomial (n : ℕ) : ℂ[X] :=
  C (H 0 0) * ((HZeroRoots n).map (fun r => (1 : ℂ[X]) - C r⁻¹ * X)).prod

@[simp] theorem HZeroPolynomial_at_zero (n : ℕ) : (HZeroPolynomial n).eval 0 = H 0 0 := by
  simp [HZeroPolynomial, finite_rootPolynomial_at_zero]

theorem HZeroPolynomial_ne_zero (n : ℕ) : HZeroPolynomial n ≠ 0 := by
  intro h
  have he := HZeroPolynomial_at_zero n
  rw [h, eval_zero] at he
  exact H_zero_ne_zero 0 he.symm

theorem HZeroPolynomial_conj (n : ℕ) :
    (HZeroPolynomial n).map (starRingEnd ℂ) = HZeroPolynomial n := by
  have hc : conj (H 0 0) = H 0 0 := by simpa using (H_conj 0 0).symm
  simp only [HZeroPolynomial, Polynomial.map_mul, Polynomial.map_C, hc,
    finite_rootPolynomial_conj _ (HZeroRoots_conj n)]

theorem HZeroPolynomial_strip (n : ℕ) (z : ℂ) (hz : (HZeroPolynomial n).eval z = 0) :
    z.im ^ 2 ≤ 1 := by
  simp only [HZeroPolynomial, eval_mul, eval_C] at hz
  have h := finite_rootPolynomial_strip _ (HZeroRoots_ne_zero n) (b := 1)
    (by simpa using HZeroRoots_strip n) ((mul_eq_zero.mp hz).resolve_left (H_zero_ne_zero 0))
  simpa using h

theorem HZeroPolynomial_eq_product (n : ℕ) (z : ℂ) :
    (HZeroPolynomial n).eval z = H 0 0 * ∏ p ∈ HZeroCutoff n,
      weierstrassFactor 1 (z / divisorZeroIndex₀_val p) := by
  rw [HZeroPolynomial, eval_mul, eval_C,
    ← balanced_canonicalProduct_eq_polynomial _ (HZeroRoots_neg n)]
  simp only [HZeroRoots, Multiset.map_map, Function.comp_def, Finset.prod]

/-- Genuine real polynomials, with unit-strip roots, converge locally uniformly to H₀. -/
theorem HZeroPolynomial_convergence :
    TendstoLocallyUniformly (fun n z => (HZeroPolynomial n).eval z) (H 0) atTop := by
  have hnet := tendstoLocallyUniformlyOn_univ.mp H_zero_canonicalProduct_convergence
  have hseq : TendstoLocallyUniformly
      (fun n z => ∏ p ∈ HZeroCutoff n, weierstrassFactor 1 (z / divisorZeroIndex₀_val p))
      (divisorCanonicalProduct 1 (H 0) univ) atTop := by
    intro u hu z
    obtain ⟨t, ht, he⟩ := hnet u hu z
    exact ⟨t, ht, HZeroCutoff_tendsto.eventually he⟩
  have hu : UniformContinuous (fun w : ℂ => H 0 0 * w) :=
    (ContinuousLinearMap.mul ℂ ℂ (H 0 0)).uniformContinuous
  have hm := hu.comp_tendstoLocallyUniformly hseq
  simpa only [Function.comp_def, ← HZeroPolynomial_eq_product,
    ← H_zero_eq_normalized_canonicalProduct] using hm

end LeanCert.Analysis.DBN
