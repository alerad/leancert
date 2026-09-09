import LeanCert.Analysis.DBN.CanonicalProduct
import LeanCert.Analysis.DBN.XiIdentity
import Mathlib.Analysis.Calculus.Deriv.Star

/-! Symmetric polynomial cutoffs of the heat integral at arbitrary real time. -/
namespace LeanCert.Analysis.DBN.TimeApproximation
variable (t : ℝ)
open Complex Complex.Hadamard Polynomial Filter Set
open scoped Topology ComplexConjugate

private theorem deriv_conj_symmetric {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hc : ∀ z, f (conj z) = conj (f z)) (z : ℂ) :
    deriv f (conj z) = conj (deriv f z) := by
  have h := (hf z).hasDerivAt.conj_conj
  have he : conj ∘ f ∘ conj = f := by ext w; simp [Function.comp_def, hc]
  rw [he] at h
  exact h.deriv

theorem H_iteratedDeriv_conj (n : ℕ) (z : ℂ) :
    iteratedDeriv n (H t) (conj z) = conj (iteratedDeriv n (H t) z) := by
  induction n generalizing z with
  | zero => exact H_conj t z
  | succ n ih =>
    rw [iteratedDeriv_succ]
    have hd : ∀ n : ℕ, Differentiable ℂ (iteratedDeriv n (H t)) := by
      intro n
      induction n with
      | zero => exact H_entire t
      | succ n ih => rw [iteratedDeriv_succ]; exact ih.deriv
    exact deriv_conj_symmetric (hd n) ih z

theorem H_analyticOrder_conj (z : ℂ) :
    analyticOrderAt (H t) (conj z) = analyticOrderAt (H t) z := by
  have hfin := analyticOrderAt_ne_top_of_exists_ne_zero (H_entire t) ⟨0, H_zero_ne_zero t⟩ z
  rw [← Nat.cast_analyticOrderNatAt hfin]
  rw [analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero ((H_entire t).analyticAt _)]
  have h := (analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero
    ((H_entire t).analyticAt z)).mp (Nat.cast_analyticOrderNatAt hfin).symm
  simpa [(H_iteratedDeriv_conj t)] using h

theorem H_analyticOrder_neg (z : ℂ) :
    analyticOrderAt (H t) (-z) = analyticOrderAt (H t) z := by
  have h := analyticOrderAt_comp_of_deriv_ne_zero (f := H t) (g := fun w : ℂ => -w)
    (z₀ := z) (by fun_prop) (by simp)
  have he : (H t ∘ fun w : ℂ => -w) = H t := funext (H_even t)
  rw [he] at h
  exact h.symm

private theorem H_divisor_neg (z : ℂ) :
    MeromorphicOn.divisor (H t) univ (-z) = MeromorphicOn.divisor (H t) univ z := by
  simp only [divisor_univ_eq_analyticOrderNatAt_int (H_entire t),
    analyticOrderNatAt, (H_analyticOrder_neg t)]

private theorem H_divisor_conj (z : ℂ) :
    MeromorphicOn.divisor (H t) univ (conj z) = MeromorphicOn.divisor (H t) univ z := by
  simp only [divisor_univ_eq_analyticOrderNatAt_int (H_entire t),
    analyticOrderNatAt, (H_analyticOrder_conj t)]

abbrev HZeroIndex := divisorZeroIndex₀ (H t) univ

private def indexNeg (p : (HZeroIndex t)) : (HZeroIndex t) :=
  ⟨⟨-p.val.1, ⟨p.val.2.val, by simpa only [(H_divisor_neg t)] using p.val.2.isLt⟩⟩,
    neg_ne_zero.mpr p.property⟩

private def indexConj (p : (HZeroIndex t)) : (HZeroIndex t) :=
  ⟨⟨conj p.val.1, ⟨p.val.2.val, by simpa only [(H_divisor_conj t)] using p.val.2.isLt⟩⟩,
    (_root_.map_ne_zero (starRingEnd ℂ)).mpr p.property⟩

private theorem indexNeg_involutive : Function.Involutive (indexNeg t) := by
  rintro ⟨⟨z, k⟩, hz⟩
  apply Subtype.ext
  apply Sigma.ext (neg_neg z)
  exact (Fin.heq_ext_iff (by simp [indexNeg])).mpr rfl

private theorem indexConj_involutive : Function.Involutive (indexConj t) := by
  rintro ⟨⟨z, k⟩, hz⟩
  apply Subtype.ext
  apply Sigma.ext (Complex.conj_conj z)
  exact (Fin.heq_ext_iff (by simp [indexConj])).mpr rfl

/-- All divisor indices of radius at most n, retaining each multiplicity label. -/
noncomputable def HZeroCutoff (n : ℕ) : Finset (HZeroIndex t) :=
  (divisorZeroIndex₀_norm_le_finite (f := H t) (n : ℝ) (subset_univ _)).toFinset

@[simp] theorem mem_HZeroCutoff (n : ℕ) (p : (HZeroIndex t)) :
    p ∈ (HZeroCutoff t) n ↔ ‖divisorZeroIndex₀_val p‖ ≤ n := by
  simp [HZeroCutoff]

theorem HZeroCutoff_tendsto : Tendsto (HZeroCutoff t) atTop atTop := by
  apply tendsto_atTop.mpr
  intro s
  have h : ∀ p ∈ s, ∀ᶠ n : ℕ in atTop, p ∈ (HZeroCutoff t) n := by
    intro p _
    obtain ⟨n, hn⟩ := exists_nat_ge ‖divisorZeroIndex₀_val p‖
    filter_upwards [eventually_ge_atTop n] with m hm
    exact ((mem_HZeroCutoff t) m p).mpr (hn.trans (by exact_mod_cast hm))
  simpa only [Finset.subset_iff] using (s.eventually_all.mpr h)

private theorem cutoff_map (n : ℕ) (e : (HZeroIndex t) → (HZeroIndex t))
    (hi : Function.Involutive e)
    (hn : ∀ p, ‖divisorZeroIndex₀_val (e p)‖ = ‖divisorZeroIndex₀_val p‖) :
    ((HZeroCutoff t) n).map ⟨e, hi.injective⟩ = (HZeroCutoff t) n := by
  ext p
  simp only [Finset.mem_map, Function.Embedding.coeFn_mk, (mem_HZeroCutoff t)]
  constructor
  · rintro ⟨q, hq, rfl⟩; rwa [hn]
  · intro hp; exact ⟨e p, by rwa [hn], hi p⟩

noncomputable def HZeroRoots (n : ℕ) : Multiset ℂ :=
  ((HZeroCutoff t) n).val.map divisorZeroIndex₀_val

theorem HZeroRoots_neg (n : ℕ) : ((HZeroRoots t) n).map Neg.neg = (HZeroRoots t) n := by
  have h := congrArg (fun s : Finset (HZeroIndex t) => s.val.map divisorZeroIndex₀_val)
    ((cutoff_map t) n (indexNeg t) (indexNeg_involutive t) (by intro p; exact norm_neg _))
  simpa only [HZeroRoots, Finset.map_val, Multiset.map_map, Function.comp_def,
    Function.Embedding.coeFn_mk, indexNeg] using h

theorem HZeroRoots_conj (n : ℕ) : ((HZeroRoots t) n).map (starRingEnd ℂ) = (HZeroRoots t) n := by
  have h := congrArg (fun s : Finset (HZeroIndex t) => s.val.map divisorZeroIndex₀_val)
    ((cutoff_map t) n (indexConj t) (indexConj_involutive t) (by intro p; exact Complex.norm_conj _))
  simpa only [HZeroRoots, Finset.map_val, Multiset.map_map, Function.comp_def,
    Function.Embedding.coeFn_mk, indexConj] using h

theorem HZeroRoots_ne_zero (n : ℕ) : ∀ r ∈ (HZeroRoots t) n, r ≠ 0 := by
  intro r hr
  obtain ⟨p, _, rfl⟩ := Multiset.mem_map.mp hr
  exact divisorZeroIndex₀_val_ne_zero p

theorem HZeroRoots_strip {b : ℝ} (hstrip : ∀ z, H t z = 0 → z.im ^ 2 ≤ b^2) (n : ℕ) : ∀ r ∈ (HZeroRoots t) n, r.im ^ 2 ≤ b^2 := by
  intro r hr
  obtain ⟨p, _, rfl⟩ := Multiset.mem_map.mp hr
  have hz : H t (divisorZeroIndex₀_val p) = 0 := by
    by_contra h
    have hd := divisorZeroIndex₀_val_mem_divisor_support p
    rw [divisor_univ_eq_analyticOrderNatAt_int (H_entire t)] at hd
    simp [analyticOrderNatAt, ((H_entire t).analyticAt _).analyticOrderAt_eq_zero.mpr h] at hd
  exact hstrip _ hz

noncomputable def HZeroPolynomial (n : ℕ) : ℂ[X] :=
  C (H t 0) * (((HZeroRoots t) n).map (fun r => (1 : ℂ[X]) - C r⁻¹ * X)).prod

@[simp] theorem HZeroPolynomial_at_zero (n : ℕ) : ((HZeroPolynomial t) n).eval 0 = H t 0 := by
  simp [HZeroPolynomial, finite_rootPolynomial_at_zero]

theorem HZeroPolynomial_ne_zero (n : ℕ) : (HZeroPolynomial t) n ≠ 0 := by
  intro h
  have he := (HZeroPolynomial_at_zero t) n
  rw [h, eval_zero] at he
  exact H_zero_ne_zero t he.symm

theorem HZeroPolynomial_conj (n : ℕ) :
    ((HZeroPolynomial t) n).map (starRingEnd ℂ) = (HZeroPolynomial t) n := by
  have hc : conj (H t 0) = H t 0 := by simpa using (H_conj t 0).symm
  simp only [HZeroPolynomial, Polynomial.map_mul, Polynomial.map_C, hc,
    finite_rootPolynomial_conj _ ((HZeroRoots_conj t) n)]

theorem HZeroPolynomial_strip {b : ℝ} (hstrip : ∀ z, H t z = 0 → z.im ^ 2 ≤ b^2) (n : ℕ) (z : ℂ) (hz : ((HZeroPolynomial t) n).eval z = 0) :
    z.im ^ 2 ≤ b^2 := by
  simp only [HZeroPolynomial, eval_mul, eval_C] at hz
  have h := finite_rootPolynomial_strip _ ((HZeroRoots_ne_zero t) n) (b := b)
    (by simpa using (HZeroRoots_strip t) hstrip n) ((mul_eq_zero.mp hz).resolve_left (H_zero_ne_zero t))
  simpa using h

theorem HZeroPolynomial_eq_product (n : ℕ) (z : ℂ) :
    ((HZeroPolynomial t) n).eval z = H t 0 * ∏ p ∈ (HZeroCutoff t) n,
      weierstrassFactor 1 (z / divisorZeroIndex₀_val p) := by
  rw [HZeroPolynomial, eval_mul, eval_C,
    ← balanced_canonicalProduct_eq_polynomial _ ((HZeroRoots_neg t) n)]
  simp only [HZeroRoots, Multiset.map_map, Function.comp_def, Finset.prod]

/-- Genuine real polynomials converge locally uniformly to the heat integral at any real time. -/
theorem HZeroPolynomial_convergence :
    TendstoLocallyUniformly (fun n z => ((HZeroPolynomial t) n).eval z) (H t) atTop := by
  have hnet := tendstoLocallyUniformlyOn_univ.mp (H_canonicalProduct_convergence t)
  have hseq : TendstoLocallyUniformly
      (fun n z => ∏ p ∈ (HZeroCutoff t) n, weierstrassFactor 1 (z / divisorZeroIndex₀_val p))
      (divisorCanonicalProduct 1 (H t) univ) atTop := by
    intro u hu z
    obtain ⟨v, ht, he⟩ := hnet u hu z
    exact ⟨v, ht, (HZeroCutoff_tendsto t).eventually he⟩
  have hu : UniformContinuous (fun w : ℂ => H t 0 * w) :=
    (ContinuousLinearMap.mul ℂ ℂ (H t 0)).uniformContinuous
  have hm := hu.comp_tendstoLocallyUniformly hseq
  simpa only [Function.comp_def, ← (HZeroPolynomial_eq_product t),
    ← H_eq_normalized_canonicalProduct] using hm

end LeanCert.Analysis.DBN.TimeApproximation
