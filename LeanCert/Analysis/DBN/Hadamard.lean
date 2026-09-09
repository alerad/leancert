import LeanCert.Analysis.DBN.HeatGrowth
import LeanCert.Analysis.HadamardSupport.Analysis.Complex.HadamardFactorization.Order

/-! Hadamard factorization instantiated for the actual H_t at every real time, not an assumed xi model.
Symmetric polynomial cutoffs and strip-preserving approximation are still separate. -/
namespace LeanCert.Analysis.DBN
open Complex Complex.Hadamard

private theorem floor_three_halves : Nat.floor (3/2 : ℝ) = 1 := by
  rw [Nat.floor_eq_iff (by norm_num)]
  norm_num

theorem H_order (t : ℝ) : EntireOfOrderAtMost (3/2) (H t) :=
  EntireOfOrderAtMost.of_norm_le_exp (H_entire t) (H_norm_le_exp_order t)

theorem H_hadamard (t : ℝ) : ∃ P : Polynomial ℂ, P.degree ≤ 1 ∧ ∀ z : ℂ,
    H t z = Complex.exp (P.eval z) *
      divisorCanonicalProduct 1 (H t) Set.univ z := by
  have h := hadamard_factorization_of_order (by norm_num : (0 : ℝ) ≤ 3/2)
    ⟨0, H_zero_ne_zero t⟩ (H_order t)
  have ho : analyticOrderNatAt (H t) 0 = 0 := by
    simp only [analyticOrderNatAt, ((H_entire t).analyticAt 0).analyticOrderAt_eq_zero.mpr (H_zero_ne_zero t), ENat.toNat_zero]
  simpa only [floor_three_halves, Nat.cast_one, ho, pow_zero, mul_one] using h

theorem H_inverse_square_summable (t : ℝ) :
    Summable (fun p : divisorZeroIndex₀ (H t) Set.univ => ‖divisorZeroIndex₀_val p‖⁻¹ ^ 2) := by
  have h := (H_order t).summable_norm_inv_pow_divisorZeroIndex₀
    (by norm_num : (0 : ℝ) ≤ 3/2) ⟨0, H_zero_ne_zero t⟩
  simpa only [floor_three_halves, Nat.reduceAdd] using h

/-- Locally uniform canonical-product convergence, before selecting symmetric cutoffs. -/
theorem H_canonicalProduct_convergence (t : ℝ) :
    HasProdLocallyUniformlyOn
      (fun (p : divisorZeroIndex₀ (H t) Set.univ) (z : ℂ) =>
        weierstrassFactor 1 (z / divisorZeroIndex₀_val p))
      (divisorCanonicalProduct 1 (H t) Set.univ) Set.univ :=
  hasProdLocallyUniformlyOn_divisorCanonicalProduct_univ 1 (H t) (H_inverse_square_summable t)

theorem H_zero_order : EntireOfOrderAtMost (3/2) (H 0) := H_order 0

theorem H_zero_hadamard : ∃ P : Polynomial ℂ, P.degree ≤ 1 ∧ ∀ z : ℂ,
    H 0 z = Complex.exp (P.eval z) *
      divisorCanonicalProduct 1 (H 0) Set.univ z := H_hadamard 0

theorem H_zero_inverse_square_summable :
    Summable (fun p : divisorZeroIndex₀ (H 0) Set.univ => ‖divisorZeroIndex₀_val p‖⁻¹ ^ 2) :=
  H_inverse_square_summable 0

theorem H_zero_canonicalProduct_convergence :
    HasProdLocallyUniformlyOn
      (fun (p : divisorZeroIndex₀ (H 0) Set.univ) (z : ℂ) =>
        weierstrassFactor 1 (z / divisorZeroIndex₀_val p))
      (divisorCanonicalProduct 1 (H 0) Set.univ) Set.univ :=
  H_canonicalProduct_convergence 0

end LeanCert.Analysis.DBN
