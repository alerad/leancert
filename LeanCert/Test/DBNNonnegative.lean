import LeanCert.Analysis.DBN.DobnerLimit
import Mathlib.Util.AssertNoSorry

open LeanCert.Analysis LeanCert.Analysis.DBN Complex

-- The final theorem has no approximation, certificate, or asymptotic premise.
example : 0 ≤ Lambda := Lambda_nonneg
example : Lambda ∈ Set.Icc (0 : ℝ) (1/2) := ⟨Lambda_nonneg, Lambda_le_half⟩

-- Negative times have a nonreal zero of the existing actual heat integral.
example {t : ℝ} (ht : t < 0) : ∃ z : ℂ, H t z = 0 ∧ z.im ≠ 0 :=
  nonreal_zero_of_lt_Lambda (lt_of_lt_of_le ht Lambda_nonneg)

-- The approximation is proved for every positive damping, not supplied by callers.
example (a : ℝ) (ha : 0 < a) : NormalizedHeatApproximation a :=
  normalizedHeatApproximation ha

-- One height threshold and one constant work for all indices and the full contour.
example (a M : ℝ) (ha : 0 < a) (hM : 0 ≤ M) :
    ∃ C Y : ℝ, 0 < C ∧ 0 < Y ∧ ∀ s : ℂ, |s.re| ≤ M → Y ≤ s.im →
      ∀ L v : ℝ, 0 ≤ L → ‖centeredKernel a s L v‖ ≤
        C*Real.exp (-a*L^2/4)*Real.exp (-v^2/(32*a)) :=
  centeredKernel_joint_majorant ha hM

assert_no_sorry real_Gamma_le_exp_sq
assert_no_sorry norm_xiGamma_le_exp_sq
assert_no_sorry norm_xiGamma_linearRatio_le
assert_no_sorry centeredKernel_coarse_bound
assert_no_sorry centeredKernel_joint_majorant
assert_no_sorry normalizedContourTerm_tendsto
assert_no_sorry normalizedHeat_sub_series_tendsto
assert_no_sorry normalizedHeatApproximation
assert_no_sorry Lambda_nonneg
