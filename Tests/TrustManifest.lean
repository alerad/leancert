/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert
import LeanCert.Examples.EulerMascheroniBounds

/-!
# Trust manifest for exported declarations

`#assert_trust` pins for the representative public surface. This complements
`Tests/AxiomAudit.lean`:

* AxiomAudit pins *exact axiom sets* for golden theorems and sweeps the whole
  library for illegally minted axioms;
* this manifest classifies exported results by *trust class* and fails on
  drift in **either** direction — a kernel-clean theorem acquiring compiler
  trust is a regression, and a native-pinned theorem losing its native
  dependency means the pin should be tightened to `kernel`.

CI runs this file in the soundness-guard workflow (after AxiomAudit).
When exporting a new headline result, add its pin here.
-/

/-! ## Golden theorems: kernel-clean by construction

The lifts from Boolean certificates to semantic propositions must never
depend on compiler trust — every proof produced by any trust mode reuses
them unchanged. -/

#assert_trust kernel LeanCert.Validity.verify_upper_bound
#assert_trust kernel LeanCert.Validity.verify_lower_bound
#assert_trust kernel LeanCert.Validity.verify_strict_upper_bound
#assert_trust kernel LeanCert.Validity.verify_strict_lower_bound
#assert_trust kernel LeanCert.Validity.verify_upper_bound_dyadic_checked
#assert_trust kernel LeanCert.Validity.verify_lower_bound_dyadic_checked
#assert_trust kernel LeanCert.Validity.Integration.verify_integral_bound
#assert_trust kernel LeanCert.Engine.verify_finsum_upper_full
#assert_trust kernel LeanCert.Engine.verify_finsum_lower_full
#assert_trust kernel LeanCert.API.Bounds.verifyUpperBoundBox

/-! ## DBN endpoint: unconditional analytic theorem, no native evaluation -/

#assert_trust kernel LeanCert.Analysis.DBN.H_norm_le_exp_order
#assert_trust kernel LeanCert.Analysis.DBN.H_hadamard
#assert_trust kernel LeanCert.Analysis.DBN.H_eq_normalized_canonicalProduct
#assert_trust kernel LeanCert.Analysis.DBN.StripPolynomialApproximation.heat_limit_strip
#assert_trust kernel LeanCert.Analysis.DBN.StripPolynomialApproximation.heat_limit_real
#assert_trust kernel LeanCert.Analysis.DBN.isClosed_realZeroTimes
#assert_trust kernel LeanCert.Analysis.DBN.realZeroTimes_eq_Ici
#assert_trust kernel LeanCert.Analysis.DBN.H_half_real_zeros
#assert_trust kernel LeanCert.Analysis.DBN.H_half_ne_zero_of_im_ne_zero
#assert_trust kernel LeanCert.API.Bounds.verifyLowerBoundBox

/-! ## Euler–Mascheroni bounds: intentionally native-trusted

Verified by an inline `native_decide` over a `2^20`-term reflective harmonic
sum — the scale at which native evaluation earns its trust cost (see the
calibration in `scripts/bench-trust/README.md`). If these ever stop
depending on native trust, the pins below fail and should be tightened to
`kernel` (and celebrated). -/

#assert_trust native EulerMascheroni.gamma_lower
#assert_trust native EulerMascheroni.gamma_upper
#assert_trust native EulerMascheroni.gamma_bounds
#assert_trust native EulerMascheroni.gamma_approx

#assert_trust kernel LeanCert.Analysis.DBN.timeShift_convergence
#assert_trust kernel LeanCert.Analysis.DBN.H_forward_strip
#assert_trust kernel LeanCert.Analysis.DBN.realZeroTimes_forward
#assert_trust kernel LeanCert.Analysis.DBN.H_real_zeros_of_half_le

/-! ## Classical DBN threshold: unconditional and kernel-trusted -/

#assert_trust kernel LeanCert.Analysis.DBN.Phi_four_point_obstruction
#assert_trust kernel LeanCert.Analysis.DBN.H_four_point_normSq
#assert_trust kernel LeanCert.Analysis.DBN.gaussianAverage_tendsto
#assert_trust kernel LeanCert.Analysis.DBN.exists_bad_negative_square
#assert_trust kernel LeanCert.Analysis.DBN.realZeroTimes_bddBelow
#assert_trust kernel LeanCert.Analysis.DBN.real_zeros_iff_Lambda_le
#assert_trust kernel LeanCert.Analysis.DBN.Lambda_le_half
#assert_trust kernel LeanCert.Analysis.DBN.dbn_certificate

/-! ## Phase 1: Gaussian Dirichlet series (not yet the DBN lower bound) -/

#assert_trust kernel LeanCert.Analysis.DirichletGaussian.entire_series
#assert_trust kernel LeanCert.Analysis.DirichletGaussian.growth_bound
#assert_trust kernel LeanCert.Analysis.DirichletGaussian.exists_zero
#assert_trust kernel LeanCert.Analysis.DirichletGaussian.negative_time_exists_zero
#assert_trust kernel LeanCert.Engine.DirichletGaussian.checkTail_sound
#assert_trust kernel LeanCert.Engine.DirichletGaussian.certified_tail
#assert_trust kernel LeanCert.Engine.DirichletGaussian.certified_disk

/-! ## Phase 2 components: approximation remains unproved -/

#assert_trust kernel LeanCert.Analysis.DirichletGaussian.exists_phase_returns
#assert_trust kernel LeanCert.Analysis.DirichletGaussian.exists_vertical_recurrence
#assert_trust kernel LeanCert.Analysis.DirichletGaussian.zeros_at_arbitrary_height
#assert_trust kernel LeanCert.Analysis.DBN.eventually_exists_zero_of_locally_uniform
#assert_trust kernel LeanCert.Analysis.DBN.xiHeat_zero
#assert_trust kernel LeanCert.Analysis.DBN.dobnerMap_re_gt_half
#assert_trust kernel LeanCert.Analysis.DBN.nonreal_zero_of_dobner_limit
#assert_trust kernel LeanCert.Analysis.DBN.Lambda_nonneg_of_negative_time_zeros

/-! ## Actual Dobner normalization and contour expansion; no asymptotic claim -/

#assert_trust kernel LeanCert.Analysis.DBN.normalizedHeat_identity
#assert_trust kernel LeanCert.Analysis.DBN.normalizedHeat_zero
#assert_trust kernel LeanCert.Analysis.DBN.differentiableAt_normalizedHeat
#assert_trust kernel LeanCert.Analysis.DBN.gaussianShift_average_H_zero
#assert_trust kernel LeanCert.Analysis.DBN.verticalGaussianIntegral
#assert_trust kernel LeanCert.Analysis.DBN.verticalGaussianIntegral_integrable
#assert_trust kernel LeanCert.Analysis.DBN.gammaContourWeight_integrable
#assert_trust kernel LeanCert.Analysis.DBN.dobnerContourTerm_tsum_eq_heat
#assert_trust kernel LeanCert.Analysis.DBN.normalizedContourTerm_tsum
#assert_trust kernel LeanCert.Analysis.DBN.normalizedHeat_sub_series
#assert_trust kernel LeanCert.Analysis.DBN.Lambda_nonneg_of_normalizedHeatApproximation

/-! ## Coarse reciprocal Gamma growth; still no saddle-point approximation -/

#assert_trust kernel LeanCert.Analysis.DBN.norm_inv_Gamma_le_reflection
#assert_trust kernel LeanCert.Analysis.DBN.norm_inv_Gamma_add_nat_le
#assert_trust kernel LeanCert.Analysis.DBN.norm_inv_Gamma_le_exp_on_strip
#assert_trust kernel LeanCert.Analysis.DBN.norm_inv_dobnerGamma_le
#assert_trust kernel LeanCert.Analysis.DBN.norm_inv_xiGamma_le
#assert_trust kernel LeanCert.Analysis.DBN.norm_inv_dobnerGamma_le_exp_on_strip

/-! ## Actual DBN contour shifts and saddle cancellation; no relative asymptotic -/

#assert_trust kernel LeanCert.Analysis.ContourShift.integral_vertical_eq_of_holomorphic_of_vanish
#assert_trust kernel LeanCert.Analysis.DBN.saddleIntegrand_strip_bound
#assert_trust kernel LeanCert.Analysis.DBN.saddleIntegrand_vertical_integrable
#assert_trust kernel LeanCert.Analysis.DBN.saddleIntegrand_contour_shift
#assert_trust kernel LeanCert.Analysis.DBN.normalizedContourTerm_eq_shifted_integral
#assert_trust kernel LeanCert.Analysis.DBN.normalizedContourTerm_eq_saddle_line
#assert_trust kernel LeanCert.Analysis.DBN.saddleIntegrand_normalized_factorization

/-! ## Relative Gamma estimates: derived from the actual Euler limit -/

#assert_trust kernel LeanCert.Analysis.GammaRatio.relative_error_bound
#assert_trust kernel LeanCert.Analysis.GammaRatio.relative_error_bound_growing
#assert_trust kernel LeanCert.Analysis.DBN.xiGamma_relative_error_bound
#assert_trust kernel LeanCert.Analysis.DBN.xiGamma_relative_error_eventually
#assert_trust kernel LeanCert.Analysis.DBN.saddleIntegrand_quadratic_relative_error_bound

/-! ## Newman nonnegativity: unconditional, actual DBN threshold -/

#assert_trust kernel LeanCert.Analysis.DBN.real_Gamma_le_exp_sq
#assert_trust kernel LeanCert.Analysis.DBN.norm_xiGamma_le_exp_sq
#assert_trust kernel LeanCert.Analysis.DBN.norm_xiGamma_linearRatio_le
#assert_trust kernel LeanCert.Analysis.DBN.centeredKernel_joint_majorant
#assert_trust kernel LeanCert.Analysis.DBN.normalizedContourTerm_tendsto
#assert_trust kernel LeanCert.Analysis.DBN.normalizedHeat_sub_series_tendsto
#assert_trust kernel LeanCert.Analysis.DBN.normalizedHeatApproximation
#assert_trust kernel LeanCert.Analysis.DBN.Lambda_nonneg
