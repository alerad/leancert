/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Analysis.DBN.DobnerReduction
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne

/-! Actual Gamma normalization of the DBN heat function. No approximation is
assumed in the definitions, holomorphy, or multiplication identities. -/
namespace LeanCert.Analysis.DBN
open Complex Filter Set
open scoped Topology

noncomputable def xiGamma (s : ℂ) : ℂ := s*(s-1)*Gammaℝ s/2
noncomputable def dobnerGamma (a : ℝ) (s : ℂ) : ℂ :=
  xiGamma s * Complex.exp ((s-dobnerMap a s)^2/(4*(a : ℂ)))
noncomputable def normalizedHeat (a : ℝ) (s : ℂ) : ℂ :=
  xiHeat (-4*a) (dobnerMap a s) / dobnerGamma a s

private theorem Gammaℝ_ne_zero_of_im_pos {s : ℂ} (hs : 0 < s.im) : Gammaℝ s ≠ 0 := by
  rw [ne_eq, Gammaℝ_eq_zero_iff]
  rintro ⟨n, rfl⟩
  simp at hs

theorem xiGamma_ne_zero {s : ℂ} (hs : 0 < s.im) : xiGamma s ≠ 0 := by
  have h0 : s ≠ 0 := by intro h; simp [h] at hs
  have h1 : s ≠ 1 := by intro h; simp [h] at hs
  exact div_ne_zero (mul_ne_zero (mul_ne_zero h0 (sub_ne_zero.mpr h1))
    (Gammaℝ_ne_zero_of_im_pos hs)) (by norm_num)

theorem dobnerGamma_ne_zero (a : ℝ) {s : ℂ} (hs : 0 < s.im) : dobnerGamma a s ≠ 0 :=
  mul_ne_zero (xiGamma_ne_zero hs) (Complex.exp_ne_zero _)

theorem xiHeat_entire (t : ℝ) : Differentiable ℂ (xiHeat t) := by
  unfold xiHeat heatCoordinate
  exact differentiable_const _ |>.mul ((H_entire t).comp (by fun_prop))

theorem differentiableAt_dobnerMap (a : ℝ) {s : ℂ} (hs : 0 < s.im) :
    DifferentiableAt ℂ (dobnerMap a) s := by
  have hslit : s/(2*Real.pi : ℂ) ∈ slitPlane := by
    apply mem_slitPlane_iff.mpr
    right
    have he : (s/(2*Real.pi : ℂ)).im = s.im/(2*Real.pi) := by
      rw [show (2*Real.pi : ℂ) = ((2*Real.pi : ℝ) : ℂ) by push_cast; rfl,
        div_ofReal_im]
    rw [he]
    exact ne_of_gt (div_pos hs (by positivity))
  unfold dobnerMap
  exact differentiableAt_id.add ((differentiableAt_const _).mul
    ((differentiableAt_id.div_const _).clog hslit))

theorem differentiableAt_xiGamma {s : ℂ} (hs : 0 < s.im) :
    DifferentiableAt ℂ xiGamma s := by
  have hg : DifferentiableAt ℂ Gammaℝ s := by
    have h := (differentiable_Gammaℝ_inv s).inv
      (inv_ne_zero (Gammaℝ_ne_zero_of_im_pos hs))
    change DifferentiableAt ℂ (fun z => ((Gammaℝ z)⁻¹)⁻¹) s at h
    simpa only [inv_inv] using h
  unfold xiGamma
  fun_prop

theorem differentiableAt_dobnerGamma (a : ℝ) {s : ℂ} (hs : 0 < s.im) :
    DifferentiableAt ℂ (dobnerGamma a) s := by
  unfold dobnerGamma
  exact (differentiableAt_xiGamma hs).mul
    ((((differentiableAt_id.sub (differentiableAt_dobnerMap a hs)).pow 2).div_const _).cexp)

theorem differentiableAt_normalizedHeat (a : ℝ) {s : ℂ} (hs : 0 < s.im) :
    DifferentiableAt ℂ (normalizedHeat a) s :=
  (((xiHeat_entire _).differentiableAt).comp s (differentiableAt_dobnerMap a hs)).div
    (differentiableAt_dobnerGamma a hs) (dobnerGamma_ne_zero a hs)

theorem normalizedHeat_identity (a : ℝ) {s : ℂ} (hs : 0 < s.im) :
    xiHeat (-4*a) (dobnerMap a s) = dobnerGamma a s * normalizedHeat a s := by
  unfold normalizedHeat
  field_simp [dobnerGamma_ne_zero a hs]

/-- The prefactor is the actual zeta completion away from the poles. -/
theorem xiGamma_mul_zeta {s : ℂ} (hs : 0 < s.im) :
    xiGamma s * riemannZeta s = riemannXi s := by
  have h0 : s ≠ 0 := by intro h; simp [h] at hs
  have h1 : s ≠ 1 := by intro h; simp [h] at hs
  rw [riemannXi_eq_mul_completed h0 h1, riemannZeta_def_of_ne_zero h0, xiGamma]
  field_simp [Gammaℝ_ne_zero_of_im_pos hs]

/-- At zero damping the normalization recovers the actual zeta function. -/
theorem normalizedHeat_zero {s : ℂ} (hs : 0 < s.im) :
    normalizedHeat 0 s = riemannZeta s := by
  simp [normalizedHeat, dobnerGamma, dobnerMap, xiHeat_zero,
    ← xiGamma_mul_zeta hs, xiGamma_ne_zero hs]

/-- Upward translates of compact sets avoid all Gamma poles and the log cut. -/
theorem eventually_translate_im_pos {τ : ℕ → ℝ} (hτ : Tendsto τ atTop atTop)
    {K : Set ℂ} (hK : IsCompact K) :
    ∀ᶠ n in atTop, ∀ s ∈ K, 0 < (s+(τ n : ℂ)*I).im := by
  obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
  filter_upwards [hτ.eventually (eventually_gt_atTop R)] with n hn s hs
  have := Complex.abs_im_le_norm s
  have := neg_abs_le s.im
  have := hR s hs
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im,
    Complex.ofReal_im, Complex.I_re, mul_one, mul_zero, add_zero]
  linarith

/-- The single analytic target still required by the Dobner route. All functions
here are concrete; no approximation theorem is asserted by this definition. -/
def NormalizedHeatApproximation (a : ℝ) : Prop :=
  TendstoLocallyUniformly
    (fun y : ℝ => fun s : ℂ => normalizedHeat a (s+(y : ℂ)*I) -
      DirichletGaussian.series a (s+(y : ℂ)*I)) (fun _ => 0) atTop

/-- Conditional only on the concrete uniform approximation, rather than abstract
normalization or holomorphy witnesses. -/
theorem nonreal_zero_of_normalizedHeatApproximation {a : ℝ} (ha : 0 < a)
    (happrox : NormalizedHeatApproximation a) :
    ∃ z : ℂ, H (-4*a) z = 0 ∧ z.im ≠ 0 := by
  obtain ⟨τ, hτ, hrec⟩ := DirichletGaussian.exists_vertical_recurrence ha
  let F : ℕ → ℂ → ℂ := fun n s => normalizedHeat a (s+(τ n : ℂ)*I)
  have herror : TendstoLocallyUniformly
      (fun n s => normalizedHeat a (s+(τ n : ℂ)*I)-
        DirichletGaussian.series a (s+(τ n : ℂ)*I)) (fun _ => 0) atTop := by
    apply tendstoLocallyUniformly_iff_forall_isCompact.mpr
    intro K hK V hV
    exact hτ.eventually ((tendstoLocallyUniformly_iff_forall_isCompact.mp happrox K hK) V hV)
  have hlim : TendstoLocallyUniformly F (DirichletGaussian.series a) atTop := by
    have h := herror.add hrec
    change TendstoLocallyUniformly
      (fun n s => (normalizedHeat a (s+(τ n : ℂ)*I)-DirichletGaussian.series a (s+(τ n : ℂ)*I)) +
        DirichletGaussian.series a (s+(τ n : ℂ)*I))
      (fun s => 0+DirichletGaussian.series a s) atTop at h
    simpa only [sub_add_cancel, zero_add] using h
  have hF : ∀ K : Set ℂ, IsCompact K → ∀ᶠ n in atTop, DifferentiableOn ℂ (F n) K := by
    intro K hK
    filter_upwards [eventually_translate_im_pos hτ hK] with n hn s hs
    exact ((differentiableAt_normalizedHeat a (hn s hs)).comp s
      (show DifferentiableAt ℂ (fun w : ℂ => w+(τ n : ℂ)*I) s by fun_prop)).differentiableWithinAt
  have hid : ∀ K : Set ℂ, IsCompact K → ∀ᶠ n in atTop, ∀ s ∈ K,
      xiHeat (-4*a) (dobnerMap a (s+(τ n : ℂ)*I)) =
        dobnerGamma a (s+(τ n : ℂ)*I)*F n s := by
    intro K hK
    filter_upwards [eventually_translate_im_pos hτ hK] with n hn s hs
    exact normalizedHeat_identity a (hn s hs)
  have h := nonreal_zero_of_dobner_limit (t := -4*a) (by linarith) hτ
    (F := F) (G := fun n s => dobnerGamma a (s+(τ n : ℂ)*I)) hF
  have he : -(-4*a)/4 = a := by ring
  rw [he] at h
  exact h hlim hid

/-- The final bound follows if the concrete approximation is proved at every
positive damping. This theorem does not supply that approximation. -/
theorem Lambda_nonneg_of_normalizedHeatApproximation
    (happrox : ∀ a : ℝ, 0 < a → NormalizedHeatApproximation a) : 0 ≤ Lambda := by
  apply Lambda_nonneg_of_negative_time_zeros
  intro t ht
  have ha : 0 < -t/4 := by linarith
  have h := nonreal_zero_of_normalizedHeatApproximation ha (happrox _ ha)
  simpa only [show -4*(-t/4) = t by ring] using h

end LeanCert.Analysis.DBN
