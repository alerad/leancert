/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Analysis.DBN.DobnerCenteredKernel
import Mathlib.MeasureTheory.Integral.DominatedConvergence

namespace LeanCert.Analysis.DBN
open Complex Filter Set MeasureTheory
open scoped Topology

def upperStripFilter (M : ℝ) : Filter ℂ :=
  Filter.comap Complex.im atTop ⊓ Filter.principal {s : ℂ | |s.re| ≤ M}

instance (M : ℝ) : (upperStripFilter M).IsCountablyGenerated := by
  unfold upperStripFilter
  infer_instance

theorem upperStrip_im (M : ℝ) : Tendsto Complex.im (upperStripFilter M) atTop :=
  tendsto_comap.mono_left inf_le_left

theorem upperStrip_re (M : ℝ) : ∀ᶠ s in upperStripFilter M, |s.re| ≤ M :=
  (show ∀ᶠ s in Filter.principal {s : ℂ | |s.re| ≤ M}, |s.re| ≤ M by simp).filter_mono inf_le_right

theorem upperStrip_height (M Y : ℝ) : ∀ᶠ s in upperStripFilter M, Y ≤ s.im :=
  (upperStrip_im M).eventually (eventually_ge_atTop Y)

theorem xiGamma_linearRatio_tendsto {ι : Type*} {l : Filter ι} {s u : ι → ℂ}
    (hi : Tendsto (fun i => (s i).im) l atTop)
    (hr : ∀ᶠ i in l, 0 ≤ (s i).re+(s i).im/2)
    {R : ℝ} (hR : 0 ≤ R) (hu : ∀ᶠ i in l, ‖u i‖ ≤ R) :
    Tendsto (fun i => xiGamma (s i+u i)/xiGamma (s i) *
      Complex.exp (-Complex.log (s i/(2*Real.pi))*u i/2)) l (𝓝 1) := by
  let A := fun i => Complex.log (s i/(2*Real.pi))*u i/2
  let Q := fun i => (u i)^2/(4*s i)
  let P := fun i => xiGamma (s i+u i)/xiGamma (s i) / Complex.exp (A i+Q i)
  have hP : Tendsto P l (𝓝 1) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    obtain ⟨Y, _, hY⟩ := xiGamma_relative_error_eventually R hR hε
    filter_upwards [hr, hu, hi.eventually (eventually_ge_atTop Y)] with i hir hiu hiy
    simpa only [P, A, Q, dist_eq_norm] using hY (s i) (u i) hiy hir hiu
  have hQ : Tendsto Q l (𝓝 0) := by
    have hsmall : Tendsto (fun i => R^2/4 * ((s i).im)⁻¹) l (𝓝 0) := by
      simpa using (tendsto_inv_atTop_zero.comp hi).const_mul (R^2/4)
    apply squeeze_zero_norm' _ hsmall
    filter_upwards [hu, hi.eventually (eventually_ge_atTop 1)] with i hiu hiy
    have hn : (s i).im ≤ ‖s i‖ := (le_abs_self _).trans (Complex.abs_im_le_norm _)
    dsimp [Q]
    rw [norm_div, norm_pow, norm_mul, Complex.norm_ofNat]
    calc
      _ ≤ R^2/(4*(s i).im) := by gcongr
      _ = _ := by ring
  have he (i : ι) : xiGamma (s i+u i)/xiGamma (s i) *
      Complex.exp (-Complex.log (s i/(2*Real.pi))*u i/2) = P i*Complex.exp (Q i) := by
    dsimp [P, A]
    rw [show -Complex.log (s i/(2*Real.pi))*u i/2 = -(Complex.log (s i/(2*Real.pi))*u i/2) by ring]
    simp only [Complex.exp_add, Complex.exp_neg]
    field_simp
  simpa only [he, Complex.exp_zero, mul_one, Function.comp_apply] using
    hP.mul ((Complex.continuous_exp.tendsto 0).comp hQ)

theorem centeredLinearRatio_tendsto {a M : ℝ} (ha : 0 < a) (hM : 0 ≤ M)
    {L : ℝ} (hL : 0 ≤ L) (v : ℝ) :
    Tendsto (fun s => xiGamma (s+saddleDisplacement a s L v)/xiGamma s *
      Complex.exp (-Complex.log (s/(2*Real.pi))*saddleDisplacement a s L v/2))
      (upperStripFilter M) (𝓝 1) := by
  refine xiGamma_linearRatio_tendsto (upperStrip_im M) ?_
    (R := 2*a*L+(M+2)+|v|) (by positivity) ?_
  · filter_upwards [upperStrip_re M, upperStrip_height M (2*M)] with s hs hy
    have := (abs_le.mp hs).1
    linarith
  · filter_upwards [upperStrip_re M] with s hs
    have he := saddleOffset_le ha hM hs hL
    have he0 := saddleOffset_nonneg a s L
    have hn : ‖saddleDisplacement a s L v‖ ≤ |2*a*L+saddleOffset a s L|+|v| := by
      simpa only [saddleDisplacement, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        Complex.norm_I, mul_one] using norm_add_le (((2*a*L+saddleOffset a s L : ℝ) : ℂ)) ((v : ℂ)*I)
    rw [abs_of_nonneg (by positivity)] at hn
    linarith

noncomputable def centeredModel (a : ℝ) (s : ℂ) (L v : ℝ) : ℂ :=
  Complex.exp (-s*(L : ℂ)+(saddleDisplacement a s L v)^2/(4*(a : ℂ))-
    saddleDisplacement a s L v*(L : ℂ))

theorem centeredModel_norm_bound {a M : ℝ} (ha : 0 < a) (hM : 0 ≤ M)
    {s : ℂ} (hs : |s.re| ≤ M) {L : ℝ} (hL : 0 ≤ L) (v : ℝ) :
    ‖centeredModel a s L v‖ ≤
      Real.exp (M*L-a*L^2+(M+2)^2/(4*a))*Real.exp (-v^2/(4*a)) := by
  rw [centeredModel, Complex.norm_exp, centeredGaussian_re ha, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have he := saddleOffset_le ha hM hs hL
  have he0 := saddleOffset_nonneg a s L
  have he2 : (saddleOffset a s L)^2/(4*a) ≤ (M+2)^2/(4*a) := by gcongr
  have hx : -s.re*L ≤ M*L := by have := (abs_le.mp hs).1; nlinarith
  ring_nf at hx he2 ⊢
  linarith

theorem centeredResidual_tendsto {a M : ℝ} (ha : 0 < a) (hM : 0 ≤ M)
    {L : ℝ} (hL : 0 ≤ L) (v : ℝ) :
    Tendsto (fun s => centeredKernel a s L v-centeredModel a s L v)
      (upperStripFilter M) (𝓝 0) := by
  let R := fun s => xiGamma (s+saddleDisplacement a s L v)/xiGamma s *
      Complex.exp (-Complex.log (s/(2*Real.pi))*saddleDisplacement a s L v/2)
  let B := Real.exp (M*L-a*L^2+(M+2)^2/(4*a))*Real.exp (-v^2/(4*a))
  have hlim : Tendsto (fun s => ‖R s-1‖*B) (upperStripFilter M) (𝓝 0) := by
    simpa only [sub_self, norm_zero, zero_mul] using
      ((centeredLinearRatio_tendsto ha hM hL v).sub_const 1).norm.mul_const B
  apply squeeze_zero_norm' _ hlim
  filter_upwards [upperStrip_re M] with s hs
  have he : centeredKernel a s L v-centeredModel a s L v = (R s-1)*centeredModel a s L v := by
    rw [centeredKernel_factorization ha]
    dsimp [R, centeredModel]
    ring
  rw [he, norm_mul]
  exact mul_le_mul_of_nonneg_left (centeredModel_norm_bound ha hM hs hL v) (norm_nonneg _)

theorem saddleLine_point (a : ℝ) (s : ℂ) (L v : ℝ) :
    s+saddleDisplacement a s L v =
      ((max 2 (s.re+2*a*L) : ℝ) : ℂ)+((s.im+v : ℝ) : ℂ)*I := by
  apply Complex.ext
  · simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero, sub_zero,
      zero_mul, add_zero]
    exact saddleLine_re a s L v
  · simp [saddleDisplacement_im]

theorem centeredKernel_integrable {a : ℝ} (ha : 0 < a) (s : ℂ) (L : ℝ) :
    Integrable (centeredKernel a s L) := by
  change Integrable (fun v : ℝ => centeredKernel a s L v)
  have hi := (saddleIntegrand_vertical_integrable (4*a) (by positivity) (dobnerMap a s) L
    (max 2 (s.re+2*a*L)) (lt_of_lt_of_le (by norm_num) (le_max_left _ _))).comp_add_left s.im
  simpa only [centeredKernel, saddleLine_point] using hi.div_const (dobnerGamma a s)

theorem normalizedContourTerm_eq_centered {a : ℝ} (ha : 0 < a) (s : ℂ) (k : ℕ) :
    normalizedContourTerm a s k =
      (∫ v : ℝ, centeredKernel a s (Real.log ((k : ℝ)+1)) v) /
        ((2*Real.sqrt a : ℝ)*(Real.sqrt Real.pi : ℂ)) := by
  rw [normalizedContourTerm_eq_saddle_line ha]
  simp only [centeredKernel, saddleLine_point]
  rw [integral_div]
  have hshift := integral_add_left_eq_self (μ := volume)
    (fun y : ℝ => saddleIntegrand (4*a) (dobnerMap a s) (Real.log ((k : ℝ)+1))
      (((max 2 (s.re+2*a*Real.log ((k : ℝ)+1)) : ℝ) : ℂ)+(y : ℂ)*I)) s.im
  rw [hshift]
  simp only [div_eq_mul_inv, mul_inv]
  ring

theorem shiftedGaussian_integrable {a : ℝ} (ha : 0 < a) (e : ℝ) :
    Integrable (fun v : ℝ => Complex.exp (((e : ℂ)+(v : ℂ)*I)^2/(4*(a : ℂ)))) := by
  have he (v : ℝ) : ((e : ℂ)+(v : ℂ)*I)^2/(4*(a : ℂ)) =
      (-1/(4*(a : ℂ)))*(v : ℂ)^2+((e : ℂ)*I/(2*(a : ℂ)))*(v : ℂ)+(e : ℂ)^2/(4*(a : ℂ)) := by
    ring_nf
    simp only [I_sq]
    ring
  simp only [he]
  apply integrable_cexp_quadratic'
  have hcast : (-1/(4*(a : ℂ))) = ((-1/(4*a) : ℝ) : ℂ) := by push_cast; rfl
  rw [hcast, ofReal_re]
  exact div_neg_of_neg_of_pos (by norm_num) (by positivity)

theorem shiftedGaussian_integral {a : ℝ} (ha : 0 < a) (e : ℝ) :
    (∫ v : ℝ, Complex.exp (((e : ℂ)+(v : ℂ)*I)^2/(4*(a : ℂ)))) =
      ((2*Real.sqrt a : ℝ) : ℂ)*(Real.sqrt Real.pi : ℂ) := by
  let c : ℝ := 2*Real.sqrt a
  let q : ℂ := (e : ℂ)*I/(c : ℂ)
  have hc : 0 < c := by dsimp [c]; positivity
  have hc2 : (c : ℂ)^2 = 4*(a : ℂ) := by
    have hr : (2*Real.sqrt a)^2 = 4*a := by nlinarith [Real.sq_sqrt ha.le]
    dsimp [c]
    convert congrArg Complex.ofReal hr using 1 <;> push_cast <;> rfl
  have he (v : ℝ) : Complex.exp (((e : ℂ)+(v : ℂ)*I)^2/(4*(a : ℂ))) = gaussianShift q (v/c) := by
    unfold gaussianShift q
    push_cast
    rw [← hc2]
    congr 1
    field_simp
    ring_nf
    simp only [I_sq]
    ring
  have hg : (∫ x : ℝ, gaussianShift q x) = (Real.sqrt Real.pi : ℂ) := by
    simpa using gaussianShift_cos_integral q 0 0
  simp only [he]
  rw [Measure.integral_comp_div, hg, abs_of_pos hc, Complex.real_smul]

theorem centeredModel_eq {a : ℝ} (ha : 0 < a) (s : ℂ) (L v : ℝ) :
    centeredModel a s L v = Complex.exp (-s*(L : ℂ)-(a : ℂ)*(L : ℂ)^2) *
      Complex.exp ((((saddleOffset a s L : ℝ) : ℂ)+(v : ℂ)*I)^2/(4*(a : ℂ))) := by
  rw [centeredModel, ← Complex.exp_add]
  congr 1
  unfold saddleDisplacement
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr ha.ne']
  ring

theorem centeredModel_integrable {a : ℝ} (ha : 0 < a) (s : ℂ) (L : ℝ) :
    Integrable (centeredModel a s L) := by
  change Integrable (fun v : ℝ => centeredModel a s L v)
  simp only [centeredModel_eq ha]
  exact (shiftedGaussian_integrable ha _).const_mul _

theorem centeredModel_integral {a : ℝ} (ha : 0 < a) (s : ℂ) (L : ℝ) :
    (∫ v : ℝ, centeredModel a s L v) /
      ((2*Real.sqrt a : ℝ)*(Real.sqrt Real.pi : ℂ)) =
        Complex.exp (-s*(L : ℂ)-(a : ℂ)*(L : ℂ)^2) := by
  simp only [centeredModel_eq ha, integral_const_mul, shiftedGaussian_integral ha]
  rw [mul_div_cancel_right₀]
  exact mul_ne_zero (by exact_mod_cast (show (2*Real.sqrt a : ℝ) ≠ 0 by positivity))
    (by exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne')

theorem centeredResidual_integral_tendsto {a M : ℝ} (ha : 0 < a) (hM : 0 ≤ M)
    {L : ℝ} (hL : 0 ≤ L) :
    Tendsto (fun s => ∫ v : ℝ, centeredKernel a s L v-centeredModel a s L v)
      (upperStripFilter M) (𝓝 0) := by
  obtain ⟨C, Y, hC, _, hbound⟩ := centeredKernel_joint_majorant ha hM
  let B := Real.exp (M*L-a*L^2+(M+2)^2/(4*a))
  let bound := fun v : ℝ => C*Real.exp (-a*L^2/4)*Real.exp (-v^2/(32*a))+
    B*Real.exp (-v^2/(4*a))
  have hi (c : ℝ) (hc : 0 < c) : Integrable (fun v : ℝ => Real.exp (-v^2/c)) := by
    simpa only [neg_mul, one_div_mul_eq_div, neg_div] using
      integrable_exp_neg_mul_sq (b := 1/c) (by positivity)
  have hb : Integrable bound :=
    ((hi (32*a) (by positivity)).const_mul _).add ((hi (4*a) (by positivity)).const_mul _)
  have h := tendsto_integral_filter_of_dominated_convergence (f := fun _ => (0 : ℂ)) bound
    (Filter.Eventually.of_forall (fun s =>
      ((centeredKernel_integrable ha s L).sub (centeredModel_integrable ha s L)).aestronglyMeasurable))
    (show ∀ᶠ s in upperStripFilter M, ∀ᵐ v : ℝ, ‖centeredKernel a s L v-centeredModel a s L v‖ ≤ bound v from by
      filter_upwards [upperStrip_re M, upperStrip_height M Y] with s hs hy
      exact Filter.Eventually.of_forall (fun v => (norm_sub_le _ _).trans
        (add_le_add (hbound s hs hy L v hL) (centeredModel_norm_bound ha hM hs hL v))))
    hb (Filter.Eventually.of_forall (fun v => centeredResidual_tendsto ha hM hL v))
  simpa only [integral_zero, Pi.sub_def] using h

theorem normalizedContourTerm_tendsto {a M : ℝ} (ha : 0 < a) (hM : 0 ≤ M) (k : ℕ) :
    Tendsto (fun s => normalizedContourTerm a s k-DirichletGaussian.term a s k)
      (upperStripFilter M) (𝓝 0) := by
  have h := (centeredResidual_integral_tendsto ha hM
    (show 0 ≤ Real.log ((k : ℝ)+1) by apply Real.log_nonneg; exact le_add_of_nonneg_left (Nat.cast_nonneg k))).div_const
    ((2*Real.sqrt a : ℝ)*(Real.sqrt Real.pi : ℂ))
  have he (s : ℂ) : (∫ v : ℝ, centeredKernel a s (Real.log ((k : ℝ)+1)) v-
      centeredModel a s (Real.log ((k : ℝ)+1)) v) /
      ((2*Real.sqrt a : ℝ)*(Real.sqrt Real.pi : ℂ)) =
        normalizedContourTerm a s k-DirichletGaussian.term a s k := by
    rw [integral_sub (centeredKernel_integrable ha _ _) (centeredModel_integrable ha _ _), sub_div,
      ← normalizedContourTerm_eq_centered ha, centeredModel_integral ha]
    congr 1
    unfold DirichletGaussian.term
    congr 1
    push_cast
    ring
  simpa only [he, zero_div] using h

theorem normalizedContourTerm_majorant {a M : ℝ} (ha : 0 < a) (hM : 0 ≤ M) :
    ∃ C Y : ℝ, 0 < C ∧ 0 < Y ∧ ∀ s : ℂ, |s.re| ≤ M → Y ≤ s.im → ∀ k : ℕ,
      ‖normalizedContourTerm a s k‖ ≤ C*Real.exp (-a*(Real.log ((k : ℝ)+1))^2/4) := by
  obtain ⟨C, Y, hC, hY, hb⟩ := centeredKernel_joint_majorant ha hM
  let g := fun v : ℝ => Real.exp (-v^2/(32*a))
  let J := ∫ v : ℝ, g v
  let d := 2*Real.sqrt a*Real.sqrt Real.pi
  have hd : 0 < d := by dsimp [d]; positivity
  have hg : Integrable g := by
    simpa only [g, neg_mul, one_div_mul_eq_div, neg_div] using
      integrable_exp_neg_mul_sq (b := 1/(32*a)) (by positivity)
  have hJ : 0 ≤ J := integral_nonneg (fun v => (Real.exp_pos _).le)
  refine ⟨C*(J+1)/d, Y, by positivity, hY, ?_⟩
  intro s hs hy k
  let L := Real.log ((k : ℝ)+1)
  have hL : 0 ≤ L := Real.log_nonneg (le_add_of_nonneg_left (Nat.cast_nonneg k))
  have hnorm : ‖((2*Real.sqrt a : ℝ)*(Real.sqrt Real.pi : ℂ))‖ = d := by
    simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg a),
      abs_of_nonneg (Real.sqrt_nonneg Real.pi), d]
  rw [normalizedContourTerm_eq_centered ha, norm_div, hnorm]
  have hI : ‖∫ v : ℝ, centeredKernel a s L v‖ ≤ C*Real.exp (-a*L^2/4)*J := by
    have h := norm_integral_le_of_norm_le (hg.const_mul (C*Real.exp (-a*L^2/4)))
      (Filter.Eventually.of_forall (fun v => hb s hs hy L v hL))
    simpa only [integral_const_mul] using h
  change ‖∫ v : ℝ, centeredKernel a s L v‖/d ≤ (C*(J+1)/d)*Real.exp (-a*L^2/4)
  calc
    _ ≤ (C*Real.exp (-a*L^2/4)*J)/d := div_le_div_of_nonneg_right hI hd.le
    _ ≤ (C*Real.exp (-a*L^2/4)*(J+1))/d := by gcongr; linarith
    _ = _ := by ring

theorem normalizedHeat_sub_series_tendsto {a M : ℝ} (ha : 0 < a) (hM : 0 ≤ M) :
    Tendsto (fun s => normalizedHeat a s-DirichletGaussian.series a s)
      (upperStripFilter M) (𝓝 0) := by
  obtain ⟨C, Y, hC, _, hb⟩ := normalizedContourTerm_majorant ha hM
  let A := Real.exp ((0+2 : ℝ)^2/(4*(a/4)))
  let B := Real.exp ((M+2)^2/(4*a))
  let bound := fun k : ℕ => (C*A+B)*DirichletGaussian.envelope k
  have hen : Summable DirichletGaussian.envelope := by
    simpa using (DirichletGaussian.envelope_hasSum 0).summable
  have hsum : Summable bound := hen.mul_left _
  have hbound : ∀ᶠ s in upperStripFilter M, ∀ k : ℕ,
      ‖normalizedContourTerm a s k-DirichletGaussian.term a s k‖ ≤ bound k := by
    filter_upwards [upperStrip_re M, upperStrip_height M Y] with s hs hy k
    have hgauss : Real.exp (-a*(Real.log ((k : ℝ)+1))^2/4) ≤ A*DirichletGaussian.envelope k := by
      have h := DirichletGaussian.norm_term_le (a := a/4) (R := 0) (s := 0) (by positivity) (by simp) k
      rw [DirichletGaussian.norm_term] at h
      simpa only [zero_re, zero_mul, sub_zero,
        show -(a/4)*(Real.log ((k : ℝ)+1))^2 = -a*(Real.log ((k : ℝ)+1))^2/4 by ring] using h
    have hmain := DirichletGaussian.norm_term_le ha (R := M) (abs_le.mp hs).1 k
    calc
      _ ≤ ‖normalizedContourTerm a s k‖+‖DirichletGaussian.term a s k‖ := norm_sub_le _ _
      _ ≤ C*(A*DirichletGaussian.envelope k)+B*DirichletGaussian.envelope k := by
        exact add_le_add ((hb s hs hy k).trans (mul_le_mul_of_nonneg_left hgauss hC.le)) hmain
      _ = _ := by dsimp [bound]; ring
  have h := tendsto_tsum_of_dominated_convergence hsum (fun k => normalizedContourTerm_tendsto ha hM k) hbound
  simpa only [← normalizedHeat_sub_series ha, tsum_zero] using h

theorem upperStrip_eventually_iff (M : ℝ) (P : ℂ → Prop) :
    (∀ᶠ s in upperStripFilter M, P s) ↔
      ∃ Y : ℝ, ∀ s : ℂ, Y ≤ s.im → |s.re| ≤ M → P s := by
  simp only [upperStripFilter, eventually_inf_principal, eventually_comap, eventually_atTop,
    mem_ofPred_eq]
  constructor
  · rintro ⟨Y, hY⟩
    exact ⟨Y, fun s hy hs => hY s.im hy s rfl hs⟩
  · rintro ⟨Y, hY⟩
    refine ⟨Y, ?_⟩
    intro y hy s hs hre
    apply hY s _ hre
    rwa [hs]

/-- The actual normalized heat function is locally uniformly approximated by
the Gaussian Dirichlet series at large positive imaginary height. -/
theorem normalizedHeatApproximation {a : ℝ} (ha : 0 < a) : NormalizedHeatApproximation a := by
  apply tendstoLocallyUniformly_iff_forall_isCompact.mpr
  intro K hK
  obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
  have hlim := normalizedHeat_sub_series_tendsto ha (abs_nonneg R)
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have he := (Metric.tendsto_nhds.mp hlim) ε hε
  obtain ⟨Y, hY⟩ := (upperStrip_eventually_iff |R| _).mp he
  filter_upwards [eventually_ge_atTop (Y+|R|)] with y hy s hs
  have hn : ‖s‖ ≤ |R| := (hR s hs).trans (le_abs_self R)
  have hre : |(s+(y : ℂ)*I).re| ≤ |R| := by
    simpa using (Complex.abs_re_le_norm s).trans hn
  have him : Y ≤ (s+(y : ℂ)*I).im := by
    have h := (Complex.abs_im_le_norm s).trans hn
    have h' := (abs_le.mp h).1
    simp only [add_im, mul_im, ofReal_re, I_im, ofReal_im, I_re, mul_one, mul_zero, add_zero]
    linarith
  simpa only [dist_comm] using hY (s+(y : ℂ)*I) him hre

/-- Newman's lower bound for the existing de Bruijn–Newman threshold.
All analytic approximation hypotheses have been discharged above. -/
theorem Lambda_nonneg : 0 ≤ Lambda :=
  Lambda_nonneg_of_normalizedHeatApproximation (fun _ ha => normalizedHeatApproximation ha)

end LeanCert.Analysis.DBN
