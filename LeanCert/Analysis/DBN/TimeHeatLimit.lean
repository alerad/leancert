import LeanCert.Analysis.DBN.HeatLimit

/-! Finite imaginary shifts converge locally uniformly to forward heat evolution. -/
namespace LeanCert.Analysis.DBN
open Complex MeasureTheory Set Filter
open scoped Topology

noncomputable def timeShift (t δ : ℝ) (n : ℕ) : ℂ → ℂ :=
  shiftIter (Real.sqrt (2*δ) * Real.sqrt (1 / ((n+1 : ℕ) : ℝ))) (n+1) (H t)

theorem timeShift_budget (δ : ℝ) (hδ : 0 ≤ δ) (n : ℕ) :
    ((n+1 : ℕ) : ℝ) * (Real.sqrt (2*δ) * Real.sqrt (1 / ((n+1 : ℕ) : ℝ))) ^ 2 = 2*δ := by
  rw [mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
  field_simp

private theorem timeMultiplier_tendsto (δ : ℝ) (hδ : 0 ≤ δ) (u : ℝ) :
    Tendsto (fun n : ℕ => Real.cosh ((Real.sqrt (2*δ) *
      Real.sqrt (1/((n+1 : ℕ) : ℝ)))*u)^(n+1))
      atTop (𝓝 (Real.exp (δ*u^2))) := by
  have h := (cosh_multiplier_tendsto (Real.sqrt (2*δ)*u)).comp (tendsto_add_atTop_nat 1)
  have he : (Real.sqrt (2*δ)*u)^2/2 = δ*u^2 := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    ring
  simpa only [Function.comp_def, he, mul_assoc, mul_left_comm] using h

/-- Joint convergence with a moving complex argument; this is stronger than
pointwise convergence and supplies the locally uniform heat limit. -/
theorem timeShift_joint_tendsto (t δ : ℝ) (hδ : 0 ≤ δ) (z : ℂ) :
    Tendsto (fun p : ℕ × ℂ => timeShift t δ p.1 p.2)
      (atTop ×ˢ 𝓝 z) (𝓝 (H (t+δ) z)) := by
  let B : ℝ → ℝ := fun u =>
    (44 * Real.exp (|t+δ|^2+(|z.im|+1+1)^2+1)) * Real.exp (-u^2)
  have hi : IntegrableOn B (Ioi 0) := by
    simpa only [B, IntegrableOn, neg_mul, one_mul] using
      (integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1)).integrableOn.const_mul
        (44 * Real.exp (|t+δ|^2+(|z.im|+1+1)^2+1))
  have hnear : ∀ᶠ w : ℂ in 𝓝 z, |w.im| ≤ |z.im|+1 := by
    have h := (Complex.continuous_im.abs.tendsto z).eventually
      (gt_mem_nhds (by linarith : |z.im| < |z.im|+1))
    exact h.mono (fun w hw => hw.le)
  have hb : ∀ᶠ p : ℕ × ℂ in atTop ×ˢ 𝓝 z,
      ∀ᵐ u ∂volume.restrict (Ioi (0 : ℝ)),
        ‖shiftHeatIntegrand t (Real.sqrt (2*δ) * Real.sqrt (1/((p.1+1 : ℕ) : ℝ))) (p.1+1) p.2 u‖ ≤ B u := by
    filter_upwards [tendsto_snd.eventually hnear] with p hp
    exact (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall (fun u hu =>
      by
        have h := shiftHeatIntegrand_norm_le t
          (Real.sqrt (2*δ) * Real.sqrt (1/((p.1+1 : ℕ) : ℝ))) (p.1+1) p.2 u
        rw [timeShift_budget δ hδ, show 2*δ/2 = δ by ring] at h
        exact h.trans (heatIntegrand_bound_box |t+δ| (|z.im|+1) le_rfl hp hu.le)))
  have hm : ∀ᶠ p : ℕ × ℂ in atTop ×ˢ 𝓝 z,
      AEStronglyMeasurable
        (shiftHeatIntegrand t (Real.sqrt (2*δ) * Real.sqrt (1/((p.1+1 : ℕ) : ℝ))) (p.1+1) p.2)
        (volume.restrict (Ioi 0)) := Eventually.of_forall (fun p =>
      (shiftHeatIntegrand_integrable t _ _ _).aestronglyMeasurable)
  have hl : ∀ᵐ u ∂volume.restrict (Ioi (0 : ℝ)),
      Tendsto (fun p : ℕ × ℂ =>
        shiftHeatIntegrand t (Real.sqrt (2*δ) * Real.sqrt (1/((p.1+1 : ℕ) : ℝ))) (p.1+1) p.2 u)
        (atTop ×ˢ 𝓝 z) (𝓝 (heatIntegrand (t+δ) z u)) := by
    apply Eventually.of_forall
    intro u
    have hm := (Complex.continuous_ofReal.tendsto _).comp
      ((timeMultiplier_tendsto δ hδ u).comp (tendsto_fst (g := 𝓝 z)))
    have hc : Continuous (fun w : ℂ => heatIntegrand t w u) := by
      unfold heatIntegrand; fun_prop
    have hh := hm.mul (hc.tendsto z |>.comp tendsto_snd)
    convert hh using 1 <;> simp [shiftHeatIntegrand, heatIntegrand,
      add_mul, Real.exp_add, Complex.ofReal_mul, mul_assoc, mul_comm, mul_left_comm]
  have h := tendsto_integral_filter_of_dominated_convergence B hm hb hi hl
  simpa only [timeShift, shiftIter_H_eq_integral, H] using h

theorem timeShift_convergence (t δ : ℝ) (hδ : 0 ≤ δ) :
    TendstoLocallyUniformly (timeShift t δ) (H (t+δ)) atTop := by
  apply tendstoLocallyUniformly_iff_forall_tendsto.mpr
  intro z
  exact (((H_entire (t+δ)).continuous.tendsto z |>.comp tendsto_snd).prodMk_nhds
    (timeShift_joint_tendsto t δ hδ z)).mono_right (nhds_le_uniformity _)


end LeanCert.Analysis.DBN
