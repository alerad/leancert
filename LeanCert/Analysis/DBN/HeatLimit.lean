import LeanCert.Analysis.DBN.HeatShift
import LeanCert.Analysis.DBN.HeatRegularity
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

/-! Locally uniform convergence of finite imaginary shifts to time one half. -/
namespace LeanCert.Analysis.DBN
open Complex MeasureTheory Set Filter
open scoped Topology

/-- The first two nonnegative terms of the cosh series give the lower squeeze. -/
theorem one_add_half_sq_le_cosh (x : ℝ) : 1+x^2/2 ≤ Real.cosh x := by
  have h := (Real.hasSum_cosh x).summable.sum_le_tsum (Finset.range 2)
    (fun n _ => div_nonneg (by rw [pow_mul]; exact pow_nonneg (sq_nonneg x) n) (Nat.cast_nonneg _))
  have h' : (∑ n ∈ Finset.range 2, x^(2*n)/(Nat.factorial (2*n) : ℝ)) ≤ Real.cosh x := by
    simpa only [Real.cosh_eq_tsum] using h
  norm_num [Finset.sum_range_succ] at h'
  exact h'

/-- The scalar heat-limit prototype needs no Taylor remainder or l'Hopital rule. -/
theorem cosh_multiplier_tendsto (u : ℝ) :
    Filter.Tendsto (fun n : ℕ => Real.cosh (Real.sqrt (1/(n : ℝ))*u)^n)
      Filter.atTop (nhds (Real.exp (u^2/2))) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (Real.tendsto_one_add_div_pow_exp (u^2/2)) tendsto_const_nhds
  · filter_upwards [Filter.eventually_gt_atTop 0] with n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hs : (Real.sqrt (1/(n : ℝ))*u)^2 = u^2/(n : ℝ) := by
      rw [mul_pow, Real.sq_sqrt (by positivity)]
      ring
    have h := one_add_half_sq_le_cosh (Real.sqrt (1/(n : ℝ))*u)
    rw [hs] at h
    rw [show 1+(u^2/2)/(n : ℝ) = 1+(u^2/(n : ℝ))/2 by ring]
    exact pow_le_pow_left₀ (by positivity) h n
  · filter_upwards [Filter.eventually_gt_atTop 0] with n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have h := Analysis.DBN.cosh_pow_le_heat_multiplier (Real.sqrt (1/(n : ℝ))) u n
    rw [Real.sq_sqrt (by positivity)] at h
    simpa [ne_of_gt hn', div_eq_mul_inv, mul_assoc, mul_comm] using h


noncomputable def unitShift (n : ℕ) : ℂ → ℂ :=
  shiftIter (Real.sqrt (1 / ((n+1 : ℕ) : ℝ))) (n+1) (H 0)

theorem unitShift_budget (n : ℕ) :
    ((n+1 : ℕ) : ℝ) * (Real.sqrt (1 / ((n+1 : ℕ) : ℝ))) ^ 2 = 1 := by
  rw [Real.sq_sqrt (by positivity)]
  field_simp

private theorem multiplier_succ_tendsto (u : ℝ) :
    Tendsto (fun n : ℕ => Real.cosh (Real.sqrt (1/((n+1 : ℕ) : ℝ))*u)^(n+1))
      atTop (𝓝 (Real.exp (u^2/2))) :=
  (cosh_multiplier_tendsto u).comp (tendsto_add_atTop_nat 1)

/-- Joint convergence with a moving complex argument; this is stronger than
pointwise convergence and supplies the locally uniform heat limit. -/
theorem unitShift_joint_tendsto (z : ℂ) :
    Tendsto (fun p : ℕ × ℂ => unitShift p.1 p.2)
      (atTop ×ˢ 𝓝 z) (𝓝 (H (1/2) z)) := by
  let B : ℝ → ℝ := fun u =>
    (44 * Real.exp ((1/2 : ℝ)^2+(|z.im|+1+1)^2+1)) * Real.exp (-u^2)
  have hi : IntegrableOn B (Ioi 0) := by
    simpa only [B, IntegrableOn, neg_mul, one_mul] using
      (integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1)).integrableOn.const_mul
        (44 * Real.exp ((1/2 : ℝ)^2+(|z.im|+1+1)^2+1))
  have hnear : ∀ᶠ w : ℂ in 𝓝 z, |w.im| ≤ |z.im|+1 := by
    have h := (Complex.continuous_im.abs.tendsto z).eventually
      (gt_mem_nhds (by linarith : |z.im| < |z.im|+1))
    exact h.mono (fun w hw => hw.le)
  have hb : ∀ᶠ p : ℕ × ℂ in atTop ×ˢ 𝓝 z,
      ∀ᵐ u ∂volume.restrict (Ioi (0 : ℝ)),
        ‖shiftHeatIntegrand 0 (Real.sqrt (1/((p.1+1 : ℕ) : ℝ))) (p.1+1) p.2 u‖ ≤ B u := by
    filter_upwards [tendsto_snd.eventually hnear] with p hp
    exact (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall (fun u hu =>
      shiftHeatIntegrand_bound_unit _ _ (unitShift_budget p.1) _ hp hu.le))
  have hm : ∀ᶠ p : ℕ × ℂ in atTop ×ˢ 𝓝 z,
      AEStronglyMeasurable
        (shiftHeatIntegrand 0 (Real.sqrt (1/((p.1+1 : ℕ) : ℝ))) (p.1+1) p.2)
        (volume.restrict (Ioi 0)) := Eventually.of_forall (fun p =>
      (shiftHeatIntegrand_integrable 0 _ _ _).aestronglyMeasurable)
  have hl : ∀ᵐ u ∂volume.restrict (Ioi (0 : ℝ)),
      Tendsto (fun p : ℕ × ℂ =>
        shiftHeatIntegrand 0 (Real.sqrt (1/((p.1+1 : ℕ) : ℝ))) (p.1+1) p.2 u)
        (atTop ×ˢ 𝓝 z) (𝓝 (heatIntegrand (1/2) z u)) := by
    apply Eventually.of_forall
    intro u
    have hm := (Complex.continuous_ofReal.tendsto _).comp
      ((multiplier_succ_tendsto u).comp (tendsto_fst (g := 𝓝 z)))
    have hc : Continuous (fun w : ℂ => heatIntegrand 0 w u) := by
      unfold heatIntegrand; fun_prop
    have hh := hm.mul (hc.tendsto z |>.comp tendsto_snd)
    convert hh using 1 <;> simp [shiftHeatIntegrand, heatIntegrand,
      div_eq_mul_inv, mul_comm, mul_left_comm]
  have h := tendsto_integral_filter_of_dominated_convergence B hm hb hi hl
  simpa only [unitShift, shiftIter_H_eq_integral, H] using h

theorem unitShift_convergence : TendstoLocallyUniformly unitShift (H (1/2)) atTop := by
  apply tendstoLocallyUniformly_iff_forall_tendsto.mpr
  intro z
  exact (((H_entire (1/2)).continuous.tendsto z |>.comp tendsto_snd).prodMk_nhds
    (unitShift_joint_tendsto z)).mono_right (nhds_le_uniformity _)

end LeanCert.Analysis.DBN
