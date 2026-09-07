import LeanCert.Analysis.DBN.HeatShift
import LeanCert.Analysis.DBN.HeatGrowth
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Util.AssertNoSorry
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

/-! Checked interfaces for the DBN route audit. These are small complete lemmas,
not assumptions standing in for polynomial approximation or Hurwitz. -/
namespace LeanCert.Test.DBNRouteAudit
open Complex Set Metric Analysis.DBN

/-- A reciprocal maximum principle supplies the local ingredient of Hurwitz. -/
theorem disk_lower_bound {f : ℂ → ℂ} {c : ℂ} {r m : ℝ}
    (hr : 0 < r) (hm : 0 < m)
    (hf : DifferentiableOn ℂ f (closedBall c r))
    (hn : ∀ z ∈ closedBall c r, f z ≠ 0)
    (hb : ∀ z ∈ sphere c r, m ≤ ‖f z‖) : m ≤ ‖f c‖ := by
  have hd : DiffContOnCl ℂ (fun z => (f z)⁻¹) (ball c r) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball c hr.ne']
    exact hf.inv hn
  have h := Complex.norm_le_of_forall_mem_frontier_norm_le (isBounded_ball : Bornology.IsBounded (ball c r)) hd
    (C := m⁻¹) (by
      intro z hz
      rw [frontier_ball c hr.ne'] at hz
      rw [norm_inv]
      exact inv_anti₀ hm (hb z hz))
    (z := c) (by rw [closure_ball c hr.ne']; exact mem_closedBall_self hr.le)
  rw [norm_inv] at h
  exact (inv_le_inv₀ (norm_pos_iff.mpr (hn c (mem_closedBall_self hr.le))) hm).mp h

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

/-- info: 'LeanCert.Test.DBNRouteAudit.cosh_multiplier_tendsto' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms cosh_multiplier_tendsto
assert_no_sorry cosh_multiplier_tendsto
assert_no_sorry disk_lower_bound
assert_no_sorry subquadratic_exponent
/-- info: 'LeanCert.Test.DBNRouteAudit.disk_lower_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms disk_lower_bound
/-- info: 'LeanCert.Analysis.DBN.subquadratic_exponent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms subquadratic_exponent
end LeanCert.Test.DBNRouteAudit
