import LeanCert.Analysis.DBN.HeatFlow
import Mathlib.Analysis.Normed.Group.FunctionSeries

/-! Continuity of the actual kernel and integrability of its even extension. -/
namespace LeanCert.Analysis.DBN
open Set Filter MeasureTheory
open scoped Topology

theorem continuous_Phi : Continuous Phi := by
  rw [continuous_iff_continuousAt]
  intro x
  let A := kernelScale (x-1)
  have hA : 0 < A := kernelScale_pos _
  have hs : Summable (fun n : ℕ => 22*Real.exp (x+1) * Real.exp (-A*(n : ℝ))) :=
    (Real.summable_exp_nat_mul_of_ge (neg_neg_of_pos hA) (fun n => le_refl (n : ℝ))).mul_left _
  have hc : ContinuousOn Phi (Icc (x-1) (x+1)) := by
    apply continuousOn_tsum (fun n => (show Continuous (fun u => kernelTerm u n) by
      unfold kernelTerm; fun_prop).continuousOn) hs
    intro n u hu
    apply (kernelTerm_bound u n).trans
    apply mul_le_mul
    · exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hu.2) (by norm_num)
    · apply Real.exp_le_exp.mpr
      have hscale : A ≤ kernelScale u := by
        unfold A kernelScale
        gcongr
        exact hu.1
      have hn : (n : ℝ) ≤ ((n : ℝ)+1)^2 := by nlinarith [Nat.cast_nonneg (α := ℝ) n]
      nlinarith [mul_le_mul_of_nonneg_left hn hA.le,
        mul_nonneg (sub_nonneg.mpr hscale) (sq_nonneg ((n : ℝ)+1))]
    · positivity
    · positivity
  exact (hc x (by constructor <;> linarith)).continuousAt
    (Icc_mem_nhds (by linarith) (by linarith))

/-- The even extension is used only as a real integration kernel. -/
noncomputable def evenPhi (u : ℝ) : ℝ := Phi |u|

theorem continuous_evenPhi : Continuous evenPhi := continuous_Phi.comp continuous_abs

theorem evenPhi_pos (u : ℝ) : 0 < evenPhi u := Phi_pos (abs_nonneg u)

theorem evenPhi_bound (u : ℝ) :
    ‖evenPhi u‖ ≤ (44*Real.exp 1) * Real.exp (-u^2) := by
  have h := Phi_bound_nonneg (abs_nonneg u)
  apply h.trans
  rw [mul_assoc, ← Real.exp_add]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Real.exp_le_exp.mpr
  have he := Real.quadratic_le_exp_of_nonneg (show 0 ≤ 4*|u| by positivity)
  have hk := kernelScale_ge_exp (u := |u|)
  nlinarith [sq_abs u, abs_nonneg u, sq_nonneg u]

theorem integrable_evenPhi : Integrable evenPhi := by
  apply ((integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1)).const_mul
    (44*Real.exp 1)).mono' continuous_evenPhi.aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun u => by simpa using evenPhi_bound u)

end LeanCert.Analysis.DBN
