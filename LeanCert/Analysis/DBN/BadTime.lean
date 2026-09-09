import LeanCert.Analysis.DBN.BackwardGaussian
import LeanCert.Analysis.DBN.FourPoint
import LeanCert.Analysis.DBN.KernelObstruction
import LeanCert.Analysis.DBN.ForwardPreservation

/-!
# Existence of a bad time

If all negative square times had only real zeros, the four-point inequality
for their divisor products would survive Gaussian rescaling and passage to
the kernel. The actual kernel strictly violates that inequality.
-/
namespace LeanCert.Analysis.DBN
open Complex Set Filter MeasureTheory
open scoped Topology

theorem normSq_H_imaginary (t y : ℝ) :
    normSq (H t ((y : ℂ)*I)) = (H t ((y : ℂ)*I)).re^2 := by
  rw [normSq_apply, H_imaginary_im]; ring

private theorem gaussianAverage_four_point_sq {c : ℝ} (hc : 0 < c)
    (ht : -c^2 ∈ realZeroTimes) :
    (gaussianAverage c 0)^20 * (gaussianAverage c 2)^12 ≤
      (gaussianAverage c 3)^2 * (gaussianAverage c 1)^30 := by
  let y : ℝ := 2*c^2
  have h := H_four_point_normSq (-c^2) ht y
  have hzero : normSq (H (-c^2) 0) = (H (-c^2) 0).re^2 := by
    simpa using normSq_H_imaginary (-c^2) 0
  rw [hzero, normSq_H_imaginary, normSq_H_imaginary, normSq_H_imaginary] at h
  let E := Real.exp (-c^2)
  let d := 2*c
  have hscaled := mul_le_mul_of_nonneg_left h
    (show 0 ≤ d^32 * E^48 by positivity)
  have he (k : ℕ) : Real.exp (-c^2*(k : ℝ)) = E^k := by
    change Real.exp (-c^2*(k : ℝ)) = (Real.exp (-c^2))^k
    rw [← Real.exp_nat_mul]; congr 1; ring
  have hA (k : ℕ) : gaussianAverage c k =
      d * E^(k^2) * (H (-c^2) (((k : ℝ)*y : ℝ)*I)).re := by
    rw [gaussianAverage_eq_H hc]
    have hex : Real.exp (-c^2*(k : ℝ)^2) = E^(k^2) := by
      convert he (k^2) using 1 <;> push_cast <;> rfl
    rw [hex]
    have harg : 2*c^2*(k : ℝ) = (k : ℝ)*y := by dsimp [y]; ring
    rw [harg]
  have hA0 := hA 0
  have hA1 := hA 1
  have hA2 := hA 2
  have hA3 := hA 3
  norm_num at hA0 hA1 hA2 hA3
  rw [hA0, hA2, hA3, hA1]
  push_cast at hscaled
  convert hscaled using 1 <;> first | rfl | ring

/-- Not every negative square time can have real-only zeros. -/
theorem exists_bad_negative_square :
    ∃ n : ℕ, -((n : ℝ)+1)^2 ∉ realZeroTimes := by
  by_contra h
  push Not at h
  have hlim (x : ℝ) := gaussianAverage_tendsto x
  have hineq := le_of_tendsto_of_tendsto
    (((hlim 0).pow 20).mul ((hlim 2).pow 12))
    (((hlim 3).pow 2).mul ((hlim 1).pow 30))
    (Eventually.of_forall (fun n => gaussianAverage_four_point_sq
      (show 0 < (n : ℝ)+1 by positivity) (h n)))
  have heven (x : ℝ) (hx : 0 ≤ x) : evenPhi x = Phi x := by
    simp [evenPhi, abs_of_nonneg hx]
  rw [heven 0 (by norm_num), heven 1 (by norm_num),
    heven 2 (by norm_num), heven 3 (by norm_num)] at hineq
  have hroot : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  have hcancel :
      (Real.sqrt Real.pi)^32 * ((Phi 0)^20 * (Phi 2)^12) ≤
      (Real.sqrt Real.pi)^32 * ((Phi 3)^2 * (Phi 1)^30) := by
    convert hineq using 1 <;> first | rfl | ring
  have hbare := (mul_le_mul_iff_of_pos_left (pow_pos hroot 32)).mp hcancel
  have hstrict : ((Phi 3)*(Phi 1)^15)^2 < ((Phi 0)^10*(Phi 2)^6)^2 :=
    pow_lt_pow_left₀ Phi_four_point_obstruction
      (mul_nonneg (Phi_pos (by norm_num)).le (pow_nonneg (Phi_pos (by norm_num)).le _))
      (by norm_num)
  nlinarith [show ((Phi 3)*(Phi 1)^15)^2 = (Phi 3)^2*(Phi 1)^30 by ring,
    show ((Phi 0)^10*(Phi 2)^6)^2 = (Phi 0)^20*(Phi 2)^12 by ring]

theorem exists_bad_time : ∃ b : ℝ, b ∉ realZeroTimes := by
  obtain ⟨n, hn⟩ := exists_bad_negative_square
  exact ⟨-((n : ℝ)+1)^2, hn⟩

theorem realZeroTimes_bddBelow : BddBelow realZeroTimes := by
  obtain ⟨b, hb⟩ := exists_bad_time
  exact realZeroTimes_bddBelow_of_bad_time realZeroTimes_forward hb

end LeanCert.Analysis.DBN
