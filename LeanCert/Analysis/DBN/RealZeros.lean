import LeanCert.Analysis.DBN.ShiftLimit
import LeanCert.Analysis.DBN.HeatLimit

/-!
# Real zeros at time one half

The unconditional endpoint theorem for the actual DBN heat integral. The proof
uses symmetric polynomial approximation, finite imaginary-shift contraction,
and two zero-preserving locally uniform limits. No finite-height certificate
or assumed approximation theorem is involved. This is not yet a definition or
bound for a real-valued de Bruijn–Newman constant.
-/
namespace LeanCert.Analysis.DBN
open Complex Set Filter
open scoped Topology

theorem unitShift_real (n : ℕ) {z : ℂ} (hz : unitShift n z = 0) : z.im = 0 :=
  shiftIter_H_unit_real (n+1) (Nat.succ_pos n) hz

/-- Every zero of the actual heat-flow function at time `1/2` is real. -/
theorem H_half_real_zeros (z : ℂ) (hz : H (1/2) z = 0) : z.im = 0 := by
  by_contra him
  exact (entire_limit_ne_zero
    (fun n => shiftIter_entire _ _ (H_entire 0)) (H_entire (1/2))
    ⟨0, H_zero_ne_zero (1/2)⟩ unitShift_convergence
    (U := {w : ℂ | w.im ≠ 0}) (isOpen_ne.preimage Complex.continuous_im)
    (fun n w hw hzero => hw (unitShift_real n hzero)) him) hz

theorem H_half_ne_zero_of_im_ne_zero {z : ℂ} (hz : z.im ≠ 0) : H (1/2) z ≠ 0 :=
  fun h => hz (H_half_real_zeros z h)

end LeanCert.Analysis.DBN
