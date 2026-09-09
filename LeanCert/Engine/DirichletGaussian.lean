/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Analysis.DirichletGaussian
import LeanCert.Core.IntervalRat.Taylor

/-!
# Gaussian Dirichlet tail certificates

The checker uses rational arithmetic and a certified lower bound on log(N+1).
It certifies the omitted tail, not the finite complex head or the DBN heat integral.
-/
namespace LeanCert.Engine.DirichletGaussian
open LeanCert.Core
open LeanCert.Analysis.DirichletGaussian

/-- Sufficient (not necessary) cutoff test, valid throughout Re(s) ≥ -R. -/
def checkTail (a R : ℚ) (N precision : ℕ) : Bool :=
  decide (0 < a ∧ R+2 ≤ a *
    (IntervalRat.logComputable (IntervalRat.singleton ((N : ℚ)+1)) precision).lo)

/-- The executable rational test implies the analytic cutoff inequality. -/
theorem checkTail_sound {a R : ℚ} {N precision : ℕ}
    (h : checkTail a R N precision = true) :
    0 < (a : ℝ) ∧ (R : ℝ)+2 ≤ (a : ℝ)*Real.log ((N : ℝ)+1) := by
  simp only [checkTail, decide_eq_true_eq] at h
  have ha : 0 < (a : ℝ) := by exact_mod_cast h.1
  have hl := IntervalRat.mem_logComputable
    (IntervalRat.mem_singleton ((N : ℚ)+1))
    (by simp only [IntervalRat.singleton]; positivity) precision
  have hb : (R : ℝ)+2 ≤ (a : ℝ)*
      ((IntervalRat.logComputable (IntervalRat.singleton ((N : ℚ)+1)) precision).lo : ℝ) := by
    exact_mod_cast h.2
  refine ⟨ha, hb.trans (mul_le_mul_of_nonneg_left ?_ ha.le)⟩
  simpa only [Rat.cast_add, Rat.cast_natCast, Rat.cast_one] using hl.1

/-- A successful check produces a kernel-checked, half-plane-uniform tail bound. -/
theorem certified_tail {a R : ℚ} {N precision : ℕ}
    (h : checkTail a R N precision = true) {s : ℂ} (hs : -(R : ℝ) ≤ s.re) :
    ‖series (a : ℝ) s - partialSum (a : ℝ) N s‖ ≤ 2/((N : ℝ)+1) := by
  obtain ⟨ha, hN⟩ := checkTail_sound h
  exact tail_bound ha N hN hs

/-- Compose a separately certified finite-head disk with the certified tail. -/
theorem certified_disk {a R : ℚ} {N precision : ℕ}
    (h : checkTail a R N precision = true) {s c : ℂ} (hs : -(R : ℝ) ≤ s.re)
    {error : ℝ} (hhead : ‖partialSum (a : ℝ) N s - c‖ ≤ error) :
    ‖series (a : ℝ) s - c‖ ≤ error + 2/((N : ℝ)+1) := by
  calc
    _ ≤ ‖series (a : ℝ) s - partialSum (a : ℝ) N s‖ +
        ‖partialSum (a : ℝ) N s - c‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ _ := by linarith [certified_tail h hs]

end LeanCert.Engine.DirichletGaussian
