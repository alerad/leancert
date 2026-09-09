import LeanCert.Analysis.DBN.TimePolynomialApproximation
import LeanCert.Analysis.DBN.TimeHeatLimit
import LeanCert.Analysis.DBN.RealZeroTimes

/-!
# Forward strip contraction for the actual heat integral

Symmetric cutoffs at arbitrary time and the generalized heat limit discharge
both analytic hypotheses of the polynomial transfer theorem. In particular,
the set of real-zero times is upward closed. Lower-boundedness of that set
is a separate assertion and is not assumed by the contraction theorem.
-/
namespace LeanCert.Analysis.DBN
open Complex Set Filter
open scoped Topology

/-- The actual divisor cutoffs inherit any known strip at the starting time. -/
noncomputable def H_stripApproximation (t b : ℝ)
    (hstrip : ∀ z, H t z = 0 → z.im^2 ≤ b^2) :
    StripPolynomialApproximation (H t) b where
  polynomial := TimeApproximation.HZeroPolynomial t
  nonzero := TimeApproximation.HZeroPolynomial_ne_zero t
  conj := TimeApproximation.HZeroPolynomial_conj t
  strip := TimeApproximation.HZeroPolynomial_strip t hstrip
  convergence := TimeApproximation.HZeroPolynomial_convergence t

/-- De Bruijn's squared-strip contraction, including zero elapsed time. -/
theorem H_forward_strip (t b δ : ℝ) (hδ : 0 ≤ δ)
    (hstrip : ∀ z, H t z = 0 → z.im^2 ≤ b^2)
    {z : ℂ} (hz : H (t+δ) z = 0) :
    z.im^2 ≤ max (b^2-2*δ) 0 := by
  rcases hδ.eq_or_lt with he | hp
  · subst δ
    simpa only [add_zero, mul_zero, sub_zero, max_eq_left (sq_nonneg b)] using
      hstrip z (by simpa only [add_zero] using hz)
  · have h := (H_stripApproximation t b hstrip).heat_limit_strip
      (c := Real.sqrt (max (b^2-2*δ) 0)) (H_entire t) (H_entire (t+δ))
      (a := fun k => Real.sqrt (2*δ) * Real.sqrt (1/((k+1 : ℕ) : ℝ)))
      (n := fun k => k+1)
      (fun k => mul_pos (Real.sqrt_pos.mpr (by positivity))
        (Real.sqrt_pos.mpr (by positivity)))
      (fun k => by
        rw [timeShift_budget δ hδ, Real.sq_sqrt (le_max_right _ _)])
      (fun k => ⟨0, shiftIter_H_ne_zero t _ _⟩)
      ⟨0, H_zero_ne_zero (t+δ)⟩ (timeShift_convergence t δ hδ) hz
    simpa only [Real.sq_sqrt (le_max_right _ _)] using h

/-- Real-only zeros remain real under every nonnegative increment of time. -/
theorem H_forward_real (t δ : ℝ) (hδ : 0 ≤ δ)
    (ht : t ∈ realZeroTimes) : t+δ ∈ realZeroTimes := by
  intro z hz
  have h := H_forward_strip t 0 δ hδ
    (fun w hw => by rw [ht w hw]) hz
  have hm : max ((0 : ℝ)^2-2*δ) 0 = 0 := max_eq_right (by nlinarith)
  rw [hm] at h
  nlinarith [sq_nonneg z.im]

theorem realZeroTimes_forward (s : ℝ) (hs : s ∈ realZeroTimes)
    (t : ℝ) (hst : s ≤ t) : t ∈ realZeroTimes := by
  simpa only [add_sub_cancel] using H_forward_real s (t-s) (sub_nonneg.mpr hst) hs

theorem H_real_zeros_of_half_le {t : ℝ} (ht : (1/2 : ℝ) ≤ t)
    (z : ℂ) (hz : H t z = 0) : z.im = 0 :=
  realZeroTimes_forward _ half_mem_realZeroTimes t ht z hz

/-- With forward preservation proved, a bad time is now the only analytic
input required by the finite-threshold characterization. -/
theorem realZeroTimes_eq_Ici_of_bad_time {b : ℝ} (hbad : b ∉ realZeroTimes) :
    realZeroTimes = Ici (sInf realZeroTimes) :=
  realZeroTimes_eq_Ici
    (realZeroTimes_bddBelow_of_bad_time realZeroTimes_forward hbad) realZeroTimes_forward

end LeanCert.Analysis.DBN
