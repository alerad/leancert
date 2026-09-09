import LeanCert.Analysis.DBN.BadTime

/-!
# The de Bruijn–Newman threshold

The actual real-zero time set is nonempty, closed, upward closed, and bounded
below. Its infimum is therefore an attained finite threshold, at most one half.
This is a qualitative classical certificate, not a sharper numerical bound.
-/
namespace LeanCert.Analysis.DBN
open Set

/-- The real-valued de Bruijn–Newman constant for the normalization of `H`. -/
noncomputable def Lambda : ℝ := sInf realZeroTimes

theorem Lambda_isLeast : IsLeast realZeroTimes Lambda :=
  realZeroTimes_isLeast_sInf realZeroTimes_bddBelow

theorem Lambda_le_half : Lambda ≤ (1/2 : ℝ) :=
  realZeroTimes_sInf_le_half realZeroTimes_bddBelow

/-- Exact threshold characterization for the actual heat integral. -/
theorem real_zeros_iff_Lambda_le (t : ℝ) :
    (∀ z : ℂ, H t z = 0 → z.im = 0) ↔ Lambda ≤ t := by
  change t ∈ realZeroTimes ↔ _
  rw [realZeroTimes_eq_Ici realZeroTimes_bddBelow realZeroTimes_forward]
  rfl

theorem H_Lambda_real_zeros (z : ℂ) (hz : H Lambda z = 0) : z.im = 0 :=
  Lambda_isLeast.1 z hz

theorem nonreal_zero_of_lt_Lambda {t : ℝ} (ht : t < Lambda) :
    ∃ z : ℂ, H t z = 0 ∧ z.im ≠ 0 := by
  have h : ¬ ∀ z : ℂ, H t z = 0 → z.im = 0 :=
    fun h => (not_le.mpr ht) ((real_zeros_iff_Lambda_le t).mp h)
  push Not at h
  exact h

/-- The threshold is uniquely determined by its zero characterization. -/
theorem Lambda_unique {a : ℝ}
    (ha : ∀ t : ℝ, (∀ z : ℂ, H t z = 0 → z.im = 0) ↔ a ≤ t) : a = Lambda := by
  apply le_antisymm
  · exact (ha Lambda).mp Lambda_isLeast.1
  · exact (real_zeros_iff_Lambda_le a).mp ((ha a).mpr le_rfl)

/-- Unconditional classical DBN certificate: a finite threshold, the exact
real-zero equivalence, and the one-half upper bound. -/
theorem dbn_certificate :
    ∃ a : ℝ, a ≤ (1/2 : ℝ) ∧
      ∀ t : ℝ, (∀ z : ℂ, H t z = 0 → z.im = 0) ↔ a ≤ t :=
  ⟨Lambda, Lambda_le_half, real_zeros_iff_Lambda_le⟩

end LeanCert.Analysis.DBN
