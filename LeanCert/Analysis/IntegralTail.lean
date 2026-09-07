import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic

/-! Exponential and Gaussian majorants for right improper integral tails.
Measurability and integrability are explicit; a totalized integral value alone
is never treated as evidence of convergence. -/
namespace LeanCert.Analysis.IntegralTail

open MeasureTheory Set
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- An exponential majorant proves integrability and bounds the tail norm. -/
theorem of_exponential (f : ℝ → E) (b C a : ℝ) (ha : 0 < a)
    (hf : AEStronglyMeasurable f (volume.restrict (Ioi b)))
    (hbound : ∀ x ∈ Ioi b, ‖f x‖ ≤ C * Real.exp (-a*x)) :
    IntegrableOn f (Ioi b) ∧
      ‖∫ x in Ioi b, f x‖ ≤ C * Real.exp (-a*b) / a := by
  have hg := (integrableOn_exp_mul_Ioi (neg_neg_of_pos ha) b).const_mul C
  have hb : ∀ᵐ x ∂volume.restrict (Ioi b), ‖f x‖ ≤ C * Real.exp (-a*x) :=
    (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall hbound)
  refine ⟨hg.mono' hf hb, ?_⟩
  have ht := norm_integral_le_of_norm_le hg hb
  rw [integral_const_mul, integral_exp_mul_Ioi (neg_neg_of_pos ha)] at ht
  convert ht using 1
  ring

/-- On `x > b > 0`, Gaussian decay is dominated by exponential decay with
rate `a*b`. This bound is deliberately elementary, not the sharp Mills bound. -/
theorem of_gaussian (f : ℝ → E) (b C a : ℝ) (hb : 0 < b) (hC : 0 ≤ C) (ha : 0 < a)
    (hf : AEStronglyMeasurable f (volume.restrict (Ioi b)))
    (hbound : ∀ x ∈ Ioi b, ‖f x‖ ≤ C * Real.exp (-a*x^2)) :
    IntegrableOn f (Ioi b) ∧
      ‖∫ x in Ioi b, f x‖ ≤ C * Real.exp (-a*b^2) / (a*b) := by
  have h := of_exponential f b C (a*b) (mul_pos ha hb) hf (fun x hx => by
    apply (hbound x hx).trans
    apply mul_le_mul_of_nonneg_left _ hC
    apply Real.exp_le_exp.mpr
    have hx0 : 0 ≤ x := (hb.trans hx).le
    nlinarith [mul_nonneg ha.le (mul_nonneg (sub_nonneg.mpr hx.le) hx0)])
  have he : -(a*b)*b = -a*b^2 := by ring
  simpa only [he] using h

/-- Join a finite interval integral to an integrable right tail. -/
theorem remainder_eq (f : ℝ → E) (a b : ℝ)
    (hhead : IntervalIntegrable f volume a b) (htail : IntegrableOn f (Ioi b)) :
    (∫ x in Ioi a, f x) - (∫ x in a..b, f x) = ∫ x in Ioi b, f x := by
  rw [← intervalIntegral.integral_interval_add_Ioi' hhead htail]
  abel

end LeanCert.Analysis.IntegralTail
