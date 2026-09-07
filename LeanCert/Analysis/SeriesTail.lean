import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Tactic

/-! Quantitative series tails in complete normed additive groups.
The finite head is indexed by `range N`; the remainder starts at `N`. -/
namespace LeanCert.Analysis.SeriesTail

variable {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]

/-- A summable majorant for the shifted tail proves summability of the whole
series and bounds the error after its first `N` terms. The head is unrestricted. -/
theorem of_majorant (f : ℕ → E) (N : ℕ) (g : ℕ → ℝ)
    (hg : Summable g) (hbound : ∀ k, ‖f (k + N)‖ ≤ g k) :
    Summable f ∧ ‖(∑' n, f n) - ∑ n ∈ Finset.range N, f n‖ ≤ ∑' k, g k := by
  have ht : Summable (fun k => f (k + N)) := hg.of_norm_bounded hbound
  have hf : Summable f := (summable_nat_add_iff N).mp ht
  refine ⟨hf, ?_⟩
  have he := hf.sum_add_tsum_nat_add N
  have hrem : (∑' n, f n) - ∑ n ∈ Finset.range N, f n = ∑' k, f (k + N) := by
    rw [← he]
    abel
  rw [hrem]
  exact tsum_of_norm_bounded hg.hasSum hbound

/-- Geometric domination of a tail, including ratio zero and an empty head.
This proves convergence, rather than assuming it in a certificate. -/
theorem of_geometric (f : ℕ → E) (N : ℕ) (A r : ℝ)
    (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hbound : ∀ k, ‖f (k + N)‖ ≤ A * r ^ k) :
    Summable f ∧ ‖(∑' n, f n) - ∑ n ∈ Finset.range N, f n‖ ≤ A / (1-r) := by
  have hg := (summable_geometric_of_lt_one hr0 hr1).mul_left A
  have h := of_majorant f N _ hg hbound
  simpa only [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1, div_eq_mul_inv] using h

end LeanCert.Analysis.SeriesTail
