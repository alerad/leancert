import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Tactic

/-! Parameter-dependent integral adapters for a continuous coefficient times
a fixed integrable majorant. Local domination is derived, not assumed. -/
namespace LeanCert.Analysis.ParametricIntegral
open MeasureTheory Filter
open scoped Topology

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem continuous_integral {X : Type*} [TopologicalSpace X] [FirstCountableTopology X]
    (F : X → α → E) (c : X → ℝ) (g : α → ℝ) (hc : Continuous c)
    (hg : Integrable g μ) (hg0 : ∀ᵐ a ∂μ, 0 ≤ g a)
    (hFm : ∀ x, AEStronglyMeasurable (F x) μ)
    (hb : ∀ᵐ a ∂μ, ∀ x, ‖F x a‖ ≤ c x * g a)
    (hFc : ∀ᵐ a ∂μ, Continuous (fun x => F x a)) :
    Continuous (fun x => ∫ a, F x a ∂μ) := by
  apply continuous_iff_continuousAt.mpr
  intro x₀
  apply continuousAt_of_dominated (bound := fun a => (c x₀+1)*g a)
    (Eventually.of_forall hFm) _ (hg.const_mul _) (hFc.mono fun _ h => h.continuousAt)
  have hn : ∀ᶠ x in 𝓝 x₀, c x < c x₀+1 := hc.continuousAt.eventually_lt_const (by linarith)
  filter_upwards [hn] with x hx
  filter_upwards [hb, hg0] with a ha hga
  exact (ha x).trans (mul_le_mul_of_nonneg_right hx.le hga)

theorem hasDerivAt_integral {𝕜 : Type*} [RCLike 𝕜] [NormedSpace 𝕜 E]
    (F F' : 𝕜 → α → E) (c : 𝕜 → ℝ) (g : α → ℝ) (hc : Continuous c)
    (hg : Integrable g μ) (hg0 : ∀ᵐ a ∂μ, 0 ≤ g a)
    (hFm : ∀ x, AEStronglyMeasurable (F x) μ)
    (hF'm : ∀ x, AEStronglyMeasurable (F' x) μ)
    (hb : ∀ᵐ a ∂μ, ∀ x, ‖F' x a‖ ≤ c x * g a)
    (hd : ∀ᵐ a ∂μ, ∀ x, HasDerivAt (fun y => F y a) (F' x a) x)
    (x₀ : 𝕜) (hi : Integrable (F x₀) μ) :
    Integrable (F' x₀) μ ∧
      HasDerivAt (fun x => ∫ a, F x a ∂μ) (∫ a, F' x₀ a ∂μ) x₀ := by
  let s := {x | c x < c x₀+1}
  have hs : s ∈ 𝓝 x₀ := hc.continuousAt.eventually_lt_const (by linarith)
  apply hasDerivAt_integral_of_dominated_loc_of_deriv_le hs
    (Eventually.of_forall hFm) hi (hF'm x₀) _ (hg.const_mul (c x₀+1))
    (hd.mono fun _ h x _ => h x)
  filter_upwards [hb, hg0] with a ha hga
  intro x hx
  exact (ha x).trans (mul_le_mul_of_nonneg_right (le_of_lt hx) hga)

end LeanCert.Analysis.ParametricIntegral
