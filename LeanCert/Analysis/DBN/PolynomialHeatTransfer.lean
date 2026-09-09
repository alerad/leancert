import LeanCert.Analysis.DBN.ZeroLimit
import LeanCert.Analysis.DBN.HeatShift

/-!
# Polynomial approximation and heat-limit zero control

This interface is independent of the DBN kernel and of any particular time or
shift budget. An approximation packages actual polynomial evidence; the transfer
lemmas prove finite strip contraction and pass it through a second locally
uniform limit. Nontriviality of both limits is explicit and indispensable.

A caller must still construct the approximation and identify its heat limit.
These are proof obligations, not fields asserting the desired zero theorem.
-/
namespace LeanCert.Analysis.DBN
open Complex Set Filter Polynomial
open scoped Topology

theorem shiftIter_entire (a : ℝ) (n : ℕ) {f : ℂ → ℂ} (hf : Differentiable ℂ f) :
    Differentiable ℂ (shiftIter a n f) := by
  induction n with
  | zero => exact hf
  | succ n ih =>
    change Differentiable ℂ (fun z =>
      (shiftIter a n f (z+(a : ℂ)*I) + shiftIter a n f (z-(a : ℂ)*I))/2)
    fun_prop

theorem shiftIter_convergence {ι : Type*} {l : Filter ι} {F : ι → ℂ → ℂ} {f : ℂ → ℂ}
    (h : TendstoLocallyUniformly F f l) (a : ℝ) (n : ℕ) :
    TendstoLocallyUniformly (fun m => shiftIter a n (F m)) (shiftIter a n f) l := by
  induction n with
  | zero => exact h
  | succ n ih =>
    have hp := ih.comp (fun z => z+(a : ℂ)*I) (by fun_prop)
    have hm := ih.comp (fun z => z-(a : ℂ)*I) (by fun_prop)
    have hu : UniformContinuous (fun w : ℂ => (1/2 : ℂ)*w) :=
      (ContinuousLinearMap.mul ℂ ℂ (1/2)).uniformContinuous
    change TendstoLocallyUniformly
      (fun m z => (shiftIter a n (F m) (z+(a : ℂ)*I) + shiftIter a n (F m) (z-(a : ℂ)*I))/2)
      (fun z => (shiftIter a n f (z+(a : ℂ)*I) + shiftIter a n f (z-(a : ℂ)*I))/2) l
    simpa only [Function.comp_def, Pi.add_apply,
      div_eq_mul_inv, mul_comm, one_mul] using hu.comp_tendstoLocallyUniformly (hp.add hm)

/-- Symmetric polynomial approximants with checked strip control. No evenness
assumption is needed by the transfer theorem; DBN supplies even cutoffs itself. -/
structure StripPolynomialApproximation (f : ℂ → ℂ) (b : ℝ) where
  polynomial : ℕ → ℂ[X]
  nonzero : ∀ n, polynomial n ≠ 0
  conj : ∀ n, (polynomial n).map (starRingEnd ℂ) = polynomial n
  strip : ∀ n z, (polynomial n).eval z = 0 → z.im^2 ≤ b^2
  convergence : TendstoLocallyUniformly (fun n => (polynomial n).eval) f atTop

/-- First limit: the polynomial strip-contraction bound holds for finite shifts
of the approximated entire function, provided that limit is not identically zero. -/
theorem StripPolynomialApproximation.shift_strip {f : ℂ → ℂ} {b : ℝ}
    (P : StripPolynomialApproximation f b) (hf : Differentiable ℂ f)
    {a : ℝ} (ha : 0 < a) (n : ℕ)
    (hnot : ∃ w, shiftIter a n f w ≠ 0) {z : ℂ}
    (hz : shiftIter a n f z = 0) : z.im^2 ≤ max (b^2 - (n : ℝ)*a^2) 0 := by
  exact entire_limit_strip
    (fun m => (shiftPolynomialIter a n (P.polynomial m)).differentiable)
    (shiftIter_entire a n hf) hnot
    (by simpa only [eval_shiftPolynomialIter] using shiftIter_convergence P.convergence a n)
    (fun m w hw => shiftPolynomialIter_strip _ (P.nonzero m) (P.conj m)
      ha (P.strip m) n hw) hz

/-- Second limit: any locally uniform limit of finite shifts inherits a common
contracted strip bound. The shift counts and amplitudes may vary independently. -/
theorem StripPolynomialApproximation.heat_limit_strip {f g : ℂ → ℂ} {b c : ℝ}
    (P : StripPolynomialApproximation f b) (hf : Differentiable ℂ f)
    (hg : Differentiable ℂ g) {a : ℕ → ℝ} {n : ℕ → ℕ}
    (ha : ∀ k, 0 < a k)
    (hbudget : ∀ k, max (b^2 - (n k : ℝ)*(a k)^2) 0 ≤ c^2)
    (hshift : ∀ k, ∃ w, shiftIter (a k) (n k) f w ≠ 0)
    (hnot : ∃ w, g w ≠ 0)
    (hlim : TendstoLocallyUniformly (fun k => shiftIter (a k) (n k) f) g atTop)
    {z : ℂ} (hz : g z = 0) : z.im^2 ≤ c^2 := by
  exact entire_limit_strip (fun k => shiftIter_entire _ _ hf) hg hnot hlim
    (fun k w hw => (P.shift_strip hf (ha k) (n k) (hshift k) hw).trans (hbudget k)) hz

/-- Covering the initial squared strip budget gives only real zeros after both
limits. This includes preservation of a zero-width strip. -/
theorem StripPolynomialApproximation.heat_limit_real {f g : ℂ → ℂ} {b : ℝ}
    (P : StripPolynomialApproximation f b) (hf : Differentiable ℂ f)
    (hg : Differentiable ℂ g) {a : ℕ → ℝ} {n : ℕ → ℕ}
    (ha : ∀ k, 0 < a k) (hbudget : ∀ k, b^2 ≤ (n k : ℝ)*(a k)^2)
    (hshift : ∀ k, ∃ w, shiftIter (a k) (n k) f w ≠ 0)
    (hnot : ∃ w, g w ≠ 0)
    (hlim : TendstoLocallyUniformly (fun k => shiftIter (a k) (n k) f) g atTop)
    {z : ℂ} (hz : g z = 0) : z.im = 0 := by
  have h := P.heat_limit_strip (c := 0) hf hg ha
    (fun k => by simpa using sub_nonpos.mpr (hbudget k)) hshift hnot hlim hz
  nlinarith [sq_nonneg z.im]

end LeanCert.Analysis.DBN
