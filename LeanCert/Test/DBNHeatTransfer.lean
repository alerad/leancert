import LeanCert.Analysis.DBN.RealZeros
import Mathlib.Util.AssertNoSorry

open LeanCert.Analysis.DBN Complex Complex.Hadamard Set Filter
open scoped Topology

-- No sign restriction on time: these are not merely forward-time statements.
example (t : ℝ) : EntireOfOrderAtMost (3/2) (H t) := H_order t
example : EntireOfOrderAtMost (3/2) (H (-100)) := H_order (-100)
example (t : ℝ) : ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ,
    ‖H t z‖ ≤ Real.exp (C*(1+‖z‖)^(3/2 : ℝ)) := H_norm_le_exp_order t
example (t : ℝ) : ∃ P : Polynomial ℂ, P.degree ≤ 1 ∧ ∀ z : ℂ,
    H t z = Complex.exp (P.eval z) * divisorCanonicalProduct 1 (H t) univ z :=
  H_hadamard t
example (t : ℝ) (z : ℂ) :
    H t z = H t 0 * divisorCanonicalProduct 1 (H t) univ z :=
  H_eq_normalized_canonicalProduct t z
example (t : ℝ) : deriv (H t) 0 = 0 := H_deriv_zero t
example (t a : ℝ) (n : ℕ) : shiftIter a n (H t) 0 ≠ 0 :=
  shiftIter_H_ne_zero t a n
-- Zero shifts and zero iterations are also covered by the integral positivity proof.
example (t : ℝ) : shiftIter 0 0 (H t) 0 ≠ 0 := shiftIter_H_ne_zero t 0 0
example : H_zero_stripApproximation.polynomial = HZeroPolynomial := rfl

-- The first transfer handles zero iterations and a zero-width strip.
example {f : ℂ → ℂ} (P : StripPolynomialApproximation f 0)
    (hf : Differentiable ℂ f) (hnot : ∃ w, f w ≠ 0)
    {z : ℂ} (hz : f z = 0) : z.im = 0 := by
  have h := P.shift_strip hf (a := 1) (by norm_num) 0 hnot hz
  norm_num at h
  nlinarith [sq_nonneg z.im]

-- Arbitrary amplitudes/counts and a nonzero target strip: no unit-budget restriction.
example {f g : ℂ → ℂ} {b c : ℝ} (P : StripPolynomialApproximation f b)
    (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    {a : ℕ → ℝ} {n : ℕ → ℕ} (ha : ∀ k, 0 < a k)
    (hb : ∀ k, max (b^2 - (n k : ℝ)*(a k)^2) 0 ≤ c^2)
    (hs : ∀ k, ∃ w, shiftIter (a k) (n k) f w ≠ 0)
    (hn : ∃ w, g w ≠ 0)
    (hl : TendstoLocallyUniformly (fun k => shiftIter (a k) (n k) f) g atTop)
    {z : ℂ} (hz : g z = 0) : z.im^2 ≤ c^2 :=
  P.heat_limit_strip hf hg ha hb hs hn hl hz

-- The actual endpoint now uses the reusable two-limit bridge internally.
example (z : ℂ) (hz : H (1/2) z = 0) : z.im = 0 := H_half_real_zeros z hz

assert_no_sorry heat_subquadratic_exponent
assert_no_sorry H_norm_le_exp_order
assert_no_sorry H_hadamard
assert_no_sorry H_inverse_square_summable
assert_no_sorry H_canonicalProduct_convergence
assert_no_sorry H_eq_normalized_canonicalProduct
assert_no_sorry shiftIter_H_ne_zero
assert_no_sorry entire_limit_strip
assert_no_sorry StripPolynomialApproximation.shift_strip
assert_no_sorry StripPolynomialApproximation.heat_limit_strip
assert_no_sorry StripPolynomialApproximation.heat_limit_real

/-- info: 'LeanCert.Analysis.DBN.H_hadamard' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms H_hadamard
/-- info: 'LeanCert.Analysis.DBN.H_eq_normalized_canonicalProduct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms H_eq_normalized_canonicalProduct
/-- info: 'LeanCert.Analysis.DBN.StripPolynomialApproximation.heat_limit_strip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms StripPolynomialApproximation.heat_limit_strip
/-- info: 'LeanCert.Analysis.DBN.StripPolynomialApproximation.heat_limit_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms StripPolynomialApproximation.heat_limit_real
