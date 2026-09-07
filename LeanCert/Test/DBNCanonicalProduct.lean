import LeanCert.Analysis.DBN.CanonicalProduct
import Mathlib.Util.AssertNoSorry

open LeanCert.Analysis.DBN Complex Complex.Hadamard Polynomial

example (z : ℂ) : H 0 z = H 0 0 * divisorCanonicalProduct 1 (H 0) Set.univ z :=
  H_zero_eq_normalized_canonicalProduct z
example : deriv (H 0) 0 = 0 := H_zero_deriv_zero
example : deriv (divisorCanonicalProduct 1 (H 0) Set.univ) 0 = 0 :=
  H_zero_canonicalProduct_deriv_zero
example (roots : Multiset ℂ) :
    (roots.map (fun r => (1 : ℂ[X]) - C r⁻¹ * X)).prod.eval 0 = 1 :=
  finite_rootPolynomial_at_zero roots
-- Repeated roots are retained; the empty root multiset gives the constant one.
example {r : ℂ} (hr : r ≠ 0) :
    (({r, r} : Multiset ℂ).map (fun w => (1 : ℂ[X]) - C w⁻¹ * X)).prod.eval r = 0 := by
  apply (finite_rootPolynomial_zero_iff _ (by simpa using hr) r).mpr
  simp
example (z : ℂ) :
    ((0 : Multiset ℂ).map (fun r => (1 : ℂ[X]) - C r⁻¹ * X)).prod.eval z = 1 := by simp

assert_no_sorry H_zero_eq_normalized_canonicalProduct
assert_no_sorry H_zero_analyticOrder_neg
assert_no_sorry balanced_canonicalProduct_eq_polynomial
assert_no_sorry finite_rootPolynomial_zero_iff
assert_no_sorry finite_rootPolynomial_conj
assert_no_sorry finite_rootPolynomial_strip
/-- info: 'LeanCert.Analysis.DBN.H_zero_eq_normalized_canonicalProduct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms H_zero_eq_normalized_canonicalProduct
/-- info: 'LeanCert.Analysis.DBN.balanced_canonicalProduct_eq_polynomial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms balanced_canonicalProduct_eq_polynomial
/-- info: 'LeanCert.Analysis.DBN.finite_rootPolynomial_strip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms finite_rootPolynomial_strip
