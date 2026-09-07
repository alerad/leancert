import LeanCert.Analysis.DBN.Hadamard
import Mathlib.Util.AssertNoSorry

open LeanCert.Analysis.DBN Complex Complex.Hadamard

example : EntireOfOrderAtMost (3/2) (H 0) := H_zero_order
example : ∃ P : Polynomial ℂ, P.degree ≤ 1 ∧ ∀ z : ℂ,
    H 0 z = Complex.exp (P.eval z) * divisorCanonicalProduct 1 (H 0) Set.univ z :=
  H_zero_hadamard

assert_no_sorry hadamard_factorization_of_order
assert_no_sorry H_zero_norm_le_exp_order
assert_no_sorry H_zero_hadamard
assert_no_sorry H_zero_inverse_square_summable
assert_no_sorry H_zero_canonicalProduct_convergence
/-- info: 'Complex.Hadamard.hadamard_factorization_of_order' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms hadamard_factorization_of_order
/-- info: 'LeanCert.Analysis.DBN.H_zero_hadamard' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms H_zero_hadamard
/-- info: 'LeanCert.Analysis.DBN.H_zero_inverse_square_summable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms H_zero_inverse_square_summable
/-- info: 'LeanCert.Analysis.DBN.H_zero_canonicalProduct_convergence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms H_zero_canonicalProduct_convergence
