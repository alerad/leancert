/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.QProduct
import LeanCert.Validity

/-!
# Sparse q-product integral tests

The sparse `QPoly` evaluation agrees with the powerset expansion, and the
sparse prime truncations certify digits of `primeLambda` at scales the
powerset form cannot reach.
-/

open LeanCert.QProduct LeanCert.Validity

/-! ## Agreement with the powerset evaluation -/

example : finiteIntegralRatSparse {2, 3} = 7 / 12 := by native_decide

example : finiteIntegralRatSparse {2, 3} = finiteIntegralRat {2, 3} := by
  native_decide

example : primeFRatSparse 13 = primeFRat 13 := by native_decide

example : primeSandwichErrorRatSparse 13 15 = primeSandwichErrorRat 13 15 := by
  native_decide

example : momentRatSparse {2, 3, 5} 4 = momentRat {2, 3, 5} 4 := by native_decide

/-- `∫₀^{1/2} (1 - u²)(1 - u³) du = 57/128`. -/
example : truncatedIntegralRat {2, 3} (1 / 2) = 57 / 128 := by native_decide

example : (truncatedIntegralRat {2, 3} (1 / 2) : ℝ) =
    ∫ u in (0 : ℝ)..((1 / 2 : ℚ) : ℝ), qProd {2, 3} u :=
  truncatedIntegralRat_correct _ _

/-! ## Digits of the prime constant

Primes up to `503` (shift index `501`) certify 19 decimal digits in a few
seconds; the powerset evaluation would need `2^97` terms. -/

set_option maxRecDepth 100000 in
theorem primeLambda_digits19 :
    ((5506530112728420906 / 10 ^ 19 : ℚ) : ℝ) ≤ primeLambda ∧
      primeLambda ≤ ((5506530112728432345 / 10 ^ 19 : ℚ) : ℝ) :=
  verify_limit_interval primeLambda_le_shiftedTruncSparse
    shiftedTruncSparse_sub_tail_le_primeLambda 501
    (5506530112728420906 / 10 ^ 19) (5506530112728432345 / 10 ^ 19)
    (by native_decide)

/-- The packaged certificate carries the same two inequality families. -/
example : primeLambdaLimitCertSparse.limit = primeLambda := rfl
