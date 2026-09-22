/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.QProduct
import LeanCert.Validity

/-!
# 26 decimal digits of the prime q-product constant (Heavy tier)

Primes up to `2003` (shift index `2001`, tail exponent `2005`) enclose
`primeLambda = ∫₀¹ ∏ₚ (1 - uᵖ) du` (OEIS A395518) to 26 decimal places. The
product polynomial has degree `279053`; one `native_decide` evaluates the
sparse truncation and its odd-tail correction exactly (about two minutes).
-/

open LeanCert.QProduct LeanCert.Validity

set_option maxRecDepth 100000 in
theorem primeLambda_digits26 :
    ((5506530112728429635779717568 / 10 ^ 28 : ℚ) : ℝ) ≤ primeLambda ∧
      primeLambda ≤ ((5506530112728429635779717572 / 10 ^ 28 : ℚ) : ℝ) :=
  verify_limit_interval primeLambda_le_shiftedTruncSparse
    shiftedTruncSparse_sub_tail_le_primeLambda 2001
    (5506530112728429635779717568 / 10 ^ 28) (5506530112728429635779717572 / 10 ^ 28)
    (by native_decide)
