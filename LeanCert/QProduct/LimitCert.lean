/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.QProduct.PrimeLambda
import LeanCert.Validity.DirectedLimit

/-!
# Directed-limit certificate for the prime q-product limit

Packages the prime sandwich (`primeLambda_sandwich`) as a
`LeanCert.Validity.DirectedLimitCert`, so two-sided rational bounds on
`primeLambda` become a single `checkLimitInterval` evaluation — no per-bound
`∀ M` tail hypothesis at the use site.

The truncation index is shifted by two (`approx N = primeFRat (N + 2)`) so
the sandwich's `2 ≤ N` side condition holds at every index, and the tail
exponent `oddAbove (N + 2)` is the least odd number exceeded by every prime
beyond the truncation, discharging the sandwich's parity and tail-size
hypotheses uniformly.
-/

namespace LeanCert.QProduct

/-- The least odd number `> N` (so every odd number `> N`, in particular
every prime `> max N 2`, is at least this). -/
def oddAbove (N : ℕ) : ℕ :=
  if N % 2 = 0 then N + 1 else N + 2

theorem oddAbove_odd (N : ℕ) : Odd (oddAbove N) := by
  unfold oddAbove
  rw [Nat.odd_iff]
  split <;> omega

theorem le_oddAbove_of_prime_gt {N p : ℕ} (hN : 2 ≤ N)
    (hp : Nat.Prime p) (hgt : N < p) : oddAbove N ≤ p := by
  have hp2 : p ≠ 2 := by omega
  have hodd : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two hp2)
  unfold oddAbove
  split <;> omega

/-- Shifted truncations bound `primeLambda` from above. -/
theorem primeLambda_le_shiftedTrunc (N : ℕ) :
    primeLambda ≤ (primeFRat (N + 2) : ℝ) :=
  primeLambda_le_trunc (N + 2)

/-- Tail-corrected shifted truncations bound `primeLambda` from below. -/
theorem shiftedTrunc_sub_tail_le_primeLambda (N : ℕ) :
    (primeFRat (N + 2) : ℝ) -
        (primeSandwichErrorRat (N + 2) (oddAbove (N + 2)) : ℝ) ≤
      primeLambda :=
  (primeLambda_sandwich (by omega) (oddAbove_odd _)
    (fun p hp hgt => le_oddAbove_of_prime_gt (by omega) hp hgt)).1

/-- The prime q-product directed limit as a `DirectedLimitCert`. -/
noncomputable def primeLambdaLimitCert : Validity.DirectedLimitCert where
  approx N := primeFRat (N + 2)
  tail N := primeSandwichErrorRat (N + 2) (oddAbove (N + 2))
  limit := primeLambda
  limit_le_approx := primeLambda_le_shiftedTrunc
  approx_sub_tail_le_limit := shiftedTrunc_sub_tail_le_primeLambda

end LeanCert.QProduct
