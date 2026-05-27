/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.ANT.EulerProduct
import LeanCert.Engine.ChebyshevTheta

/-!
# Finite Mertens-style certificates

This module connects the existing Chebyshev theta log enclosures to finite
prime-weighted sums that occur in Mertens/Euler-product arguments.
-/

namespace LeanCert.ANT

open scoped BigOperators
open LeanCert.Engine.ChebyshevTheta

/-- Semantic finite Mertens log sum `∑_{p ≤ N} log p / p`. -/
noncomputable def mertensLogSum (N : Nat) : ℝ :=
  ∑ p ∈ primesLE N, Real.log p / (p : ℝ)

/-- Rational lower endpoint for `∑_{p ≤ N} log p / p`. -/
def mertensLogSumLowerRat (N depth : Nat) : ℚ :=
  ∑ p ∈ primesLE N, logPrimeLB p depth / (p : ℚ)

/-- Rational upper endpoint for `∑_{p ≤ N} log p / p`. -/
def mertensLogSumUpperRat (N depth : Nat) : ℚ :=
  ∑ p ∈ primesLE N, logPrimeUB p depth / (p : ℚ)

private theorem prime_pos_of_mem_primesLE {N p : Nat} (hp : p ∈ primesLE N) :
    0 < p := by
  simp only [primesLE, Finset.mem_filter, Finset.mem_range] at hp
  exact hp.2.pos

/-- Lower correctness for the finite Mertens log-sum certificate. -/
theorem mertensLogSumLowerRat_le (N depth : Nat) :
    (mertensLogSumLowerRat N depth : ℝ) ≤ mertensLogSum N := by
  unfold mertensLogSumLowerRat mertensLogSum
  rw [Rat.cast_sum]
  apply Finset.sum_le_sum
  intro p hp
  have hlog := logPrimeLB_le_log_prime p depth
  have hpPrime : Nat.Prime p := by
    have hp' := hp
    simp only [primesLE, Finset.mem_filter, Finset.mem_range] at hp'
    exact hp'.2
  have hp_pos_real : (0 : ℝ) < p := by exact_mod_cast hpPrime.pos
  have hp_pos_rat : (0 : ℚ) < p := by exact_mod_cast hpPrime.pos
  simp [hpPrime] at hlog
  have hdiv := div_le_div_of_nonneg_right hlog (le_of_lt hp_pos_real)
  simpa [Rat.cast_div, ne_of_gt hp_pos_rat, div_eq_mul_inv] using hdiv

/-- Upper correctness for the finite Mertens log-sum certificate. -/
theorem mertensLogSum_le_mertensLogSumUpperRat (N depth : Nat) :
    mertensLogSum N ≤ (mertensLogSumUpperRat N depth : ℝ) := by
  unfold mertensLogSumUpperRat mertensLogSum
  rw [Rat.cast_sum]
  apply Finset.sum_le_sum
  intro p hp
  have hlog := log_prime_le_logPrimeUB p depth
  have hpPrime : Nat.Prime p := by
    have hp' := hp
    simp only [primesLE, Finset.mem_filter, Finset.mem_range] at hp'
    exact hp'.2
  have hp_pos_real : (0 : ℝ) < p := by exact_mod_cast hpPrime.pos
  have hp_pos_rat : (0 : ℚ) < p := by exact_mod_cast hpPrime.pos
  simp [hpPrime] at hlog
  have hdiv := div_le_div_of_nonneg_right hlog (le_of_lt hp_pos_real)
  simpa [Rat.cast_div, ne_of_gt hp_pos_rat, div_eq_mul_inv] using hdiv

/-- Boolean interval checker for finite Mertens log sums. -/
def checkMertensLogSumInterval (N depth : Nat) (lo hi : ℚ) : Bool :=
  decide (lo ≤ mertensLogSumLowerRat N depth) &&
    decide (mertensLogSumUpperRat N depth ≤ hi)

/-- Golden theorem for finite Mertens log-sum certificates. -/
theorem verify_mertensLogSum_interval (N depth : Nat) (lo hi : ℚ)
    (hcheck : checkMertensLogSumInterval N depth lo hi = true) :
    (lo : ℝ) ≤ mertensLogSum N ∧ mertensLogSum N ≤ (hi : ℝ) := by
  simp only [checkMertensLogSumInterval, Bool.and_eq_true, decide_eq_true_eq] at hcheck
  have hlo : (lo : ℝ) ≤ (mertensLogSumLowerRat N depth : ℝ) := by
    exact_mod_cast hcheck.1
  have hhi : (mertensLogSumUpperRat N depth : ℝ) ≤ (hi : ℝ) := by
    exact_mod_cast hcheck.2
  exact ⟨hlo.trans (mertensLogSumLowerRat_le N depth),
    (mertensLogSum_le_mertensLogSumUpperRat N depth).trans hhi⟩

end LeanCert.ANT
