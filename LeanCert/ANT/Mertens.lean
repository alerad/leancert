/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.ANT.Abel
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

/-- Prime logarithm increment used by the Abel bridge. -/
noncomputable def thetaIncrement (n : Nat) : ℝ :=
  if n.Prime then Real.log n else 0

/-- Rational weight `1/n`. -/
def invNatRat (n : Nat) : ℚ :=
  1 / (n : ℚ)

/-- Lower prefix envelope for `thetaIncrement`. -/
def thetaPrefixLowerRat (depth k : Nat) : ℚ :=
  ∑ n ∈ Finset.range k, logPrimeLB n depth

/-- Upper prefix envelope for `thetaIncrement`. -/
def thetaPrefixUpperRat (depth k : Nat) : ℚ :=
  ∑ n ∈ Finset.range k, logPrimeUB n depth

/-- The Abel-side weighted sum for `∑_{p ≤ N} log p / p`. -/
noncomputable def mertensAbelSum (N : Nat) : ℝ :=
  weightedSum thetaIncrement invNatRat 2 (N + 1)

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

theorem thetaPrefixLowerRat_le_prefix (depth k : Nat) :
    (thetaPrefixLowerRat depth k : ℝ) ≤ prefixSum thetaIncrement k := by
  unfold thetaPrefixLowerRat prefixSum thetaIncrement
  rw [Rat.cast_sum]
  apply Finset.sum_le_sum
  intro n hn
  exact logPrimeLB_le_log_prime n depth

theorem prefix_le_thetaPrefixUpperRat (depth k : Nat) :
    prefixSum thetaIncrement k ≤ (thetaPrefixUpperRat depth k : ℝ) := by
  unfold thetaPrefixUpperRat prefixSum thetaIncrement
  rw [Rat.cast_sum]
  apply Finset.sum_le_sum
  intro n hn
  exact log_prime_le_logPrimeUB n depth

theorem thetaPrefix_envelope (depth : Nat) :
    ∀ k, (thetaPrefixLowerRat depth k : ℝ) ≤ prefixSum thetaIncrement k ∧
      prefixSum thetaIncrement k ≤ (thetaPrefixUpperRat depth k : ℝ) := by
  intro k
  exact ⟨thetaPrefixLowerRat_le_prefix depth k, prefix_le_thetaPrefixUpperRat depth k⟩

/-- Abel-bound checker for the Mertens log sum. -/
def checkMertensAbelInterval (N depth : Nat) (lo hi : ℚ) : Bool :=
  checkAbelBoundInterval invNatRat (thetaPrefixLowerRat depth)
    (thetaPrefixUpperRat depth) 2 (N + 1) lo hi

/-- Golden theorem for the Abel-certified Mertens weighted sum. -/
theorem verify_mertensAbel_interval {N depth : Nat} (hN : 2 < N + 1) (lo hi : ℚ)
    (hcheck : checkMertensAbelInterval N depth lo hi = true) :
    (lo : ℝ) ≤ mertensAbelSum N ∧ mertensAbelSum N ≤ (hi : ℝ) := by
  unfold checkMertensAbelInterval at hcheck
  unfold mertensAbelSum
  exact verify_abelBound_interval thetaIncrement invNatRat
    (thetaPrefixLowerRat depth) (thetaPrefixUpperRat depth) hN
    (thetaPrefix_envelope depth) lo hi hcheck

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
