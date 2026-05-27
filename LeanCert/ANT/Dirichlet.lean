/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.ANT.PrimeEuler
import LeanCert.Engine.ChebyshevTheta

/-!
# Certified finite Dirichlet-series truncations

This module certifies finite sums of the form

`∑ n ∈ S, a n * w n`

from rational interval enclosures for the coefficients `a n` and weights `w n`.
The multiplication envelope is sign-aware, so the API works for signed
coefficients such as Möbius-like data as well as nonnegative prime weights.
-/

namespace LeanCert.ANT

open scoped BigOperators
open LeanCert.Engine.ChebyshevTheta

/-- Semantic finite Dirichlet-style weighted sum. -/
noncomputable def finiteDirichletSum
    (S : Finset Nat) (a w : Nat → ℝ) : ℝ :=
  ∑ n ∈ S, a n * w n

/-- Lower endpoint for multiplying a signed coefficient interval by a nonnegative weight interval. -/
def intervalMulLowerRat (aLo _aHi wLo wHi : ℚ) : ℚ :=
  if 0 ≤ aLo then aLo * wLo else aLo * wHi

/-- Upper endpoint for multiplying a signed coefficient interval by a nonnegative weight interval. -/
def intervalMulUpperRat (_aLo aHi wLo wHi : ℚ) : ℚ :=
  if 0 ≤ aHi then aHi * wHi else aHi * wLo

private theorem intervalMulLowerRat_le_mul {a w : ℝ} {aLo aHi wLo wHi : ℚ}
    (ha : (aLo : ℝ) ≤ a ∧ a ≤ (aHi : ℝ))
    (hw_nonneg : 0 ≤ wLo)
    (hw : (wLo : ℝ) ≤ w ∧ w ≤ (wHi : ℝ)) :
    (intervalMulLowerRat aLo aHi wLo wHi : ℝ) ≤ a * w := by
  unfold intervalMulLowerRat
  by_cases haLo_nonneg : 0 ≤ aLo
  · simp [haLo_nonneg]
    have hLo_nonneg : 0 ≤ (aLo : ℝ) := by exact_mod_cast haLo_nonneg
    have hwLo_nonneg : 0 ≤ (wLo : ℝ) := by exact_mod_cast hw_nonneg
    exact (mul_le_mul_of_nonneg_right ha.1 hwLo_nonneg).trans
      (mul_le_mul_of_nonneg_left hw.1 (hLo_nonneg.trans ha.1))
  · simp [haLo_nonneg]
    have haLo_nonpos : (aLo : ℝ) ≤ 0 := by exact_mod_cast le_of_not_ge haLo_nonneg
    have hw_nonneg_real : 0 ≤ w := (by exact_mod_cast hw_nonneg : (0 : ℝ) ≤ wLo).trans hw.1
    exact (mul_le_mul_of_nonpos_left hw.2 haLo_nonpos).trans
      (mul_le_mul_of_nonneg_right ha.1 hw_nonneg_real)

private theorem mul_le_intervalMulUpperRat {a w : ℝ} {aLo aHi wLo wHi : ℚ}
    (ha : (aLo : ℝ) ≤ a ∧ a ≤ (aHi : ℝ))
    (hw_nonneg : 0 ≤ wLo)
    (hw : (wLo : ℝ) ≤ w ∧ w ≤ (wHi : ℝ)) :
    a * w ≤ (intervalMulUpperRat aLo aHi wLo wHi : ℝ) := by
  unfold intervalMulUpperRat
  by_cases haHi_nonneg : 0 ≤ aHi
  · simp [haHi_nonneg]
    have hHi_nonneg : 0 ≤ (aHi : ℝ) := by exact_mod_cast haHi_nonneg
    have hw_nonneg_real : 0 ≤ w := (by exact_mod_cast hw_nonneg : (0 : ℝ) ≤ wLo).trans hw.1
    exact (mul_le_mul_of_nonneg_right ha.2 hw_nonneg_real).trans
      (mul_le_mul_of_nonneg_left hw.2 hHi_nonneg)
  · simp [haHi_nonneg]
    have haHi_nonpos : (aHi : ℝ) ≤ 0 := by exact_mod_cast le_of_not_ge haHi_nonneg
    have hw_nonneg_real : 0 ≤ w := (by exact_mod_cast hw_nonneg : (0 : ℝ) ≤ wLo).trans hw.1
    exact (mul_le_mul_of_nonneg_right ha.2 hw_nonneg_real).trans
      (mul_le_mul_of_nonpos_left hw.1 haHi_nonpos)

/-- Rational lower endpoint for a finite Dirichlet sum. -/
def finiteDirichletSumLowerRat
    (S : Finset Nat) (aLo aHi wLo wHi : Nat → ℚ) : ℚ :=
  ∑ n ∈ S, intervalMulLowerRat (aLo n) (aHi n) (wLo n) (wHi n)

/-- Rational upper endpoint for a finite Dirichlet sum. -/
def finiteDirichletSumUpperRat
    (S : Finset Nat) (aLo aHi wLo wHi : Nat → ℚ) : ℚ :=
  ∑ n ∈ S, intervalMulUpperRat (aLo n) (aHi n) (wLo n) (wHi n)

theorem finiteDirichletSumLowerRat_le
    (S : Finset Nat) (a w : Nat → ℝ) (aLo aHi wLo wHi : Nat → ℚ)
    (ha : ∀ n ∈ S, (aLo n : ℝ) ≤ a n ∧ a n ≤ (aHi n : ℝ))
    (hw_nonneg : ∀ n ∈ S, 0 ≤ wLo n)
    (hw : ∀ n ∈ S, (wLo n : ℝ) ≤ w n ∧ w n ≤ (wHi n : ℝ)) :
    (finiteDirichletSumLowerRat S aLo aHi wLo wHi : ℝ) ≤ finiteDirichletSum S a w := by
  unfold finiteDirichletSumLowerRat finiteDirichletSum
  rw [Rat.cast_sum]
  apply Finset.sum_le_sum
  intro n hn
  exact intervalMulLowerRat_le_mul (ha n hn) (hw_nonneg n hn) (hw n hn)

theorem finiteDirichletSum_le_upperRat
    (S : Finset Nat) (a w : Nat → ℝ) (aLo aHi wLo wHi : Nat → ℚ)
    (ha : ∀ n ∈ S, (aLo n : ℝ) ≤ a n ∧ a n ≤ (aHi n : ℝ))
    (hw_nonneg : ∀ n ∈ S, 0 ≤ wLo n)
    (hw : ∀ n ∈ S, (wLo n : ℝ) ≤ w n ∧ w n ≤ (wHi n : ℝ)) :
    finiteDirichletSum S a w ≤ (finiteDirichletSumUpperRat S aLo aHi wLo wHi : ℝ) := by
  unfold finiteDirichletSumUpperRat finiteDirichletSum
  rw [Rat.cast_sum]
  apply Finset.sum_le_sum
  intro n hn
  exact mul_le_intervalMulUpperRat (ha n hn) (hw_nonneg n hn) (hw n hn)

/-- Boolean interval checker for finite Dirichlet sums. -/
def checkDirichletSumInterval
    (S : Finset Nat) (aLo aHi wLo wHi : Nat → ℚ) (lo hi : ℚ) : Bool :=
  LeanCert.Cert.checkRatInterval
    (finiteDirichletSumLowerRat S aLo aHi wLo wHi)
    (finiteDirichletSumUpperRat S aLo aHi wLo wHi) lo hi

/-- Boolean lower checker for finite Dirichlet sums. -/
def checkDirichletSumLower
    (S : Finset Nat) (aLo aHi wLo wHi : Nat → ℚ) (lo : ℚ) : Bool :=
  LeanCert.Cert.checkRatLower
    (finiteDirichletSumLowerRat S aLo aHi wLo wHi) lo

/-- Boolean upper checker for finite Dirichlet sums. -/
def checkDirichletSumUpper
    (S : Finset Nat) (aLo aHi wLo wHi : Nat → ℚ) (hi : ℚ) : Bool :=
  LeanCert.Cert.checkRatUpper
    (finiteDirichletSumUpperRat S aLo aHi wLo wHi) hi

/-- Golden theorem for finite Dirichlet-sum interval certificates. -/
theorem verify_dirichletSum_interval
    (S : Finset Nat) (a w : Nat → ℝ) (aLo aHi wLo wHi : Nat → ℚ)
    (ha : ∀ n ∈ S, (aLo n : ℝ) ≤ a n ∧ a n ≤ (aHi n : ℝ))
    (hw_nonneg : ∀ n ∈ S, 0 ≤ wLo n)
    (hw : ∀ n ∈ S, (wLo n : ℝ) ≤ w n ∧ w n ≤ (wHi n : ℝ))
    (lo hi : ℚ)
    (hcheck : checkDirichletSumInterval S aLo aHi wLo wHi lo hi = true) :
    (lo : ℝ) ≤ finiteDirichletSum S a w ∧ finiteDirichletSum S a w ≤ (hi : ℝ) := by
  exact LeanCert.Cert.verify_rat_interval
    (finiteDirichletSumLowerRat_le S a w aLo aHi wLo wHi ha hw_nonneg hw)
    (finiteDirichletSum_le_upperRat S a w aLo aHi wLo wHi ha hw_nonneg hw)
    hcheck

/-- Golden theorem for finite Dirichlet-sum lower certificates. -/
theorem verify_dirichletSum_lower
    (S : Finset Nat) (a w : Nat → ℝ) (aLo aHi wLo wHi : Nat → ℚ)
    (ha : ∀ n ∈ S, (aLo n : ℝ) ≤ a n ∧ a n ≤ (aHi n : ℝ))
    (hw_nonneg : ∀ n ∈ S, 0 ≤ wLo n)
    (hw : ∀ n ∈ S, (wLo n : ℝ) ≤ w n ∧ w n ≤ (wHi n : ℝ))
    (lo : ℚ)
    (hcheck : checkDirichletSumLower S aLo aHi wLo wHi lo = true) :
    (lo : ℝ) ≤ finiteDirichletSum S a w := by
  exact LeanCert.Cert.verify_rat_lower
    (finiteDirichletSumLowerRat_le S a w aLo aHi wLo wHi ha hw_nonneg hw)
    hcheck

/-- Golden theorem for finite Dirichlet-sum upper certificates. -/
theorem verify_dirichletSum_upper
    (S : Finset Nat) (a w : Nat → ℝ) (aLo aHi wLo wHi : Nat → ℚ)
    (ha : ∀ n ∈ S, (aLo n : ℝ) ≤ a n ∧ a n ≤ (aHi n : ℝ))
    (hw_nonneg : ∀ n ∈ S, 0 ≤ wLo n)
    (hw : ∀ n ∈ S, (wLo n : ℝ) ≤ w n ∧ w n ≤ (wHi n : ℝ))
    (hi : ℚ)
    (hcheck : checkDirichletSumUpper S aLo aHi wLo wHi hi = true) :
    finiteDirichletSum S a w ≤ (hi : ℝ) := by
  exact LeanCert.Cert.verify_rat_upper
    (finiteDirichletSum_le_upperRat S a w aLo aHi wLo wHi ha hw_nonneg hw)
    hcheck

/-! ### Common finite Dirichlet truncation presets -/

/-- Natural numbers `1 ≤ n ≤ N`. -/
def naturalsIcc (N : Nat) : Finset Nat :=
  Finset.Icc 1 N

/-- Harmonic truncation `∑_{1 ≤ n ≤ N} 1/n`. -/
noncomputable def harmonicSum (N : Nat) : ℝ :=
  finiteDirichletSum (naturalsIcc N) (fun _ => (1 : ℝ)) fun n => 1 / (n : ℝ)

/-- Exact rational harmonic truncation. -/
def harmonicSumRat (N : Nat) : ℚ :=
  ∑ n ∈ naturalsIcc N, 1 / (n : ℚ)

/-- Prime harmonic truncation `∑_{p ≤ N} 1/p`. -/
noncomputable def primeHarmonicSum (N : Nat) : ℝ :=
  finiteDirichletSum (primesLE N) (fun _ => (1 : ℝ)) fun p => 1 / (p : ℝ)

/-- Exact rational prime harmonic truncation. -/
def primeHarmonicSumRat (N : Nat) : ℚ :=
  ∑ p ∈ primesLE N, 1 / (p : ℚ)

/-- Prime logarithmic Dirichlet truncation `∑_{p ≤ N} log p / p`. -/
noncomputable def logPrimeOverPrimeSum (N : Nat) : ℝ :=
  finiteDirichletSum (primesLE N) (fun p => Real.log p) fun p => 1 / (p : ℝ)

/-- Lower endpoint for `∑_{p ≤ N} log p / p`. -/
def logPrimeOverPrimeLowerRat (N depth : Nat) : ℚ :=
  ∑ p ∈ primesLE N, logPrimeLB p depth / (p : ℚ)

/-- Upper endpoint for `∑_{p ≤ N} log p / p`. -/
def logPrimeOverPrimeUpperRat (N depth : Nat) : ℚ :=
  ∑ p ∈ primesLE N, logPrimeUB p depth / (p : ℚ)

private theorem invNatRat_interval_of_pos {n : Nat} (hn : 0 < n) :
    ((1 / (n : ℚ) : ℚ) : ℝ) ≤ 1 / (n : ℝ) ∧
      1 / (n : ℝ) ≤ ((1 / (n : ℚ) : ℚ) : ℝ) := by
  have hnq : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  norm_num [Rat.cast_div, hnq]

theorem harmonicSum_eq_rat (N : Nat) :
    harmonicSum N = (harmonicSumRat N : ℝ) := by
  unfold harmonicSum harmonicSumRat finiteDirichletSum naturalsIcc
  rw [Rat.cast_sum]
  apply Finset.sum_congr rfl
  intro n hn
  have hn_pos : 0 < n := by
    simp only [Finset.mem_Icc] at hn
    exact hn.1
  have hnq : (n : ℚ) ≠ 0 := by exact_mod_cast hn_pos.ne'
  norm_num [Rat.cast_div, hnq]

theorem primeHarmonicSum_eq_rat (N : Nat) :
    primeHarmonicSum N = (primeHarmonicSumRat N : ℝ) := by
  unfold primeHarmonicSum primeHarmonicSumRat finiteDirichletSum
  rw [Rat.cast_sum]
  apply Finset.sum_congr rfl
  intro p hp
  have hp' := hp
  simp only [primesLE, Finset.mem_filter, Finset.mem_range] at hp'
  have hp_pos : 0 < p := hp'.2.pos
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hp_pos.ne'
  norm_num [Rat.cast_div, hpq]

/-- Boolean interval checker for harmonic truncations. -/
def checkHarmonicSumInterval (N : Nat) (lo hi : ℚ) : Bool :=
  LeanCert.Cert.checkRatInterval (harmonicSumRat N) (harmonicSumRat N) lo hi

/-- Boolean interval checker for prime harmonic truncations. -/
def checkPrimeHarmonicSumInterval (N : Nat) (lo hi : ℚ) : Bool :=
  LeanCert.Cert.checkRatInterval (primeHarmonicSumRat N) (primeHarmonicSumRat N) lo hi

/-- Boolean interval checker for `∑_{p ≤ N} log p / p`. -/
def checkLogPrimeOverPrimeSumInterval (N depth : Nat) (lo hi : ℚ) : Bool :=
  LeanCert.Cert.checkRatInterval (logPrimeOverPrimeLowerRat N depth)
    (logPrimeOverPrimeUpperRat N depth) lo hi

theorem logPrimeOverPrimeLowerRat_le (N depth : Nat) :
    (logPrimeOverPrimeLowerRat N depth : ℝ) ≤ logPrimeOverPrimeSum N := by
  unfold logPrimeOverPrimeLowerRat logPrimeOverPrimeSum finiteDirichletSum
  rw [Rat.cast_sum]
  apply Finset.sum_le_sum
  intro p hp
  have hp' := hp
  simp only [primesLE, Finset.mem_filter, Finset.mem_range] at hp'
  have hlog := logPrimeLB_le_log_prime p depth
  have hpos : (0 : ℝ) ≤ 1 / (p : ℝ) := by positivity
  simp [hp'.2] at hlog
  have h := mul_le_mul_of_nonneg_right hlog hpos
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hp'.2.pos.ne'
  simpa [Rat.cast_div, hpq, mul_div_assoc] using h

theorem logPrimeOverPrime_le_upperRat (N depth : Nat) :
    logPrimeOverPrimeSum N ≤ (logPrimeOverPrimeUpperRat N depth : ℝ) := by
  unfold logPrimeOverPrimeUpperRat logPrimeOverPrimeSum finiteDirichletSum
  rw [Rat.cast_sum]
  apply Finset.sum_le_sum
  intro p hp
  have hp' := hp
  simp only [primesLE, Finset.mem_filter, Finset.mem_range] at hp'
  have hlog := log_prime_le_logPrimeUB p depth
  have hpos : (0 : ℝ) ≤ 1 / (p : ℝ) := by positivity
  simp [hp'.2] at hlog
  have h := mul_le_mul_of_nonneg_right hlog hpos
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hp'.2.pos.ne'
  simpa [Rat.cast_div, hpq, mul_div_assoc] using h

theorem verify_harmonicSum_interval (N : Nat) (lo hi : ℚ)
    (hcheck : checkHarmonicSumInterval N lo hi = true) :
    (lo : ℝ) ≤ harmonicSum N ∧ harmonicSum N ≤ (hi : ℝ) := by
  rw [harmonicSum_eq_rat N]
  exact LeanCert.Cert.verify_rat_interval le_rfl le_rfl hcheck

theorem verify_primeHarmonicSum_interval (N : Nat) (lo hi : ℚ)
    (hcheck : checkPrimeHarmonicSumInterval N lo hi = true) :
    (lo : ℝ) ≤ primeHarmonicSum N ∧ primeHarmonicSum N ≤ (hi : ℝ) := by
  rw [primeHarmonicSum_eq_rat N]
  exact LeanCert.Cert.verify_rat_interval le_rfl le_rfl hcheck

theorem verify_logPrimeOverPrimeSum_interval (N depth : Nat) (lo hi : ℚ)
    (hcheck : checkLogPrimeOverPrimeSumInterval N depth lo hi = true) :
    (lo : ℝ) ≤ logPrimeOverPrimeSum N ∧ logPrimeOverPrimeSum N ≤ (hi : ℝ) := by
  exact LeanCert.Cert.verify_rat_interval (logPrimeOverPrimeLowerRat_le N depth)
    (logPrimeOverPrime_le_upperRat N depth) hcheck

end LeanCert.ANT
