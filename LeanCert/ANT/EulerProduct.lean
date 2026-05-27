/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.ANT.Step
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# Finite Euler-product and log-product certificates

This module certifies finite products by rational factor envelopes and finite
log-products by rational logarithm envelopes.
-/

namespace LeanCert.ANT

open scoped BigOperators

/-- Prime numbers up to `N`. -/
def primesLE (N : Nat) : Finset Nat :=
  (Finset.range (N + 1)).filter Nat.Prime

/-- Rational lower endpoint of a finite product certificate. -/
def productLowerRat (S : Finset Nat) (lo : Nat → ℚ) : ℚ :=
  ∏ n ∈ S, lo n

/-- Rational upper endpoint of a finite product certificate. -/
def productUpperRat (S : Finset Nat) (hi : Nat → ℚ) : ℚ :=
  ∏ n ∈ S, hi n

/-- Semantic finite product. -/
noncomputable def finiteProduct (S : Finset Nat) (g : Nat → ℝ) : ℝ :=
  ∏ n ∈ S, g n

/-- Lower product certificate from pointwise nonnegative factor envelopes. -/
theorem productLowerRat_le_finiteProduct
    (S : Finset Nat) (g : Nat → ℝ) (lo : Nat → ℚ)
    (hlo_nonneg : ∀ n ∈ S, 0 ≤ lo n)
    (hlo : ∀ n ∈ S, (lo n : ℝ) ≤ g n) :
    (productLowerRat S lo : ℝ) ≤ finiteProduct S g := by
  unfold productLowerRat finiteProduct
  rw [Rat.cast_prod]
  exact Finset.prod_le_prod (fun n hn => by exact_mod_cast hlo_nonneg n hn) hlo

/-- Upper product certificate from pointwise nonnegative factor envelopes. -/
theorem finiteProduct_le_productUpperRat
    (S : Finset Nat) (g : Nat → ℝ) (lo hi : Nat → ℚ)
    (hlo_nonneg : ∀ n ∈ S, 0 ≤ lo n)
    (hlo : ∀ n ∈ S, (lo n : ℝ) ≤ g n)
    (hhi : ∀ n ∈ S, g n ≤ (hi n : ℝ)) :
    finiteProduct S g ≤ (productUpperRat S hi : ℝ) := by
  unfold productUpperRat finiteProduct
  rw [Rat.cast_prod]
  exact Finset.prod_le_prod
    (fun n hn => by
      have hlo0 : (0 : ℝ) ≤ (lo n : ℝ) := by exact_mod_cast hlo_nonneg n hn
      exact hlo0.trans (hlo n hn))
    hhi

/-- Boolean interval checker for finite product certificates. -/
def checkEulerProductInterval (S : Finset Nat) (lo hi : Nat → ℚ)
    (targetLo targetHi : ℚ) : Bool :=
  decide (targetLo ≤ productLowerRat S lo) &&
    decide (productUpperRat S hi ≤ targetHi)

/-- Golden theorem for finite Euler-product interval certificates. -/
theorem verify_eulerProduct_interval
    (S : Finset Nat) (g : Nat → ℝ) (lo hi : Nat → ℚ)
    (hlo_nonneg : ∀ n ∈ S, 0 ≤ lo n)
    (hlo : ∀ n ∈ S, (lo n : ℝ) ≤ g n)
    (hhi : ∀ n ∈ S, g n ≤ (hi n : ℝ))
    (targetLo targetHi : ℚ)
    (hcheck : checkEulerProductInterval S lo hi targetLo targetHi = true) :
    (targetLo : ℝ) ≤ finiteProduct S g ∧ finiteProduct S g ≤ (targetHi : ℝ) := by
  simp only [checkEulerProductInterval, Bool.and_eq_true, decide_eq_true_eq] at hcheck
  have htargetLo : (targetLo : ℝ) ≤ (productLowerRat S lo : ℝ) := by
    exact_mod_cast hcheck.1
  have htargetHi : (productUpperRat S hi : ℝ) ≤ (targetHi : ℝ) := by
    exact_mod_cast hcheck.2
  exact ⟨htargetLo.trans (productLowerRat_le_finiteProduct S g lo hlo_nonneg hlo),
    (finiteProduct_le_productUpperRat S g lo hi hlo_nonneg hlo hhi).trans
      htargetHi⟩

/-- Semantic finite log-product, represented as a sum of logs. -/
noncomputable def finiteLogProduct (S : Finset Nat) (g : Nat → ℝ) : ℝ :=
  ∑ n ∈ S, Real.log (g n)

/-- Rational lower endpoint of a finite log-product certificate. -/
def logProductLowerRat (S : Finset Nat) (lo : Nat → ℚ) : ℚ :=
  ∑ n ∈ S, lo n

/-- Rational upper endpoint of a finite log-product certificate. -/
def logProductUpperRat (S : Finset Nat) (hi : Nat → ℚ) : ℚ :=
  ∑ n ∈ S, hi n

/-- Lower log-product certificate from pointwise logarithm envelopes. -/
theorem logProductLowerRat_le_finiteLogProduct
    (S : Finset Nat) (g : Nat → ℝ) (lo : Nat → ℚ)
    (hlo : ∀ n ∈ S, (lo n : ℝ) ≤ Real.log (g n)) :
    (logProductLowerRat S lo : ℝ) ≤ finiteLogProduct S g := by
  unfold logProductLowerRat finiteLogProduct
  rw [Rat.cast_sum]
  exact Finset.sum_le_sum hlo

/-- Upper log-product certificate from pointwise logarithm envelopes. -/
theorem finiteLogProduct_le_logProductUpperRat
    (S : Finset Nat) (g : Nat → ℝ) (hi : Nat → ℚ)
    (hhi : ∀ n ∈ S, Real.log (g n) ≤ (hi n : ℝ)) :
    finiteLogProduct S g ≤ (logProductUpperRat S hi : ℝ) := by
  unfold logProductUpperRat finiteLogProduct
  rw [Rat.cast_sum]
  exact Finset.sum_le_sum hhi

/-- Boolean interval checker for finite log-product certificates. -/
def checkLogProductInterval (S : Finset Nat) (lo hi : Nat → ℚ)
    (targetLo targetHi : ℚ) : Bool :=
  decide (targetLo ≤ logProductLowerRat S lo) &&
    decide (logProductUpperRat S hi ≤ targetHi)

/-- Golden theorem for finite log-product interval certificates. -/
theorem verify_logProduct_interval
    (S : Finset Nat) (g : Nat → ℝ) (lo hi : Nat → ℚ)
    (hlo : ∀ n ∈ S, (lo n : ℝ) ≤ Real.log (g n))
    (hhi : ∀ n ∈ S, Real.log (g n) ≤ (hi n : ℝ))
    (targetLo targetHi : ℚ)
    (hcheck : checkLogProductInterval S lo hi targetLo targetHi = true) :
    (targetLo : ℝ) ≤ finiteLogProduct S g ∧
      finiteLogProduct S g ≤ (targetHi : ℝ) := by
  simp only [checkLogProductInterval, Bool.and_eq_true, decide_eq_true_eq] at hcheck
  have htargetLo : (targetLo : ℝ) ≤ (logProductLowerRat S lo : ℝ) := by
    exact_mod_cast hcheck.1
  have htargetHi : (logProductUpperRat S hi : ℝ) ≤ (targetHi : ℝ) := by
    exact_mod_cast hcheck.2
  exact ⟨htargetLo.trans (logProductLowerRat_le_finiteLogProduct S g lo hlo),
    (finiteLogProduct_le_logProductUpperRat S g hi hhi).trans htargetHi⟩

/-- Positive finite products are exponentials of their finite log-products. -/
theorem finiteProduct_eq_exp_finiteLogProduct
    (S : Finset Nat) (g : Nat → ℝ)
    (hpos : ∀ n ∈ S, 0 < g n) :
    finiteProduct S g = Real.exp (finiteLogProduct S g) := by
  unfold finiteProduct finiteLogProduct
  have hprod_pos : 0 < ∏ n ∈ S, g n := Finset.prod_pos hpos
  have hlog : Real.log (∏ n ∈ S, g n) = ∑ n ∈ S, Real.log (g n) := by
    rw [Real.log_prod]
    intro n hn
    exact ne_of_gt (hpos n hn)
  calc
    ∏ n ∈ S, g n = Real.exp (Real.log (∏ n ∈ S, g n)) := by
      rw [Real.exp_log hprod_pos]
    _ = Real.exp (∑ n ∈ S, Real.log (g n)) := by rw [hlog]

/-- Convert a certified log-product interval into an exponential product interval. -/
theorem verify_product_interval_of_log_interval
    (S : Finset Nat) (g : Nat → ℝ) (lo hi : ℚ)
    (hpos : ∀ n ∈ S, 0 < g n)
    (hlog : (lo : ℝ) ≤ finiteLogProduct S g ∧ finiteLogProduct S g ≤ (hi : ℝ)) :
    Real.exp (lo : ℝ) ≤ finiteProduct S g ∧
      finiteProduct S g ≤ Real.exp (hi : ℝ) := by
  rw [finiteProduct_eq_exp_finiteLogProduct S g hpos]
  exact ⟨Real.exp_le_exp.mpr hlog.1, Real.exp_le_exp.mpr hlog.2⟩

/-! ### Prime Euler-product presets -/

/-- Rational factor `1 - 1/n`. -/
def oneMinusInvRat (n : Nat) : ℚ :=
  1 - 1 / (n : ℚ)

/-- Rational factor `1 + 1/n`. -/
def onePlusInvRat (n : Nat) : ℚ :=
  1 + 1 / (n : ℚ)

/-- Finite prime product `∏_{p ≤ N} (1 - 1/p)`. -/
noncomputable def primeEulerOneMinusInv (N : Nat) : ℝ :=
  finiteProduct (primesLE N) fun p => (1 : ℝ) - 1 / (p : ℝ)

/-- Exact rational value of `∏_{p ≤ N} (1 - 1/p)`. -/
def primeEulerOneMinusInvRat (N : Nat) : ℚ :=
  productLowerRat (primesLE N) oneMinusInvRat

/-- Finite prime product `∏_{p ≤ N} (1 + 1/p)`. -/
noncomputable def primeEulerOnePlusInv (N : Nat) : ℝ :=
  finiteProduct (primesLE N) fun p => (1 : ℝ) + 1 / (p : ℝ)

/-- Exact rational value of `∏_{p ≤ N} (1 + 1/p)`. -/
def primeEulerOnePlusInvRat (N : Nat) : ℚ :=
  productLowerRat (primesLE N) onePlusInvRat

private theorem prime_of_mem_primesLE {N p : Nat} (hp : p ∈ primesLE N) :
    Nat.Prime p := by
  have hp' := hp
  simp only [primesLE, Finset.mem_filter, Finset.mem_range] at hp'
  exact hp'.2

private theorem oneMinusInvRat_nonneg_of_prime {p : Nat} (hp : Nat.Prime p) :
    0 ≤ oneMinusInvRat p := by
  unfold oneMinusInvRat
  have hp_pos : (0 : ℚ) < p := by exact_mod_cast hp.pos
  have hp_one : (1 : ℚ) ≤ p := by exact_mod_cast hp.one_le
  have hinv' : (1 : ℚ) / p ≤ (p : ℚ) / p :=
    div_le_div_of_nonneg_right hp_one (le_of_lt hp_pos)
  have hinv : (1 / (p : ℚ)) ≤ 1 := by
    simpa [div_self (ne_of_gt hp_pos)] using hinv'
  linarith

private theorem oneMinusInvRat_cast_eq {p : Nat} (hp : Nat.Prime p) :
    (oneMinusInvRat p : ℝ) = (1 : ℝ) - 1 / (p : ℝ) := by
  unfold oneMinusInvRat
  have hp_ne : (p : ℚ) ≠ 0 := by exact_mod_cast hp.pos.ne'
  norm_num [Rat.cast_div, hp_ne]

private theorem onePlusInvRat_cast_eq {p : Nat} (hp : Nat.Prime p) :
    (onePlusInvRat p : ℝ) = (1 : ℝ) + 1 / (p : ℝ) := by
  unfold onePlusInvRat
  have hp_ne : (p : ℚ) ≠ 0 := by exact_mod_cast hp.pos.ne'
  norm_num [Rat.cast_div, hp_ne]

/-- Boolean interval checker for `∏_{p ≤ N} (1 - 1/p)`. -/
def checkPrimeEulerOneMinusInvInterval (N : Nat) (lo hi : ℚ) : Bool :=
  decide (lo ≤ primeEulerOneMinusInvRat N) &&
    decide (primeEulerOneMinusInvRat N ≤ hi)

/-- Boolean interval checker for `∏_{p ≤ N} (1 + 1/p)`. -/
def checkPrimeEulerOnePlusInvInterval (N : Nat) (lo hi : ℚ) : Bool :=
  decide (lo ≤ primeEulerOnePlusInvRat N) &&
    decide (primeEulerOnePlusInvRat N ≤ hi)

/-- Golden theorem for finite prime products `∏_{p ≤ N} (1 - 1/p)`. -/
theorem verify_primeEulerOneMinusInv_interval (N : Nat) (lo hi : ℚ)
    (hcheck : checkPrimeEulerOneMinusInvInterval N lo hi = true) :
    (lo : ℝ) ≤ primeEulerOneMinusInv N ∧
      primeEulerOneMinusInv N ≤ (hi : ℝ) := by
  unfold checkPrimeEulerOneMinusInvInterval at hcheck
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hcheck
  unfold primeEulerOneMinusInvRat at hcheck
  have hprod := verify_eulerProduct_interval (primesLE N)
    (fun p => (1 : ℝ) - 1 / (p : ℝ)) oneMinusInvRat oneMinusInvRat
    (fun p hp => oneMinusInvRat_nonneg_of_prime (prime_of_mem_primesLE hp))
    (fun p hp => by rw [oneMinusInvRat_cast_eq (prime_of_mem_primesLE hp)])
    (fun p hp => by rw [oneMinusInvRat_cast_eq (prime_of_mem_primesLE hp)])
    lo hi
  have hgeneric :
      checkEulerProductInterval (primesLE N) oneMinusInvRat oneMinusInvRat lo hi = true := by
    simpa [checkEulerProductInterval, productUpperRat, productLowerRat] using hcheck
  simpa [primeEulerOneMinusInv] using hprod hgeneric

/-- Golden theorem for finite prime products `∏_{p ≤ N} (1 + 1/p)`. -/
theorem verify_primeEulerOnePlusInv_interval (N : Nat) (lo hi : ℚ)
    (hcheck : checkPrimeEulerOnePlusInvInterval N lo hi = true) :
    (lo : ℝ) ≤ primeEulerOnePlusInv N ∧
      primeEulerOnePlusInv N ≤ (hi : ℝ) := by
  unfold checkPrimeEulerOnePlusInvInterval at hcheck
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hcheck
  unfold primeEulerOnePlusInvRat at hcheck
  have hprod := verify_eulerProduct_interval (primesLE N)
    (fun p => (1 : ℝ) + 1 / (p : ℝ)) onePlusInvRat onePlusInvRat
    (fun p hp => by unfold onePlusInvRat; positivity)
    (fun p hp => by rw [onePlusInvRat_cast_eq (prime_of_mem_primesLE hp)])
    (fun p hp => by rw [onePlusInvRat_cast_eq (prime_of_mem_primesLE hp)])
    lo hi
  have hgeneric :
      checkEulerProductInterval (primesLE N) onePlusInvRat onePlusInvRat lo hi = true := by
    simpa [checkEulerProductInterval, productUpperRat, productLowerRat] using hcheck
  simpa [primeEulerOnePlusInv] using hprod hgeneric

end LeanCert.ANT
