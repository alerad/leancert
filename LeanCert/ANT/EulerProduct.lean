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

end LeanCert.ANT
