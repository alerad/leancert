/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.ANT.Step
import LeanCert.Cert.Interval
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
  exact Finset.prod_le_prod₀ (fun n hn => by exact_mod_cast hlo_nonneg n hn) hlo

/-- Upper product certificate from pointwise nonnegative factor envelopes. -/
theorem finiteProduct_le_productUpperRat
    (S : Finset Nat) (g : Nat → ℝ) (lo hi : Nat → ℚ)
    (hlo_nonneg : ∀ n ∈ S, 0 ≤ lo n)
    (hlo : ∀ n ∈ S, (lo n : ℝ) ≤ g n)
    (hhi : ∀ n ∈ S, g n ≤ (hi n : ℝ)) :
    finiteProduct S g ≤ (productUpperRat S hi : ℝ) := by
  unfold productUpperRat finiteProduct
  rw [Rat.cast_prod]
  exact Finset.prod_le_prod₀
    (fun n hn => by
      have hlo0 : (0 : ℝ) ≤ (lo n : ℝ) := by exact_mod_cast hlo_nonneg n hn
      exact hlo0.trans (hlo n hn))
    hhi

/-- Boolean interval checker for finite product certificates. -/
def checkEulerProductInterval (S : Finset Nat) (lo hi : Nat → ℚ)
    (targetLo targetHi : ℚ) : Bool :=
  LeanCert.Cert.checkRatInterval (productLowerRat S lo) (productUpperRat S hi)
    targetLo targetHi

/-- Golden theorem for finite Euler-product interval certificates. -/
theorem verify_eulerProduct_interval
    (S : Finset Nat) (g : Nat → ℝ) (lo hi : Nat → ℚ)
    (hlo_nonneg : ∀ n ∈ S, 0 ≤ lo n)
    (hlo : ∀ n ∈ S, (lo n : ℝ) ≤ g n)
    (hhi : ∀ n ∈ S, g n ≤ (hi n : ℝ))
    (targetLo targetHi : ℚ)
    (hcheck : checkEulerProductInterval S lo hi targetLo targetHi = true) :
    (targetLo : ℝ) ≤ finiteProduct S g ∧ finiteProduct S g ≤ (targetHi : ℝ) := by
  exact LeanCert.Cert.verify_rat_interval
    (productLowerRat_le_finiteProduct S g lo hlo_nonneg hlo)
    (finiteProduct_le_productUpperRat S g lo hi hlo_nonneg hlo hhi)
    hcheck

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
  LeanCert.Cert.checkRatInterval (logProductLowerRat S lo) (logProductUpperRat S hi)
    targetLo targetHi

/-- Golden theorem for finite log-product interval certificates. -/
theorem verify_logProduct_interval
    (S : Finset Nat) (g : Nat → ℝ) (lo hi : Nat → ℚ)
    (hlo : ∀ n ∈ S, (lo n : ℝ) ≤ Real.log (g n))
    (hhi : ∀ n ∈ S, Real.log (g n) ≤ (hi n : ℝ))
    (targetLo targetHi : ℚ)
    (hcheck : checkLogProductInterval S lo hi targetLo targetHi = true) :
    (targetLo : ℝ) ≤ finiteLogProduct S g ∧
      finiteLogProduct S g ≤ (targetHi : ℝ) := by
  exact LeanCert.Cert.verify_rat_interval
    (logProductLowerRat_le_finiteLogProduct S g lo hlo)
    (finiteLogProduct_le_logProductUpperRat S g hi hhi)
    hcheck

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

/-- Convert a certified log-product lower bound into an exponential product lower bound. -/
theorem verify_product_lower_of_log_lower
    (S : Finset Nat) (g : Nat → ℝ) (lo : ℚ)
    (hpos : ∀ n ∈ S, 0 < g n)
    (hlog : (lo : ℝ) ≤ finiteLogProduct S g) :
    Real.exp (lo : ℝ) ≤ finiteProduct S g := by
  rw [finiteProduct_eq_exp_finiteLogProduct S g hpos]
  exact Real.exp_le_exp.mpr hlog

/-- Convert a certified log-product upper bound into an exponential product upper bound. -/
theorem verify_product_upper_of_log_upper
    (S : Finset Nat) (g : Nat → ℝ) (hi : ℚ)
    (hpos : ∀ n ∈ S, 0 < g n)
    (hlog : finiteLogProduct S g ≤ (hi : ℝ)) :
    finiteProduct S g ≤ Real.exp (hi : ℝ) := by
  rw [finiteProduct_eq_exp_finiteLogProduct S g hpos]
  exact Real.exp_le_exp.mpr hlog

end LeanCert.ANT
