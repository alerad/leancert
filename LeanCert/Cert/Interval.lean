/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Basic.Real.Basic

/-!
# Small rational interval certificate combinators

These helpers factor the common LeanCert pattern:

* a computable rational lower endpoint;
* a computable rational upper endpoint;
* semantic lower/upper correctness proofs;
* a boolean endpoint check.
-/

namespace LeanCert.Cert

/-- Boolean checker for rational interval endpoints. -/
def checkRatInterval (lower upper lo hi : ℚ) : Bool :=
  decide (lo ≤ lower) && decide (upper ≤ hi)

/-- Boolean checker for a rational upper endpoint. -/
def checkRatUpper (upper hi : ℚ) : Bool :=
  decide (upper ≤ hi)

/-- Boolean checker for a rational lower endpoint. -/
def checkRatLower (lower lo : ℚ) : Bool :=
  decide (lo ≤ lower)

/-- Generic Golden Theorem for rational interval endpoints. -/
theorem verify_rat_interval {value : ℝ} {lower upper lo hi : ℚ}
    (hlower : (lower : ℝ) ≤ value)
    (hupper : value ≤ (upper : ℝ))
    (hcheck : checkRatInterval lower upper lo hi = true) :
    (lo : ℝ) ≤ value ∧ value ≤ (hi : ℝ) := by
  simp only [checkRatInterval, Bool.and_eq_true, decide_eq_true_eq] at hcheck
  have hlo : (lo : ℝ) ≤ (lower : ℝ) := by exact_mod_cast hcheck.1
  have hhi : (upper : ℝ) ≤ (hi : ℝ) := by exact_mod_cast hcheck.2
  exact ⟨hlo.trans hlower, hupper.trans hhi⟩

/-- Generic Golden Theorem for rational upper endpoints. -/
theorem verify_rat_upper {value : ℝ} {upper hi : ℚ}
    (hupper : value ≤ (upper : ℝ))
    (hcheck : checkRatUpper upper hi = true) :
    value ≤ (hi : ℝ) := by
  simp only [checkRatUpper, decide_eq_true_eq] at hcheck
  have hhi : (upper : ℝ) ≤ (hi : ℝ) := by exact_mod_cast hcheck
  exact hupper.trans hhi

/-- Generic Golden Theorem for rational lower endpoints. -/
theorem verify_rat_lower {value : ℝ} {lower lo : ℚ}
    (hlower : (lower : ℝ) ≤ value)
    (hcheck : checkRatLower lower lo = true) :
    (lo : ℝ) ≤ value := by
  simp only [checkRatLower, decide_eq_true_eq] at hcheck
  have hlo : (lo : ℝ) ≤ (lower : ℝ) := by exact_mod_cast hcheck
  exact hlo.trans hlower

end LeanCert.Cert
