/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import Mathlib.Tactic

/-!
# Fixed-cutoff eventual bounds

This module contains the first executable certificate family for quantitative
asymptotics.  It deliberately starts with a small global tail language:
nonnegative rational multiples of reciprocal powers.

Candidate cutoffs are untrusted.  The Boolean checker validates the endpoint
inequality and the Golden Theorem proves that the same inequality holds at
every larger natural number.
-/

namespace LeanCert.Validity

/-- Check the side conditions and cutoff value for
`q / (n : ℝ) ^ k ≤ bound` on every `n ≥ cutoff`. -/
def checkReciprocalPowerUpper
    (q bound : ℚ) (k cutoff : Nat) : Bool :=
  0 ≤ q && 0 < k && 0 < cutoff && q / (cutoff : ℚ) ^ k ≤ bound

/-- Soundness-facing package for a fixed-cutoff reciprocal-power bound. -/
structure ReciprocalPowerUpperCert
    (q bound : ℚ) (k cutoff : Nat) where
  checked : checkReciprocalPowerUpper q bound k cutoff = true

/-- Self-contained fixed-cutoff certificate data. This is the stable payload
that untrusted cutoff discovery may construct before checker replay. -/
structure EventualBoundCert where
  coefficient : ℚ
  bound : ℚ
  exponent : Nat
  cutoff : Nat
  checked :
    checkReciprocalPowerUpper coefficient bound exponent cutoff = true

/-- **Golden Theorem for fixed-cutoff reciprocal-power upper bounds.**

The only computational premise is `checkReciprocalPowerUpper = true`.  Search
for `cutoff` may therefore remain entirely untrusted. -/
theorem verify_reciprocal_power_upper
    (q bound : ℚ) (k cutoff : Nat)
    (hcheck : checkReciprocalPowerUpper q bound k cutoff = true) :
    ∀ n : Nat, cutoff ≤ n →
      (q : ℝ) / (n : ℝ) ^ k ≤ (bound : ℝ) := by
  simp only [checkReciprocalPowerUpper, Bool.and_eq_true, decide_eq_true_eq] at hcheck
  rcases hcheck with ⟨⟨⟨hq, hk⟩, hcutoff⟩, hendpoint⟩
  intro n hn
  have hcutoffReal : (0 : ℝ) < cutoff := by exact_mod_cast hcutoff
  have hnReal : (cutoff : ℝ) ≤ n := by exact_mod_cast hn
  have hpow : (cutoff : ℝ) ^ k ≤ (n : ℝ) ^ k := by
    exact pow_le_pow_left₀ (by positivity) hnReal k
  have hqReal : (0 : ℝ) ≤ q := by exact_mod_cast hq
  have htail : (q : ℝ) / (n : ℝ) ^ k ≤ (q : ℝ) / (cutoff : ℝ) ^ k := by
    exact div_le_div_of_nonneg_left hqReal (by positivity) hpow
  have hendpointReal :
      (q : ℝ) / (cutoff : ℝ) ^ k ≤ (bound : ℝ) := by
    exact_mod_cast hendpoint
  exact htail.trans hendpointReal

/-- Verify a packaged fixed-cutoff reciprocal-power certificate. -/
theorem ReciprocalPowerUpperCert.verify
    {q bound : ℚ} {k cutoff : Nat}
    (cert : ReciprocalPowerUpperCert q bound k cutoff) :
    ∀ n : Nat, cutoff ≤ n →
      (q : ℝ) / (n : ℝ) ^ k ≤ (bound : ℝ) :=
  verify_reciprocal_power_upper q bound k cutoff cert.checked

/-- Semantic theorem represented by a self-contained eventual-bound
certificate. -/
theorem EventualBoundCert.verify (cert : EventualBoundCert) :
    ∀ n : Nat, cert.cutoff ≤ n →
      (cert.coefficient : ℝ) / (n : ℝ) ^ cert.exponent ≤
        (cert.bound : ℝ) :=
  verify_reciprocal_power_upper cert.coefficient cert.bound cert.exponent
    cert.cutoff cert.checked

/-- Convenient `k = 1` Golden Theorem for tails written as `q / n`. -/
theorem verify_reciprocal_upper
    (q bound : ℚ) (cutoff : Nat)
    (hcheck : checkReciprocalPowerUpper q bound 1 cutoff = true) :
    ∀ n : Nat, cutoff ≤ n →
      (q : ℝ) / (n : ℝ) ≤ (bound : ℝ) := by
  simpa using verify_reciprocal_power_upper q bound 1 cutoff hcheck

end LeanCert.Validity
