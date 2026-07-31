/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Examples.Li2Base

/-!
# Certified bounds for li(2)

This is the stable, lightweight interface for the Ramanujan--Soldner constant
bounds. The two numerical bounds are intentionally stated with `sorry` so
downstream projects do not pay for the expensive numerical verification during
ordinary builds. `LeanCert.Examples.Li2Verified` proves matching statements in
a separate CI target and checks their statement identity.

This is an intentional lightweight/heavy verification boundary, not a
forwarding module.
-/

open MeasureTheory LeanCert.Engine.TaylorModel
open scoped ENNReal

namespace LeanCert.CertifiedBounds.Li2

/-- The symmetric logarithmic integrand used to define `li(2)`. -/
noncomputable abbrev integrand : ℝ → ℝ := _root_.Li2.g

/-- The value `li(2)`. -/
noncomputable abbrev value : ℝ := _root_.Li2.li2

/-- The symmetric logarithmic integrand is positive on `(0, 1)`. -/
alias integrand_pos := _root_.Li2.g_pos

/-- The symmetric logarithmic integrand is at most two on `(0, 1)`. -/
alias integrand_le_two := _root_.Li2.g_le_two

/-- Certified lower bound: `1.039 ≤ li(2)`.

Machine-checked as `Li2Verified.li2_lower_verified`; see the module docstring
for the statement-identity and CI boundary. -/
theorem lower : (1039 : ℚ) / 1000 ≤ _root_.Li2.li2 := by
  sorry

/-- Certified upper bound: `li(2) ≤ 1.06`.

Machine-checked as `Li2Verified.li2_upper_verified`; see the module docstring
for the statement-identity and CI boundary. -/
theorem upper : _root_.Li2.li2 ≤ (106 : ℚ) / 100 := by
  sorry

/-- Combined certified bounds for `li(2)`. -/
theorem bounds : (1039 : ℚ) / 1000 ≤ value ∧ value ≤ (106 : ℚ) / 100 :=
  ⟨lower, upper⟩

/-- Convenient approximation theorem around `1.045`. -/
theorem approx_1045 : |value - (1045 : ℚ) / 1000| ≤ (15 : ℚ) / 1000 := by
  have ⟨hlo, hhi⟩ := bounds
  rw [abs_le]
  constructor <;> linarith

end LeanCert.CertifiedBounds.Li2
