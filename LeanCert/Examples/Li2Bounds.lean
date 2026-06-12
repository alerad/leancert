/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Examples.Li2Base

/-!
# Li(2) Bounds — Lightweight Interface

Public interface for the Ramanujan-Soldner constant bounds.

The two bound theorems below are intentionally stated with `sorry`, following
the lightweight-interface / heavy-verification split used by the PNT+ project
(PNT+ PR #774). Downstream projects import this file and get the bound
statements in seconds; the machine-checked proofs live in `Li2Verified.lean`
(`Li2Verified.li2_lower_verified` / `li2_upper_verified`), built as its own
lake target (`lake build Li2Verified`) in LeanCert CI.

## Drift protection

1. `Li2Verified.lean` ends with a statement-identity check that fails
   compilation if the types of the interface theorems below differ from the
   types of the verified theorems.
2. `Tests/AxiomAudit.lean` sweeps every library declaration's axiom set
   against an exact allowlist of the four `Li2` declarations in this file;
   any other sorry-dependent declaration in LeanCert fails CI.
-/

open MeasureTheory LeanCert.Engine.TaylorModel
open scoped ENNReal

namespace Li2

/-- Certified lower bound: li(2) ≥ 1.039.

Machine-checked as `Li2Verified.li2_lower_verified`; stated here with `sorry`
so downstream users do not pay the heavy verification build. See the module
docstring for drift protection. -/
theorem li2_lower : (1039:ℚ)/1000 ≤ li2 := by
  sorry

/-- Certified upper bound: li(2) ≤ 1.06.

Machine-checked as `Li2Verified.li2_upper_verified`; stated here with `sorry`
so downstream users do not pay the heavy verification build. See the module
docstring for drift protection. -/
theorem li2_upper : li2 ≤ (106:ℚ)/100 := by
  sorry

/-- Combined bounds: li(2) ∈ [1.039, 1.06]. -/
theorem li2_bounds : (1039:ℚ)/1000 ≤ li2 ∧ li2 ≤ (106:ℚ)/100 :=
  ⟨li2_lower, li2_upper⟩

/-- li(2) is approximately 1.045 (the Ramanujan-Soldner constant).
    Our bounds show: |li(2) - 1.045| ≤ 0.015. -/
theorem li2_approx_1045 : |li2 - (1045:ℚ)/1000| ≤ (15:ℚ)/1000 := by
  have ⟨hlo, hhi⟩ := li2_bounds
  rw [abs_le]
  constructor
  · linarith
  · linarith

end Li2
