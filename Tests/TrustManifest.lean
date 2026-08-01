/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert
import LeanCert.Examples.EulerMascheroniBounds

/-!
# Trust manifest for exported declarations

`#assert_trust` pins for the representative public surface. This complements
`Tests/AxiomAudit.lean`:

* AxiomAudit pins *exact axiom sets* for golden theorems and sweeps the whole
  library for illegally minted axioms;
* this manifest classifies exported results by *trust class* and fails on
  drift in **either** direction — a kernel-clean theorem acquiring compiler
  trust is a regression, and a native-pinned theorem losing its native
  dependency means the pin should be tightened to `kernel`.

CI runs this file in the soundness-guard workflow (after AxiomAudit).
When exporting a new headline result, add its pin here.
-/

/-! ## Golden theorems: kernel-clean by construction

The lifts from Boolean certificates to semantic propositions must never
depend on compiler trust — every proof produced by any trust mode reuses
them unchanged. -/

#assert_trust kernel LeanCert.Validity.verify_upper_bound
#assert_trust kernel LeanCert.Validity.verify_lower_bound
#assert_trust kernel LeanCert.Validity.verify_strict_upper_bound
#assert_trust kernel LeanCert.Validity.verify_strict_lower_bound
#assert_trust kernel LeanCert.Validity.verify_upper_bound_dyadic_checked
#assert_trust kernel LeanCert.Validity.verify_lower_bound_dyadic_checked
#assert_trust kernel LeanCert.Validity.Integration.verify_integral_bound
#assert_trust kernel LeanCert.Engine.verify_finsum_upper_full
#assert_trust kernel LeanCert.Engine.verify_finsum_lower_full
#assert_trust kernel LeanCert.API.Bounds.verifyUpperBoundBox
#assert_trust kernel LeanCert.API.Bounds.verifyLowerBoundBox
#assert_trust kernel LeanCert.Validity.verify_matrix_posSemidef
#assert_trust kernel LeanCert.Validity.verify_matrix_posDef
#assert_trust kernel LeanCert.gramMatrix_posSemidef
#assert_trust kernel LeanCert.regularizedGramMatrix_posDef

/-! ## Euler–Mascheroni bounds: intentionally native-trusted

Verified by an inline `native_decide` over a `2^20`-term reflective harmonic
sum — the scale at which native evaluation earns its trust cost (see the
calibration in `scripts/bench-trust/README.md`). If these ever stop
depending on native trust, the pins below fail and should be tightened to
`kernel` (and celebrated). -/

#assert_trust native EulerMascheroni.gamma_lower
#assert_trust native EulerMascheroni.gamma_upper
#assert_trust native EulerMascheroni.gamma_bounds
#assert_trust native EulerMascheroni.gamma_approx
