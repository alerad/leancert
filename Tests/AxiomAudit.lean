import Mathlib.Util.AssertNoSorry
import LeanCert
-- Library modules not reachable from the root `LeanCert` module are imported
-- explicitly so the whole-library axiom sweep below actually covers them.
-- `LeanCert.Test.*` and `LeanCert.Examples.*` are deliberately excluded:
-- `native_decide` is a legitimate user-facing engine there.
import LeanCert.Validity
import LeanCert.Validity.AffineBounds
-- NOTE: `LeanCert.Validity.Integration`, `.CertificateIntegration` (which
-- imports `.Integration`), and the `LeanCert.Validity.Bounds.*` submodules are
-- NOT imported: they duplicate declarations inside the `LeanCert.Validity.Bounds`
-- monolith and clash with it (e.g. `integrateInterval1Core`,
-- `checkPointUpperBound` are each defined in both copies — a half-finished
-- file split). The Integration cluster gets its own sweep in
-- `Tests/AxiomAuditIntegration.lean`.
import LeanCert.Validity.IntegrationDyadic
import LeanCert.Validity.Monotonicity
import LeanCert.Engine.Eval
import LeanCert.Engine.Pisano
import LeanCert.Engine.PentagonLucas
import LeanCert.Engine.TaylorModel.Log1p
import LeanCert.Engine.TaylorModel.TrigReduced
import LeanCert.Core.HermiteBounds
import LeanCert.Core.LogBounds

/-!
Axiom/sorry guardrail for the certified interval evaluation path.

Two layers of protection:

1. `assert_no_sorry` — rejects `sorryAx`.
2. `#guard_msgs in #print axioms` — pins the FULL axiom set of the flagship
   theorems to the three standard Lean/Mathlib axioms. This catches
   `native_decide` (`Lean.ofReduceBool`) creep, which `assert_no_sorry` cannot
   see. A library-internal `native_decide` once leaked into
   `evalIntervalCore_correct` via the Euler–Mascheroni interval proof; these
   guards make that class of regression a build failure.

`native_decide` remains a legitimate *user-facing* verification engine for
certificate checks; the invariant enforced here is that the *library theorems
themselves* do not depend on it.
-/

assert_no_sorry LeanCert.Engine.evalIntervalCore_correct
assert_no_sorry LeanCert.Engine.evalIntervalCore1_correct
assert_no_sorry LeanCert.Core.IntervalRat.mem_logComputable
assert_no_sorry LeanCert.Core.IntervalRat.mem_sinComputableReduced
assert_no_sorry LeanCert.Core.IntervalRat.mem_cosComputableReduced
assert_no_sorry LeanCert.Engine.mem_erfPointComputable

/-! ### Exact axiom pinning (catches `native_decide` / `ofReduceBool` creep) -/

/--
info: 'LeanCert.Engine.evalIntervalCore_correct' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LeanCert.Engine.evalIntervalCore_correct

/--
info: 'LeanCert.Core.MathConst.mem_interval' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LeanCert.Core.MathConst.mem_interval

/--
info: 'LeanCert.Core.IntervalRat.mem_logComputable' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LeanCert.Core.IntervalRat.mem_logComputable

/--
info: 'LeanCert.Core.IntervalRat.mem_expComputable' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LeanCert.Core.IntervalRat.mem_expComputable

/--
info: 'LeanCert.Core.IntervalRat.mem_sinComputableReduced' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LeanCert.Core.IntervalRat.mem_sinComputableReduced

/--
info: 'LeanCert.Core.IntervalRat.mem_cosComputableReduced' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LeanCert.Core.IntervalRat.mem_cosComputableReduced

/--
info: 'LeanCert.Validity.RootFinding.verify_no_root' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LeanCert.Validity.RootFinding.verify_no_root

/--
info: 'LeanCert.Validity.verify_upper_bound_affine1_strict' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LeanCert.Validity.verify_upper_bound_affine1_strict

/--
info: 'LeanCert.Validity.verify_upper_bound_dyadic' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LeanCert.Validity.verify_upper_bound_dyadic

/-! ### Whole-library sweep: no axioms minted inside LeanCert

Every `native_decide` use inside the library mints a per-declaration axiom
(`<decl>._native.native_decide.ax_*`). This sweep walks the entire environment
(the audit imports the full `LeanCert` root module) and fails if ANY axiom
lives in the LeanCert namespace — including private-mangled names, which
per-theorem pinning cannot see. `native_decide` in tactic *quotations* is
unaffected: those axioms are minted in end-user proofs, not in the library. -/

open Lean in
run_meta do
  let env ← getEnv
  let mut offenders : Array Name := #[]
  for (n, info) in env.constants.toList do
    if let .axiomInfo _ := info then
      if (n.toString.splitOn "LeanCert").length > 1 then
        offenders := offenders.push n
  unless offenders.isEmpty do
    throwError "Axioms minted inside LeanCert (library-internal native_decide leak?):\n\
      {offenders.toList}"
