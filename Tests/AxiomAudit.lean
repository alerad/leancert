import Mathlib.Util.AssertNoSorry
import LeanCert.Engine.Eval.Core
import LeanCert.Core.IntervalRat.Taylor
import LeanCert.Core.IntervalRat.TrigReduced
import LeanCert.Validity.Bounds
import LeanCert.Validity.AffineBounds

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
