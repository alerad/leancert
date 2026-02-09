import Mathlib.Util.AssertNoSorry
import LeanCert.Engine.Eval.Core
import LeanCert.Core.IntervalRat.Taylor
import LeanCert.Core.IntervalRat.TrigReduced

/-!
Axiom/sorry guardrail for the certified interval evaluation path.
These should stay free of `sorryAx`.
-/

assert_no_sorry LeanCert.Engine.evalIntervalCore_correct
assert_no_sorry LeanCert.Engine.evalIntervalCore1_correct
assert_no_sorry LeanCert.Core.IntervalRat.mem_logComputable
assert_no_sorry LeanCert.Core.IntervalRat.mem_sinComputableReduced
assert_no_sorry LeanCert.Core.IntervalRat.mem_cosComputableReduced
assert_no_sorry LeanCert.Engine.mem_erfPointComputable
