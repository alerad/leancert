/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import Mathlib.Tactic.Basic
import LeanCert.Tactic.LeanCert.Types

/-!
# Transactional Solver Attempts

A speculative solver must either close its focused goal completely or leave
the tactic state exactly as it found it.  Messages and info trees produced by
failed attempts are captured rather than leaked to the user.
-/

open Lean Meta Elab Tactic

namespace LeanCert.Tactic

/-- Run `solver` transactionally on the main goal.

Success requires the focused goal to be completely closed.  Sibling goals are
preserved.  Exceptions and partial proofs restore the complete saved state.
Messages and info trees from the attempt are suppressed; the future semantic
router can emit one message from the returned structured result instead. -/
def runAttempt (report : SolverReport) (solver : TacticM Unit) :
    TacticM (Except AttemptFailure SolverReport) := do
  let originalGoals ← getGoals
  let some focused := originalGoals.head?
    | return .error (.internalFailure "no goals to solve")
  let siblings := originalGoals.tail
  let saved ← saveState
  setGoals [focused]
  try
    let captured ← Mathlib.Tactic.withResetServerInfo solver
    if captured.msgs.hasErrors then
      let rendered ← captured.msgs.toList.mapM fun msg => msg.data.toString
      saved.restore
      return .error (.internalFailure (String.intercalate "\n" rendered))
    let remaining ← getGoals
    if remaining.isEmpty then
      setGoals siblings
      return .ok report
    let rendered ← remaining.mapM fun goal => do
      goal.withContext do
        return toString (← ppExpr (← goal.getType))
    saved.restore
    return .error (.incompleteProof rendered.toArray)
  catch e =>
    let detail ← e.toMessageData.toString
    saved.restore
    return .error (.internalFailure detail)

end LeanCert.Tactic
