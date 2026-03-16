/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import Lean

/-!
# Shared Bridge + native_decide Infrastructure

Common pattern for `finsum_bound`, `finsum_witness`, and `finmatrix_bound`:
apply a bridge proof term, close the Bool/ℚ check with `native_decide`,
and handle the case where the bridge's type isn't defEq to the goal
via a suffices + converter fallback.
-/

open Lean Meta Elab Tactic Term

namespace LeanCert.Tactic

/-- Apply a bridge proof and close the certificate check with `native_decide`.

If `proofTy` is definitionally equal to `goalType`, assigns directly.
Otherwise, uses a suffices + converter pattern:
1. Creates `suffMVar : proofTy` and `converterMVar : proofTy → goalType`
2. Assigns `goal := converterMVar suffMVar`
3. Closes `suffMVar` with the bridge proof
4. Closes `checkMVar` with `native_decide`
5. Tries each converter tactic in sequence on `converterMVar`

Parameters:
- `goal`: the main goal mvar
- `goalType`: the goal's type
- `proof`: the bridge proof term (with `checkMVar` as a placeholder argument)
- `checkMVar`: the mvar for the Bool/ℚ certificate check
- `tacticName`: name for error messages (e.g., "finsum_bound")
- `converterSteps`: fallback tactics to try (in order) for converting `proofTy → goalType`
-/
def closeBridgeWithNativeDecide
    (goal : MVarId) (goalType : Lean.Expr)
    (proof checkMVar : Lean.Expr)
    (tacticName : String)
    (converterSteps : Array (TacticM Unit))
    : TacticM Unit := do
  let proofTy ← inferType proof
  if ← isDefEq proofTy goalType then
    -- Direct path: bridge type matches goal exactly
    goal.assign proof
    replaceMainGoal [checkMVar.mvarId!]
    evalTactic (← `(tactic| native_decide))
  else
    -- Suffices fallback: bridge type differs from goal
    let suffMVar ← mkFreshExprMVar (some proofTy) (kind := .syntheticOpaque)
    let converterMVar ← mkFreshExprMVar
      (some (← mkArrow proofTy goalType)) (kind := .syntheticOpaque)
    goal.assign (mkApp converterMVar suffMVar)

    -- 1. Solve suffMVar: assign the bridge proof
    suffMVar.mvarId!.assign proof

    -- 2. Solve checkMVar with native_decide
    setGoals [checkMVar.mvarId!]
    try
      evalTactic (← `(tactic| native_decide))
    catch e =>
      throwError "{tacticName}: native_decide failed on certificate check.\n{e.toMessageData}"

    -- 3. Solve converterMVar: try each converter in sequence
    setGoals [converterMVar.mvarId!]
    for step in converterSteps do
      if (← getGoals).isEmpty then return
      try
        step
        return
      catch _ => pure ()
    -- All converters failed
    let cvGoalType ← converterMVar.mvarId!.getType
    throwError "{tacticName}: could not convert bridge type to goal type.\n\
      Converter goal: {← ppExpr cvGoalType}"

end LeanCert.Tactic
