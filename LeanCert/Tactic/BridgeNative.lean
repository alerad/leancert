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
    -- Close the executable certificate before assigning the main goal.  This
    -- avoids leaving the user with an assigned theorem whose checker proof
    -- failed afterward.
    replaceMainGoal [checkMVar.mvarId!]
    try
      evalTactic (← `(tactic| native_decide))
    catch e =>
      throwError "{tacticName}: native_decide failed on certificate check.\n\
        Check expression type: {← ppExpr (← checkMVar.mvarId!.getType)}\n\
        Bridge proof type: {← ppExpr proofTy}\n\
        Goal type: {← ppExpr goalType}\n\
        {e.toMessageData}"
    goal.assign proof
  else
    -- Suffices fallback: bridge type differs from goal
    let suffMVar ← mkFreshExprMVar (some proofTy) (kind := .syntheticOpaque)
    let converterMVar ← mkFreshExprMVar
      (some (← mkArrow proofTy goalType)) (kind := .syntheticOpaque)

    -- 1. Solve checkMVar with native_decide before assigning the main goal.
    setGoals [checkMVar.mvarId!]
    try
      evalTactic (← `(tactic| native_decide))
    catch e =>
      throwError "{tacticName}: native_decide failed on certificate check.\n\
        Check expression type: {← ppExpr (← checkMVar.mvarId!.getType)}\n\
        Bridge proof type: {← ppExpr proofTy}\n\
        Goal type: {← ppExpr goalType}\n\
        {e.toMessageData}"

    -- 2. Solve converterMVar: try each converter in sequence.  A converter
    -- only succeeds if it closes all goals; partial progress is rolled back.
    setGoals [converterMVar.mvarId!]
    for step in converterSteps do
      if (← getGoals).isEmpty then return
      let saved ← saveState
      try
        step
        if (← getGoals).isEmpty then
          suffMVar.mvarId!.assign proof
          goal.assign (mkApp converterMVar suffMVar)
          return
        else
          saved.restore
      catch _ =>
        saved.restore
    -- All converters failed
    let cvGoalType ← converterMVar.mvarId!.getType
    throwError "{tacticName}: could not convert bridge type to goal type.\n\
      Bridge proof type: {← ppExpr proofTy}\n\
      Goal type: {← ppExpr goalType}\n\
      Converter goal: {← ppExpr cvGoalType}\n\
      Check expression type: {← ppExpr (← checkMVar.mvarId!.getType)}"

end LeanCert.Tactic
