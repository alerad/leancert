/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import Lean
import LeanCert.Tactic.Verification

/-!
# Shared Bridge + Certificate-Verification Infrastructure

Common pattern for `finsum_bound`, `finsum_witness`, and `finmatrix_bound`:
apply a bridge proof term, close the Bool/ℚ check via the verification
choke point (`closeCertificateGoal`, honoring `leancert.trust`), and handle
the case where the bridge's type isn't defEq to the goal via a
suffices + converter fallback.
-/

open Lean Meta Elab Tactic Term

namespace LeanCert.Tactic

/-- Typed failures from applying a checked bridge theorem. -/
inductive BridgeFailure where
  | rejected
  | verificationFailure (detail : String)
  | transportFailure (detail : String)
  deriving Inhabited, Repr

private def throwBridgeFailure (tacticName : String) : BridgeFailure → TacticM α
  | .rejected =>
      throwError "{tacticName}: the bridge certificate was rejected"
  | .verificationFailure detail =>
      throwError "{tacticName}: certificate verification failed:\n{detail}"
  | .transportFailure detail =>
      throwError "{tacticName}: could not transport the checked bridge theorem:\n{detail}"

/-- Apply a bridge proof and close its certificate through the configured
verification route.

If `proofTy` is definitionally equal to `goalType`, assigns directly.
Otherwise, uses a suffices + converter pattern:
1. Creates `suffMVar : proofTy` and `converterMVar : proofTy → goalType`
2. Assigns `goal := converterMVar suffMVar`
3. Closes `suffMVar` with the bridge proof
4. Closes `checkMVar` through the configured kernel/native/auto verification route
5. Tries each converter tactic in sequence on `converterMVar`

Parameters:
- `goal`: the main goal mvar
- `goalType`: the goal's type
- `proof`: the bridge proof term (with `checkMVar` as a placeholder argument)
- `checkMVar`: the mvar for the Bool/ℚ certificate check
- `tacticName`: name for error messages (e.g., "finsum_bound")
- `converterSteps`: fallback tactics to try (in order) for converting `proofTy → goalType`
-/
private def closeBridgeWithVerificationTypedImpl
    (original : Lean.Elab.Tactic.SavedState)
    (goal : MVarId) (goalType : Lean.Expr)
    (proof checkMVar : Lean.Expr)
    (tacticName : String)
    (converterSteps : Array (TacticM Unit))
    : TacticM (Except BridgeFailure VerificationEvent) := do
  let proofTy ← inferType proof
  if ← isDefEq proofTy goalType then
    let event ←
      match ← closeCertificateGoalTyped (← VerificationConfig.current)
          checkMVar.mvarId! (tacticName := tacticName) with
      | .accepted event => pure event
      | .rejected =>
          original.restore
          return .error .rejected
      | .failed failure =>
          original.restore
          return .error <| .verificationFailure (failure.message tacticName)
    goal.assign proof
    return .ok event
  else
    let suffMVar ← mkFreshExprMVar (some proofTy) (kind := .syntheticOpaque)
    let converterMVar ← mkFreshExprMVar
      (some (← mkArrow proofTy goalType)) (kind := .syntheticOpaque)

    let event ←
      match ← closeCertificateGoalTyped (← VerificationConfig.current)
          checkMVar.mvarId! (tacticName := tacticName) with
      | .accepted event => pure event
      | .rejected =>
          original.restore
          return .error .rejected
      | .failed failure =>
          original.restore
          return .error <| .verificationFailure (failure.message tacticName)

    setGoals [converterMVar.mvarId!]
    for step in converterSteps do
      if (← getGoals).isEmpty then
        suffMVar.mvarId!.assign proof
        goal.assign (mkApp converterMVar suffMVar)
        return .ok event
      let saved ← saveState
      try
        step
        if (← getGoals).isEmpty then
          suffMVar.mvarId!.assign proof
          goal.assign (mkApp converterMVar suffMVar)
          return .ok event
        else
          saved.restore
      catch _ =>
        saved.restore
    let cvGoalType ← converterMVar.mvarId!.getType
    let detail ← m!"Bridge proof type: {← ppExpr proofTy}\n\
      Goal type: {← ppExpr goalType}\n\
      Converter goal: {← ppExpr cvGoalType}\n\
      Check expression type: {← ppExpr (← checkMVar.mvarId!.getType)}".toString
    original.restore
    return .error <| .transportFailure detail

/-- Typed and exception-total bridge boundary. Certificate rejection,
verification infrastructure failure, and theorem transport failure all restore
the complete caller state. -/
def closeBridgeWithVerificationTyped
    (goal : MVarId) (goalType : Lean.Expr)
    (proof checkMVar : Lean.Expr)
    (tacticName : String)
    (converterSteps : Array (TacticM Unit)) :
    TacticM (Except BridgeFailure VerificationEvent) := do
  let original ← saveState
  try
    closeBridgeWithVerificationTypedImpl original goal goalType proof checkMVar
      tacticName converterSteps
  catch e =>
    original.restore
    return .error <| .transportFailure (← e.toMessageData.toString)

/-- Reporting compatibility wrapper preserving the historical throwing API. -/
def closeBridgeWithVerificationReported
    (goal : MVarId) (goalType : Lean.Expr)
    (proof checkMVar : Lean.Expr)
    (tacticName : String)
    (converterSteps : Array (TacticM Unit))
    : TacticM VerificationEvent := do
  match ← closeBridgeWithVerificationTyped goal goalType proof checkMVar
      tacticName converterSteps with
  | .ok event => return event
  | .error failure => throwBridgeFailure tacticName failure

/-- Compatibility wrapper retaining the historical API name and result type. -/
def closeBridgeWithNativeDecide
    (goal : MVarId) (goalType : Lean.Expr)
    (proof checkMVar : Lean.Expr)
    (tacticName : String)
    (converterSteps : Array (TacticM Unit)) : TacticM Unit := do
  discard <| closeBridgeWithVerificationReported goal goalType proof checkMVar
    tacticName converterSteps

end LeanCert.Tactic
