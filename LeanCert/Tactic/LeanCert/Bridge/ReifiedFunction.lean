/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Meta.ProveContinuous
import LeanCert.Tactic.LeanCert.Normalize

/-!
# Proof-Carrying Reification

The reifier's syntax result is not itself a semantic bridge.  This module
packages the reflected AST with a kernel-checked equality between its evaluator
and the original function.  Solver capabilities are derived separately.
-/

open Lean Meta Elab Tactic

namespace LeanCert.Tactic.Bridge

structure ReifiedFunction where
  arity : Nat
  ast : Lean.Expr
  original : Lean.Expr
  /-- A proof of `∀ x₀ ... xₙ, Expr.eval ρ ast = original x₀ ... xₙ`,
  where `ρ i` reads the corresponding argument and defaults to zero. -/
  evalEq : Lean.Expr
  unfolded : Array Name := #[]
  deriving Inhabited

structure FunctionCapabilities where
  supportedCore : Option Lean.Expr := none
  continuousCore : Option Lean.Expr := none
  domainValid : Option Lean.Expr := none
  deriving Inhabited

private def mkEnvironment (arguments : Array Lean.Expr) : MetaM Lean.Expr := do
  if arguments.size == 1 then
    withLocalDeclD `i (mkConst ``Nat) fun i => do
      mkLambdaFVars #[i] arguments[0]!
  else
  withLocalDeclD `i (mkConst ``Nat) fun i => do
    let zeroRat := toExpr (0 : ℚ)
    let mut body ← mkAppOptM ``Rat.cast #[mkConst ``Real, none, zeroRat]
    for index in (List.range arguments.size).reverse do
      let condition ← mkAppM ``Eq #[i, toExpr index]
      body ← mkAppM ``ite #[condition, arguments[index]!, body]
    mkLambdaFVars #[i] body

private def closeBridgeGoal (report : LeanCert.Meta.ReifyReport)
    (proposition : Lean.Expr) : TacticM Lean.Expr := do
  let originalGoals ← getGoals
  let saved ← saveState
  let proof ← mkFreshExprMVar proposition MetavarKind.syntheticOpaque
  setGoals [proof.mvarId!]
  try
    LeanCert.Tactic.closeReificationBridge report
    let remaining ← getGoals
    unless remaining.isEmpty do
      let rendered ← remaining.mapM fun goal => goal.withContext do
        ppExpr (← goal.getType)
      throwError "reification equality normalization left proof obligations:\n\
        {MessageData.joinSep rendered m!"\n"}"
    let proof ← instantiateMVars proof
    if proof.hasMVar then
      throwError "reification equality contains metavariables"
    setGoals originalGoals
    return proof
  catch exception =>
    saved.restore
    throw exception

/-- Reify a closed real-valued function and prove evaluator agreement. -/
def reifyFunction (function : Lean.Expr) : TacticM ReifiedFunction := do
  let report ← LeanCert.Meta.reifyWithReport function
  lambdaTelescope function fun arguments body => do
    for argument in arguments do
      let type ← inferType argument
      unless ← isDefEq type (mkConst ``Real) do
        throwError "proof-carrying reification currently requires real arguments"
    let environment ← mkEnvironment arguments
    let evaluated ← mkAppM ``LeanCert.Core.Expr.eval #[environment, report.expr]
    let localType ← mkAppM ``Eq #[evaluated, body]
    let localProof ← closeBridgeGoal report localType
    let evalEq ← mkLambdaFVars arguments localProof
    return {
      arity := arguments.size
      ast := report.expr
      original := function
      evalEq
      unfolded := report.unfolded
    }

/-- Derive expression-fragment capabilities independently from semantic
reification equality.  Failure to derive a capability is expected and does not
invalidate `evalEq`. -/
def deriveCapabilities (function : ReifiedFunction) : MetaM FunctionCapabilities := do
  let supportedCore : Option Lean.Expr ←
    try
      pure (some (← LeanCert.Meta.mkSupportedCoreProof function.ast))
    catch _ =>
      pure none
  let continuousCore : Option Lean.Expr ←
    try
      pure (some (← LeanCert.Meta.mkContinuousCoreProof function.ast))
    catch _ =>
      pure none
  return { supportedCore, continuousCore }

end LeanCert.Tactic.Bridge
