/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Tactic.Discovery
import LeanCert.Tactic.FinSumBound
import LeanCert.Tactic.LeanCert.Types

/-!
# Semantic Goal Classification

Classification preserves semantic heads such as `ExistsUnique` and reuses the
dedicated tactic parsers.  Solver tactics remain responsible for constructing
their detailed payloads; the router does not duplicate their syntax logic.
-/

open Lean Meta

namespace LeanCert.Tactic

open LeanCert.Tactic.Discovery

private def multivariateVarCount
    (goal : Lean.Expr) : MetaM (Option Nat) := do
  let some parsed ← Auto.parseMultivariateBoundGoal goal | return none
  match parsed with
  | .forallLe vars .. | .forallGe vars .. => return some vars.size

private def multivariateExistentialVarCount
    (goal : Lean.Expr) : MetaM (Option Nat) := do
  let some parsed ← parseMultivariateExistentialGoal goal | return none
  match parsed with
  | .minimize _ vars _ | .maximize _ vars _ => return some vars.size

/-- Recognize point comparisons and propositional combinations of comparisons. -/
private partial def isPointComparison (goal : Lean.Expr) : MetaM Bool := do
  if goal.isForall then return false
  if goal.isAppOfArity ``And 2 then
    let args := goal.getAppArgs
    return (← isPointComparison args[0]!) && (← isPointComparison args[1]!)
  if goal.isAppOfArity ``Or 2 then
    let args := goal.getAppArgs
    return (← isPointComparison args[0]!) || (← isPointComparison args[1]!)
  return (← Auto.parsePointIneq goal).isSome

/-- Recognize only closed Boolean checkers implemented inside LeanCert. -/
private def isClosedLeanCertChecker (goal : Lean.Expr) : MetaM Bool := do
  match_expr goal with
  | Eq ty lhs rhs =>
    unless ← isDefEq ty (mkConst ``Bool) do return false
    let checker :=
      if rhs.isConstOf ``Bool.true then some lhs
      else if lhs.isConstOf ``Bool.true then some rhs
      else none
    let some checker := checker | return false
    if checker.hasFVar then return false
    let some name := checker.getAppFn.constName? | return false
    return name.getRoot == `LeanCert
  | _ => return false

/-- Classify a goal by mathematical intent without changing the tactic state. -/
def classifyGoal (goal : Lean.Expr) : MetaM (Option GoalIntent) := do
  -- Preserve `ExistsUnique`: reducing it first destroys the semantic head.
  if (← parseUniqueRootGoal goal).isSome then
    return some .uniqueRoot

  if (← parseRootExistsGoal goal).isSome then
    return some .rootExists
  if (← parseArgminGoal goal).isSome then
    return some .argmin
  if (← parseArgmaxGoal goal).isSome then
    return some .argmax

  if let some count ← multivariateExistentialVarCount goal then
    if count > 1 then
      let some parsed ← parseMultivariateExistentialGoal goal | return none
      match parsed with
      | .minimize .. => return some .existentialMinimum
      | .maximize .. => return some .existentialMaximum

  if let some parsed ← parseExistentialGoal goal then
    match parsed with
    | .minimize .. => return some .existentialMinimum
    | .maximize .. => return some .existentialMaximum

  if (← Auto.parseRootGoal goal).isSome then
    return some .noRoot
  if ← isFinSumBoundGoal goal then
    return some .finiteSum
  if ← isClosedLeanCertChecker goal then
    return some .certificateCheck

  if let some count ← multivariateVarCount goal then
    if count > 1 then return some .multivariateBound
  if (← Auto.parseBoundGoal goal).isSome then
    return some .intervalBound

  -- The current integration parser recognizes the legacy explicit-enclosure
  -- form.  It is classified so the front door can give a precise PR3 message.
  if (← parseIntegrationGoal goal).isSome then
    return some .integralBound
  if ← isPointComparison goal then
    return some .pointInequality
  return none

end LeanCert.Tactic
