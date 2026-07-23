/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import Mathlib.Tactic
import LeanCert.Core.IntervalRat.Basic
import LeanCert.Meta.Numeral
import LeanCert.Tactic.LeanCert.Bridge.ReifiedFunction
import LeanCert.Tactic.LeanCert.Semantic.Goal

/-!
# Proof-Bearing Semantic Preparation

Preparation turns source interval syntax into solver-ready domains.  Numerical
endpoint extraction is never accepted by itself: every normalized domain
carries a kernel-checked membership theorem relating it to the source domain.
-/

open Lean Meta Elab Tactic

namespace LeanCert.Tactic.Semantic

structure PreparationFailure where
  source : Lean.Expr
  detail : String
  deriving Inhabited

inductive PreparedFunction where
  | ready
      (source : Lean.Expr)
      (reified : LeanCert.Tactic.Bridge.ReifiedFunction)
      (capabilities : LeanCert.Tactic.Bridge.FunctionCapabilities)
  | unsupported
      (source : Lean.Expr)
      (detail : String)
  | deferred
      (source : Lean.Expr)
      (detail : String)
  deriving Inhabited

structure PreparedGoal where
  semantic : SemanticGoal
  domains : Array PreparedInterval := #[]
  functions : Array PreparedFunction := #[]
  deriving Inhabited

private def proveByNormNum (proposition : Lean.Expr) : TacticM Lean.Expr := do
  let originalGoals ← getGoals
  let saved ← saveState
  let proof ← mkFreshExprMVar proposition MetavarKind.syntheticOpaque
  setGoals [proof.mvarId!]
  try
    evalTactic (← `(tactic|
      norm_num [Set.mem_Icc, LeanCert.Core.IntervalRat.mem_def]))
    unless (← getGoals).isEmpty do
      throwError "normalization left proof obligations"
    let proof ← instantiateMVars proof
    if proof.hasMVar then
      throwError "normalization proof contains metavariables"
    setGoals originalGoals
    return proof
  catch exception =>
    saved.restore
    throw exception

private def membership (container element : Lean.Expr) : MetaM Lean.Expr :=
  mkAppM ``Membership.mem #[container, element]

private def forallMembershipIff (carrier source target : Lean.Expr) : MetaM Lean.Expr := do
  withLocalDeclD `x carrier fun x => do
    let lhs ← membership source x
    let rhs ← membership target x
    let body ← mkAppM ``Iff #[lhs, rhs]
    mkForallFVars #[x] body

private def forallNoMembership (carrier source : Lean.Expr) : MetaM Lean.Expr := do
  withLocalDeclD `x carrier fun x => do
    let member ← membership source x
    let body := mkApp (mkConst ``Not) member
    mkForallFVars #[x] body

private def singletonMembershipIff (source point : Lean.Expr) : MetaM Lean.Expr := do
  let pointType ← inferType point
  withLocalDeclD `x pointType fun x => do
    let lhs ← membership source x
    let rhs ← mkAppM ``Eq #[x, point]
    let body ← mkAppM ``Iff #[lhs, rhs]
    mkForallFVars #[x] body

/-- Normalize one interval domain and construct all transport evidence. -/
def prepareInterval (source : IntervalSyntax) : TacticM PreparedInterval := do
  match source.kind with
  | .open | .leftOpen | .rightOpen =>
      return .unsupported source (.topology source.kind)
  | .unorderedClosed =>
      return .unsupported source (.topology source.kind)
  | .intervalRat =>
      let iffType ← forallMembershipIff (mkConst ``Real) source.original source.original
      let iffProof ← proveByNormNum iffType
      return .closedRat source source.original iffProof
  | .closed =>
      let some loExpr := source.lo
        | return .unsupported source (.unsupportedSyntax "closed interval has no lower endpoint")
      let some hiExpr := source.hi
        | return .unsupported source (.unsupportedSyntax "closed interval has no upper endpoint")
      let carrier ← inferType loExpr
      unless ← isDefEq carrier (mkConst ``Real) do
        return .unsupported source (.unsupportedCarrier carrier)
      let some lo ← LeanCert.Meta.Numeral.toRat? loExpr
        | return .symbolicClosed source loExpr hiExpr
      let some hi ← LeanCert.Meta.Numeral.toRat? hiExpr
        | return .symbolicClosed source loExpr hiExpr
      if hi < lo then
        let emptyType ← forallNoMembership carrier source.original
        let emptyProof ← proveByNormNum emptyType
        return .empty source emptyProof
      if lo == hi then
        let singletonType ← singletonMembershipIff source.original loExpr
        let singletonProof ← proveByNormNum singletonType
        return .singleton source loExpr singletonProof
      let leType ← mkAppM ``LE.le #[toExpr lo, toExpr hi]
      let leProof ← mkDecideProof leType
      let interval ← mkAppM ``LeanCert.Core.IntervalRat.mk #[toExpr lo, toExpr hi, leProof]
      let iffType ← forallMembershipIff carrier source.original interval
      let iffProof ← proveByNormNum iffType
      return .closedRat source interval iffProof

private def prepareFunction (function : Lean.Expr) : TacticM PreparedFunction := do
  try
    discard <| LeanCert.Meta.reifyWithReport function
  catch exception =>
    return .unsupported function (← exception.toMessageData.toString)
  try
    let reified ← LeanCert.Tactic.Bridge.reifyFunction function
    let capabilities ← LeanCert.Tactic.Bridge.deriveCapabilities reified
    return .ready function reified capabilities
  catch exception =>
    return .deferred function (← exception.toMessageData.toString)

private def functionsOf : SemanticGoal → Array Lean.Expr
  | .bound spec =>
      if spec.normalizedDifference then #[spec.lhs]
      else #[spec.lhs, spec.rhs]
  | .root spec => #[spec.function]
  | .extremum spec => #[spec.function]
  | .discovery spec => #[spec.function]
  | .integral spec => #[spec.integrand]
  | _ => #[]

/-- Prepare all domains represented by a parsed theorem. -/
partial def prepareGoal (semantic : SemanticGoal) :
    TacticM (Except PreparationFailure PreparedGoal) := do
  try
    match semantic with
    | .bound spec =>
        let domains ← spec.boundVars.mapM fun boundVar => prepareInterval boundVar.domain
        let functions ← (functionsOf semantic).mapM prepareFunction
        return .ok { semantic, domains, functions }
    | .root spec =>
        let domain ← prepareInterval spec.boundVar.domain
        let functions ← (functionsOf semantic).mapM prepareFunction
        return .ok { semantic, domains := #[domain], functions }
    | .extremum spec =>
        let domain ← prepareInterval spec.boundVar.domain
        let functions ← (functionsOf semantic).mapM prepareFunction
        return .ok { semantic, domains := #[domain], functions }
    | .discovery spec =>
        let domains ← spec.boundVars.mapM fun boundVar => prepareInterval boundVar.domain
        let functions ← (functionsOf semantic).mapM prepareFunction
        return .ok { semantic, domains, functions }
    | .integral _ =>
        let functions ← (functionsOf semantic).mapM prepareFunction
        return .ok { semantic, functions }
    | .allOf _ children =>
        let preparedChildren ← children.mapM prepareGoal
        let mut domains := #[]
        let mut functions := #[]
        for child in preparedChildren do
          match child with
          | .ok prepared =>
              domains := domains ++ prepared.domains
              functions := functions ++ prepared.functions
          | .error failure => return .error failure
        return .ok { semantic, domains, functions }
    | _ =>
        return .ok { semantic }
  catch exception =>
    return .error {
      source := semantic.original
      detail := ← exception.toMessageData.toString
    }

end LeanCert.Tactic.Semantic
