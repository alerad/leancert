/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Engine.Eval.Core
import LeanCert.Meta.Numeral
import LeanCert.Tactic.Extension.Registry
import LeanCert.Tactic.LeanCert.Bridge.ReifiedFunction
import LeanCert.Tactic.LeanCert.Semantic.Prepare
import LeanCert.Tactic.Verification

/-!
# Execution of registered unary enclosure rules

This module is the tactic-side consumer of the persistent extension registry.
It deliberately leaves candidate generation untrusted: only a successfully
verified checker and its registered soundness theorem contribute to the proof.
-/

open Lean Meta Elab Tactic

namespace LeanCert.Tactic.Extension

open LeanCert.Core
open LeanCert.Tactic.Semantic

initialize registerTraceClass `LeanCert.extension

/-- Expected, typed non-successes from registered enclosure execution. -/
inductive RegisteredEnclosureFailure where
  | notApplicable
  | unsupported (expression detail : String)
  | domainObstruction (operation detail : String)
  | inconclusive (detail : String) (enclosure : Option IntervalRat := none)
  | rejected (checker : Option Name) (enclosure : Option IntervalRat) (detail : String)
  | verificationFailure (detail : String)
  deriving Inhabited

/-- One registered checker proof retained by successful execution. -/
structure RegisteredEnclosureObservation where
  rule : UnaryEnclosureRule
  enclosure : IntervalRat
  verification : LeanCert.Tactic.VerificationUsage
  deriving Inhabited

/-- Retained facts from a successful registered enclosure proof. -/
structure RegisteredEnclosureOutcome where
  enclosure : IntervalRat
  observations : Array RegisteredEnclosureObservation
  verification : LeanCert.Tactic.VerificationUsage
  deriving Inhabited

private structure EnclosedTerm where
  value : Lean.Expr
  interval : IntervalRat
  intervalExpr : Lean.Expr
  membership : Lean.Expr
  observations : Array RegisteredEnclosureObservation := #[]
  verification : LeanCert.Tactic.VerificationUsage := {}

private def mkIntervalExpr (interval : IntervalRat) : MetaM Lean.Expr := do
  let ordered ← mkDecideProof (← mkAppM ``LE.le #[toExpr interval.lo, toExpr interval.hi])
  mkAppM ``IntervalRat.mk #[toExpr interval.lo, toExpr interval.hi, ordered]

private def mkRequestExpr (input : Lean.Expr) (precision : Int)
    (taylorDepth : Nat) : MetaM Lean.Expr :=
  mkAppM ``UnaryEnclosureRequest.mk #[input, toExpr precision, toExpr taylorDepth]

private def proveByNormNum (proposition : Lean.Expr) : TacticM Lean.Expr := do
  let originalGoals ← getGoals
  let saved ← saveState
  let proof ← mkFreshExprMVar proposition MetavarKind.syntheticOpaque
  setGoals [proof.mvarId!]
  try
    evalTactic (← `(tactic| norm_num [LeanCert.Core.IntervalRat.mem_def]))
    unless (← getGoals).isEmpty do
      throwError "exact rational comparison left proof obligations"
    let proof ← instantiateMVars proof
    if proof.hasMVar then
      throwError "exact rational comparison contains metavariables"
    setGoals originalGoals
    return proof
  catch exception =>
    saved.restore
    throw exception

private def explicitMembership? (type : Lean.Expr) : Option (Lean.Expr × Lean.Expr) := do
  guard <| type.getAppFn.constName? == some ``Membership.mem
  let args := type.getAppArgs
  guard <| 2 ≤ args.size
  return (args[args.size - 1]!, args[args.size - 2]!)

private def closeCheck (check : Lean.Expr) (role : String) :
    TacticM (Except RegisteredEnclosureFailure (Lean.Expr × VerificationEvent)) := do
  let proposition ← mkAppM ``Eq #[check, mkConst ``Bool.true]
  let proof ← mkFreshExprMVar proposition MetavarKind.syntheticOpaque
  let cfg ← VerificationConfig.current
  match ← closeCertificateGoalTyped cfg proof.mvarId! (tacticName := role) with
  | .accepted event =>
      return .ok (← instantiateMVars proof, event)
  | .rejected =>
      return .error <| .rejected none none s!"{role} evaluated to false"
  | .failed failure =>
      return .error <| .verificationFailure (failure.message role)

private def transportMembership (equality membership : Lean.Expr) : MetaM Lean.Expr := do
  let equalityType ← inferType equality
  let some (_, _, rhs) := equalityType.eq?
    | throwError "registered enclosure transport expected an equality"
  let membershipType ← inferType membership
  let some (_, interval) := explicitMembership? membershipType
    | throwError "registered enclosure transport expected interval membership"
  let predicate ← withLocalDeclD `value (mkConst ``Real) fun value => do
    let body ← mkAppM ``Membership.mem #[interval, value]
    mkLambdaFVars #[value] body
  let transportedEquality ← mkAppM ``congrArg #[predicate, equality]
  let transported ← mkAppM ``Eq.mp #[transportedEquality, membership]
  let expected ← mkAppM ``Membership.mem #[interval, rhs]
  let actual ← inferType transported
  unless ← isDefEq actual expected do
    throwError "registered enclosure membership transport produced an unexpected type"
  return transported

private def encloseReified (x : Lean.Expr) (hx : Lean.Expr)
    (inputExpr body : Lean.Expr)
    (taylorDepth : Nat) : TacticM (Except RegisteredEnclosureFailure EnclosedTerm) := do
  let function ← mkLambdaFVars #[x] body
  try
    discard <| LeanCert.Meta.reifyWithReport function
  catch exception =>
    return .error <| .unsupported (toString body)
      (← exception.toMessageData.toString)
  -- Once syntax reification succeeded, bridge-construction failures are
  -- unexpected and must escape to the typed solver boundary as internal errors.
  let reified ← LeanCert.Tactic.Bridge.reifyFunction function
  let capabilities ← LeanCert.Tactic.Bridge.deriveCapabilities reified
  let some supported := capabilities.supportedCore
    | return .error <| .unsupported (toString body)
        "the inner expression has no core interval-support proof"
  let cfgExpr ← mkAppM ``LeanCert.Engine.EvalConfig.mk #[toExpr taylorDepth]
  let check ← mkAppM ``LeanCert.Engine.checkDomainValid1 #[reified.ast, inputExpr, cfgExpr]
  let checked ← closeCheck check "registered enclosure inner-domain check"
  let (domainCheckProof, event) ←
    match checked with
    | .ok result => pure result
    | .error (.rejected ..) =>
        return .error <| .domainObstruction "inner expression"
          "the checked interval evaluator rejected a partial operation"
    | .error failure => return .error failure
  let domainProof ← mkAppM ``LeanCert.Engine.checkDomainValid1_correct
    #[reified.ast, inputExpr, cfgExpr, domainCheckProof]
  let resultExpr ← mkAppM ``LeanCert.Internal.Rational.evalTotalCore1
    #[reified.ast, inputExpr, cfgExpr]
  let result ← unsafe evalExpr IntervalRat (mkConst ``IntervalRat) resultExpr
  let evalMembership ← mkAppM ``LeanCert.Engine.evalIntervalCore1_correct
    #[reified.ast, supported, x, inputExpr, hx, cfgExpr, domainProof]
  let equality ← instantiateMVars (mkApp reified.evalEq x)
  let membership ← transportMembership equality evalMembership
  return .ok {
    value := body
    interval := result
    intervalExpr := resultExpr
    membership
    verification := event.toUsage
  }

private unsafe def runCandidate (rule : UnaryEnclosureRule)
    (request : UnaryEnclosureRequest) (requestExpr : Lean.Expr)
    (argument : EnclosedTerm) :
    TacticM (Except RegisteredEnclosureFailure EnclosedTerm) := do
  let candidateFn ← evalExpr UnaryEnclosureCandidate
    (mkConst ``UnaryEnclosureCandidate) (mkConst rule.candidateName)
  let output ←
    match candidateFn request with
    | .ok output => pure output
    | .error (.domainObstruction detail) =>
        return .error <| .domainObstruction rule.functionName.toString detail
    | .error (.inconclusive detail) =>
        return .error <| .inconclusive detail
  let outputExpr ← mkIntervalExpr output
  let check ← mkAppM rule.checkerName #[requestExpr, outputExpr]
  let checked ← closeCheck check s!"registered enclosure checker `{rule.checkerName}`"
  let (checkProof, event) ←
    match checked with
    | .ok result => pure result
    | .error (.rejected ..) =>
        return .error <| .rejected (some rule.checkerName) (some output)
          "The registered candidate was rejected by its checker."
    | .error failure => return .error failure
  let proof := mkAppN (mkConst rule.theoremName)
    #[requestExpr, argument.value, outputExpr, argument.membership, checkProof]
  discard <| inferType proof
  return .ok {
    value := mkApp (mkConst rule.functionName) argument.value
    interval := output
    intervalExpr := outputExpr
    membership := proof
    observations := argument.observations.push {
      rule
      enclosure := output
      verification := event.toUsage
    }
    verification := argument.verification.combine event.toUsage
  }

private unsafe def encloseTerm (x : Lean.Expr) (hx : Lean.Expr)
    (inputExpr body : Lean.Expr)
    (precision : Int) (taylorDepth : Nat) :
    TacticM (Except RegisteredEnclosureFailure EnclosedTerm) := do
  let body := body.headBeta
  let rules := body.getAppFn.constName?.map
    (getUnaryEnclosureRules (← getEnv)) |>.getD #[]
  if rules.isEmpty then
    return ← encloseReified x hx inputExpr body taylorDepth
  let arguments := body.getAppArgs
  unless arguments.size == 1 do
    return .error <| .unsupported (toString body)
      "registered unary enclosure function was not applied to exactly one argument"
  let argumentResult ← encloseTerm x hx inputExpr arguments[0]! precision taylorDepth
  let argument ←
    match argumentResult with
    | .ok argument => pure argument
    | .error failure => return .error failure
  let request : UnaryEnclosureRequest := {
    input := argument.interval
    precision
    taylorDepth
  }
  let requestExpr ← mkRequestExpr argument.intervalExpr precision taylorDepth
  let mut lastFailure : Option RegisteredEnclosureFailure := none
  for rule in rules do
    match ← runCandidate rule request requestExpr argument with
    | .ok result => return .ok result
    | .error failure@(.domainObstruction ..) => return .error failure
    | .error failure@(.verificationFailure ..) => return .error failure
    | .error failure => lastFailure := some failure
  return .error <| lastFailure.getD <| .inconclusive
    s!"no registered enclosure rule for `{body.getAppFn}` produced a certificate"

private def containsRegisteredFunction (env : Environment) (expression : Lean.Expr) : Bool :=
  (expression.find? fun subterm =>
    subterm.getAppFn.constName?.any fun name =>
      !(getUnaryEnclosureRules env name).isEmpty).isSome

private def finalComparisonProof (comparison : Comparison) (functionOnLeft : Bool)
    (bound : ℚ) (boundExpr : Lean.Expr) (enclosed : EnclosedTerm) :
    TacticM (Except RegisteredEnclosureFailure Lean.Expr) := do
  let endpoint := if functionOnLeft then enclosed.interval.hi else enclosed.interval.lo
  let comparisonHolds :=
    match comparison, functionOnLeft with
    | .le, true => decide (endpoint ≤ bound)
    | .le, false => decide (bound ≤ endpoint)
    | .lt, true => decide (endpoint < bound)
    | .lt, false => decide (bound < endpoint)
    | _, _ => false
  unless comparisonHolds do
    return .error <| .inconclusive
      s!"registered enclosure [{enclosed.interval.lo}, {enclosed.interval.hi}] does not prove the requested bound"
      (some enclosed.interval)
  let endpointReal ← mkAppOptM ``Rat.cast #[mkConst ``Real, none, toExpr endpoint]
  let endpointComparison ←
    match comparison, functionOnLeft with
    | .le, true => mkAppM ``LE.le #[endpointReal, boundExpr]
    | .le, false => mkAppM ``LE.le #[boundExpr, endpointReal]
    | .lt, true => mkAppM ``LT.lt #[endpointReal, boundExpr]
    | .lt, false => mkAppM ``LT.lt #[boundExpr, endpointReal]
    | _, _ => throwError "unsupported registered enclosure comparison"
  let endpointProof ← proveByNormNum endpointComparison
  let membershipType ← inferType enclosed.membership
  let some (_, _) := explicitMembership? membershipType
    | throwError "registered enclosure theorem did not produce interval membership"
  let side ←
    if functionOnLeft then mkAppM ``And.right #[enclosed.membership]
    else mkAppM ``And.left #[enclosed.membership]
  let proof ←
    match comparison, functionOnLeft with
    | .le, true => mkAppM ``le_trans #[side, endpointProof]
    | .le, false => mkAppM ``le_trans #[endpointProof, side]
    | .lt, true => mkAppM ``lt_of_le_of_lt #[side, endpointProof]
    | .lt, false => mkAppM ``lt_of_lt_of_le #[endpointProof, side]
    | _, _ => throwError "unsupported registered enclosure comparison"
  return .ok proof

/-- Try to prove a unary quantified bound through imported enclosure rules. -/
unsafe def registeredEnclosureBoundCoreTyped (prepared : PreparedGoal)
    (precision : Int) (taylorDepth : Nat) :
    TacticM (Except RegisteredEnclosureFailure RegisteredEnclosureOutcome) := do
  let .bound spec := prepared.semantic
    | return .error .notApplicable
  unless spec.boundVars.size == 1 && prepared.domains.size == 1 do
    return .error .notApplicable
  unless spec.comparison == .le || spec.comparison == .lt do
    return .error .notApplicable
  let .closedRat _ inputExpr membershipIff := prepared.domains[0]!
    | return .error .notApplicable
  let goal ← getMainGoal
  let (xId, goal) ← goal.intro1P
  let (hxSourceId, goal) ← goal.intro1P
  setGoals [goal]
  goal.withContext do
    let x := mkFVar xId
    let hxSource := mkFVar hxSourceId
    let iffAt ← mkAppM' membershipIff #[x]
    let hx ← mkAppM ``Iff.mp #[iffAt, hxSource]
    trace[LeanCert.extension] "transported source membership"
    let lhs := (mkApp spec.lhs x).headBeta
    let rhs := (mkApp spec.rhs x).headBeta
    let lhsUses := lhs.containsFVar x.fvarId!
    let rhsUses := rhs.containsFVar x.fvarId!
    if lhsUses == rhsUses then
      return .error .notApplicable
    let functionOnLeft := lhsUses
    let functionBody := if functionOnLeft then lhs else rhs
    let boundBody := if functionOnLeft then rhs else lhs
    unless containsRegisteredFunction (← getEnv) functionBody do
      return .error .notApplicable
    let some bound ← LeanCert.Meta.Numeral.toRat? boundBody
      | return .error <| .unsupported (toString boundBody)
          "registered enclosure bounds currently require a rational constant on the other side"
    let enclosed ←
      match ← encloseTerm x hx inputExpr functionBody precision taylorDepth with
      | .ok enclosed => pure enclosed
      | .error failure => return .error failure
    trace[LeanCert.extension] "constructed registered enclosure proof"
    if enclosed.observations.isEmpty then
      return .error .notApplicable
    let finalProof ←
      match ← finalComparisonProof spec.comparison functionOnLeft bound boundBody enclosed with
      | .ok proof => pure proof
      | .error failure => return .error failure
    trace[LeanCert.extension] "constructed final comparison proof"
    goal.assign finalProof
    replaceMainGoal []
    return .ok {
      enclosure := enclosed.interval
      observations := enclosed.observations
      verification := enclosed.verification
    }

end LeanCert.Tactic.Extension
