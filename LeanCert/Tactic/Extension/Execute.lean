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
  compositionSteps : Nat := 0
  verification : LeanCert.Tactic.VerificationUsage
  deriving Inhabited

private structure EnclosedTerm where
  value : Lean.Expr
  interval : IntervalRat
  intervalExpr : Lean.Expr
  membership : Lean.Expr
  observations : Array RegisteredEnclosureObservation := #[]
  compositionSteps : Nat := 0
  verification : LeanCert.Tactic.VerificationUsage := {}

/-- Interval counterpart of `Bridge.realEnvironment`. -/
private def intervalEnvironment (values : List IntervalRat) (index : Nat) : IntervalRat :=
  match values with
  | [value] => value
  | _ => values.getD index (IntervalRat.singleton 0)

private theorem getD_mem_environment
    {values : List ℝ} {intervals : List IntervalRat}
    (h : List.Forall₂ (fun value interval => value ∈ interval) values intervals) :
    ∀ index, values.getD index 0 ∈ intervals.getD index (IntervalRat.singleton 0) := by
  intro index
  induction h generalizing index with
  | nil => simpa using IntervalRat.mem_singleton (0 : ℚ)
  | cons hmem _ ih =>
      cases index with
      | zero => simpa using hmem
      | succ index => simpa using ih index

private theorem environment_mem
    {values : List ℝ} {intervals : List IntervalRat}
    (h : List.Forall₂ (fun value interval => value ∈ interval) values intervals) :
    LeanCert.Engine.envMem
      (LeanCert.Tactic.Bridge.realEnvironment values)
      (intervalEnvironment intervals) := by
  intro index
  cases h with
  | nil =>
      simpa [LeanCert.Tactic.Bridge.realEnvironment, intervalEnvironment] using
        IntervalRat.mem_singleton (0 : ℚ)
  | cons hmem htail =>
      cases htail with
      | nil =>
          simpa [LeanCert.Tactic.Bridge.realEnvironment, intervalEnvironment] using hmem
      | cons hmem' htail' =>
          simpa [LeanCert.Tactic.Bridge.realEnvironment, intervalEnvironment] using
            getD_mem_environment (.cons hmem (.cons hmem' htail')) index

private def withRealLocals {α : Type} (count : Nat)
    (continuation : Array Lean.Expr → TacticM α) : TacticM α := do
  let rec loop (remaining : Nat) (locals : Array Lean.Expr) : TacticM α := do
    match remaining with
    | 0 => continuation locals
    | remaining + 1 =>
        withLocalDeclD `value (mkConst ``Real) fun value =>
          loop remaining (locals.push value)
  loop count #[]

private partial def collectRegisteredRoots (env : Environment) (expression : Lean.Expr)
    (roots : Array Lean.Expr := #[]) : Array Lean.Expr :=
  if expression.getAppFn.constName?.any fun name =>
      !(getUnaryEnclosureRules env name).isEmpty then
    if roots.any (· == expression) then roots else roots.push expression
  else
    match expression with
    | .app fn argument =>
        collectRegisteredRoots env argument (collectRegisteredRoots env fn roots)
    | .mdata _ body | .proj _ _ body => collectRegisteredRoots env body roots
    | .letE _ type value body _ =>
        collectRegisteredRoots env body <|
          collectRegisteredRoots env value <| collectRegisteredRoots env type roots
    | .lam _ type body _ | .forallE _ type body _ =>
        collectRegisteredRoots env body (collectRegisteredRoots env type roots)
    | _ => roots

private def mkMembershipRelation : MetaM Lean.Expr := do
  withLocalDeclD `value (mkConst ``Real) fun value =>
    withLocalDeclD `interval (mkConst ``IntervalRat) fun interval => do
      let membership ← mkAppM ``Membership.mem #[interval, value]
      mkLambdaFVars #[value, interval] membership

private def mkForall₂Membership (memberships : Array Lean.Expr) : MetaM Lean.Expr := do
  let relation ← mkMembershipRelation
  let emptyValues ← mkListLit (mkConst ``Real) []
  let emptyIntervals ← mkListLit (mkConst ``IntervalRat) []
  let mut values := emptyValues
  let mut intervals := emptyIntervals
  let mut proof ← mkAppOptM ``List.Forall₂.nil
    #[some (mkConst ``Real), some (mkConst ``IntervalRat), some relation]
  for membership in memberships.reverse do
    let membershipType ← inferType membership
    let arguments := membershipType.getAppArgs
    if arguments.size < 2 then
      throwError "registered enclosure atom did not have an explicit membership proposition"
    let value := arguments[arguments.size - 1]!
    let interval := arguments[arguments.size - 2]!
    proof ← mkAppOptM ``List.Forall₂.cons #[
      some (mkConst ``Real), some (mkConst ``IntervalRat), some relation,
      some value, some interval, some values, some intervals,
      some membership, some proof]
    values ← mkAppM ``List.cons #[value, values]
    intervals ← mkAppM ``List.cons #[interval, intervals]
  return proof

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

private def proveRatCastComparison (rational real : Lean.Expr)
    (rationalProof : Lean.Expr) : TacticM Lean.Expr := do
  let originalGoals ← getGoals
  let saved ← saveState
  try
    withLocalDeclD `h rational fun h => do
      let proof ← mkFreshExprMVar real MetavarKind.syntheticOpaque
      setGoals [proof.mvarId!]
      let hSyntax ← Term.exprToSyntax h
      evalTactic (← `(tactic| exact_mod_cast $hSyntax))
      unless (← getGoals).isEmpty do
        throwError "rational-cast comparison left proof obligations"
      let proof ← instantiateMVars proof
      if proof.hasMVar then
        throwError "rational-cast comparison contains metavariables"
      let implication ← mkLambdaFVars #[h] proof
      setGoals originalGoals
      return mkApp implication rationalProof
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

private def transportMembershipInterval (value membership targetInterval : Lean.Expr) : MetaM Lean.Expr := do
  let membershipType ← inferType membership
  let some (_, sourceInterval) := explicitMembership? membershipType
    | throwError "registered enclosure interval transport expected interval membership"
  let intervalEquality ← mkDecideProof (← mkAppM ``Eq #[sourceInterval, targetInterval])
  let predicate ← withLocalDeclD `interval (mkConst ``IntervalRat) fun interval => do
    let body ← mkAppM ``Membership.mem #[interval, value]
    mkLambdaFVars #[interval] body
  let transportedEquality ← mkAppM ``congrArg #[predicate, intervalEquality]
  mkAppM ``Eq.mp #[transportedEquality, membership]

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
    compositionSteps := argument.compositionSteps
    verification := argument.verification.combine event.toUsage
  }

private unsafe def encloseTerm (x : Lean.Expr) (hx : Lean.Expr)
    (inputExpr body : Lean.Expr)
    (precision : Int) (taylorDepth : Nat) :
    TacticM (Except RegisteredEnclosureFailure EnclosedTerm) := do
  let body := body.headBeta
  let env ← getEnv
  let rules := body.getAppFn.constName?.map
    (getUnaryEnclosureRules env) |>.getD #[]
  if rules.isEmpty then
    let roots := collectRegisteredRoots env body
    if roots.isEmpty then
      return ← encloseReified x hx inputExpr body taylorDepth
    let mut enclosedRoots : Array EnclosedTerm := #[]
    for root in roots do
      match ← encloseTerm x hx inputExpr root precision taylorDepth with
      | .ok enclosed => enclosedRoots := enclosedRoots.push enclosed
      | .error failure => return .error failure
    -- This temporary tree is inspected only for free-variable occurrence. The
    -- placeholder prevents variables inside registered roots from being counted;
    -- it is never elaborated or used to construct a proof.
    let bodyWithoutRoots := body.replace fun expression =>
      if roots.any (· == expression) then some (mkConst ``True) else none
    let needsInput := bodyWithoutRoots.containsFVar x.fvarId!
    let localCount := roots.size + if needsInput then 1 else 0
    return ← withRealLocals localCount fun locals => do
      let transformed := body.replace fun expression =>
        match roots.findIdx? (· == expression) with
        | some index => some locals[index]!
        | none =>
            if needsInput && expression.isFVar && expression.fvarId! == x.fvarId! then
              some locals[roots.size]!
            else
              none
      let function ← mkLambdaFVars locals transformed
      let reified ← LeanCert.Tactic.Bridge.reifyFunction function
      let capabilities ← LeanCert.Tactic.Bridge.deriveCapabilities reified
      let some supported := capabilities.supportedCore
        | return .error <| .unsupported (toString body)
            "the expression surrounding registered applications is not supported by the core evaluator"
      let mut values := enclosedRoots.map (·.value)
      let mut intervals := enclosedRoots.map (·.intervalExpr)
      let mut memberships := enclosedRoots.map (·.membership)
      if needsInput then
        values := values.push x
        intervals := intervals.push inputExpr
        memberships := memberships.push hx
      let valuesList ← mkListLit (mkConst ``Real) values.toList
      let intervalsList ← mkListLit (mkConst ``IntervalRat) intervals.toList
      let realEnv ← mkAppM ``LeanCert.Tactic.Bridge.realEnvironment #[valuesList]
      let intervalEnv ← mkAppM ``intervalEnvironment #[intervalsList]
      let membershipList ← mkForall₂Membership memberships
      let environmentMembership ← mkAppM ``environment_mem #[membershipList]
      let cfgExpr ← mkAppM ``LeanCert.Engine.EvalConfig.mk #[toExpr taylorDepth]
      let check ← mkAppM ``LeanCert.Engine.checkDomainValid
        #[reified.ast, intervalEnv, cfgExpr]
      let checked ← closeCheck check "registered enclosure composition-domain check"
      let (domainCheckProof, event) ←
        match checked with
        | .ok result => pure result
        | .error (.rejected ..) =>
            return .error <| .domainObstruction "surrounding expression"
              "the checked interval evaluator rejected a partial operation"
        | .error failure => return .error failure
      let domainProof ← mkAppM ``LeanCert.Engine.checkDomainValid_correct
        #[reified.ast, intervalEnv, cfgExpr, domainCheckProof]
      let resultExpr ← mkAppM ``LeanCert.Internal.Rational.evalTotalCore
        #[reified.ast, intervalEnv, cfgExpr]
      let result ← unsafe evalExpr IntervalRat (mkConst ``IntervalRat) resultExpr
      let explicitResultExpr ← mkIntervalExpr result
      let evalMembership ← mkAppM ``LeanCert.Engine.evalIntervalCore_correct
        #[reified.ast, supported, realEnv, intervalEnv, environmentMembership,
          cfgExpr, domainProof]
      let equality ← instantiateMVars (mkAppN reified.evalEq values)
      let membership ← transportMembership equality evalMembership
      let membership ← transportMembershipInterval body membership explicitResultExpr
      let observations := enclosedRoots.foldl
        (fun accumulated enclosed => accumulated ++ enclosed.observations) #[]
      let compositionSteps := enclosedRoots.foldl
        (fun accumulated enclosed => accumulated + enclosed.compositionSteps) 1
      let verification := enclosedRoots.foldl
        (fun accumulated enclosed => accumulated.combine enclosed.verification)
        event.toUsage
      return .ok {
        value := body
        interval := result
        intervalExpr := explicitResultExpr
        membership
        observations
        compositionSteps
        verification
      }
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
  let boundReal ← mkAppOptM ``Rat.cast #[mkConst ``Real, none, toExpr bound]
  let rationalComparison ←
    match comparison, functionOnLeft with
    | .le, true => mkAppM ``LE.le #[toExpr endpoint, toExpr bound]
    | .le, false => mkAppM ``LE.le #[toExpr bound, toExpr endpoint]
    | .lt, true => mkAppM ``LT.lt #[toExpr endpoint, toExpr bound]
    | .lt, false => mkAppM ``LT.lt #[toExpr bound, toExpr endpoint]
    | _, _ => throwError "unsupported registered enclosure comparison"
  let rationalProof ← mkDecideProof rationalComparison
  let castComparison ←
    match comparison, functionOnLeft with
    | .le, true => mkAppM ``LE.le #[endpointReal, boundReal]
    | .le, false => mkAppM ``LE.le #[boundReal, endpointReal]
    | .lt, true => mkAppM ``LT.lt #[endpointReal, boundReal]
    | .lt, false => mkAppM ``LT.lt #[boundReal, endpointReal]
    | _, _ => throwError "unsupported registered enclosure comparison"
  let castProof ← proveRatCastComparison rationalComparison castComparison rationalProof
  let boundEquality ← proveByNormNum (← mkAppM ``Eq #[boundReal, boundExpr])
  let predicate ← withLocalDeclD `bound (mkConst ``Real) fun boundValue => do
    let proposition ←
      if functionOnLeft then
        match comparison with
        | .le => mkAppM ``LE.le #[endpointReal, boundValue]
        | .lt => mkAppM ``LT.lt #[endpointReal, boundValue]
        | _ => throwError "unsupported registered enclosure comparison"
      else
        match comparison with
        | .le => mkAppM ``LE.le #[boundValue, endpointReal]
        | .lt => mkAppM ``LT.lt #[boundValue, endpointReal]
        | _ => throwError "unsupported registered enclosure comparison"
    mkLambdaFVars #[boundValue] proposition
  let endpointProof ← mkAppM ``Eq.mp
    #[← mkAppM ``congrArg #[predicate, boundEquality], castProof]
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
      compositionSteps := enclosed.compositionSteps
      verification := enclosed.verification
    }

end LeanCert.Tactic.Extension
