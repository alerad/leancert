/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import Mathlib.Tactic
import LeanCert.Engine.Algebra.QPolyIntegral
import LeanCert.Meta.Numeral
import LeanCert.Meta.ProveContinuous
import LeanCert.Meta.ProveSupported
import LeanCert.Tactic.LeanCert.Bridge.ReifiedFunction
import LeanCert.Tactic.LeanCert.Config
import LeanCert.Tactic.LeanCert.Normalize
import LeanCert.Validity.Integration

/-!
# Natural integral goals

This module parses ordinary interval-integral equalities and inequalities.  It
first tries exact rational-polynomial integration, then falls back to LeanCert's
checked partition search for non-polynomial expressions.
-/

open Lean Meta Elab Tactic

namespace LeanCert.Tactic

open LeanCert.Core LeanCert.Engine LeanCert.Meta

inductive IntegralComparison where
  | eq | upper | lower | upperStrict | lowerStrict
  deriving Repr, BEq

structure ParsedIntegralGoal where
  comparison : IntegralComparison
  targetIntegral : Lean.Expr
  integrand : Lean.Expr
  lo : Lean.Expr
  hi : Lean.Expr
  bound : Lean.Expr

/-- Integral proof route retained for reporting. -/
inductive IntegralRoute where
  | exactRational
  | checkedPartitions
  deriving Repr, Inhabited, BEq

/-- Runtime facts retained by one integral proof. -/
structure IntegralOutcome where
  route : IntegralRoute
  checker : Name
  verifier : Name
  verification : Option VerificationUsage := none
  partitionStart : Option Nat := none
  partitionMaximum : Option Nat := none
  chosenPartitions : Option Nat := none
  attempts : Option Nat := none
  enclosure : Option IntervalRat := none
  deriving Inhabited

/-- Typed failures from exact and partition-based integral solvers. -/
inductive IntegralFailure where
  | unsupported (detail : String)
  | domainObstruction (detail : String)
  | exhausted (start maximum : Nat) (lastPartitions : Option Nat)
      (lastEnclosure : Option IntervalRat) (attempts : Nat)
  | rejected (checker : Name) (enclosure : Option IntervalRat)
  | verificationFailure (detail : String)
  | transportFailure (detail : String)
  | internalFailure (detail : String)
  deriving Inhabited, Repr

private def parseIntegralTerm? (e : Lean.Expr) : Option (Lean.Expr × Lean.Expr × Lean.Expr) :=
  if e.getAppFn.constName? == some ``intervalIntegral && e.getAppNumArgs >= 4 then
    let args := e.getAppArgs
    -- The final explicit arguments are function, lower endpoint, upper
    -- endpoint, and measure; universe/typeclass parameters precede them.
    some (args[args.size - 4]!, args[args.size - 3]!, args[args.size - 2]!)
  else none

/-- Parse `integral = c`, `integral ≤ c`, and `c ≤ integral`, including the
corresponding reversed equality.  Bounds and endpoints are validated as
rationals by the solver rather than by classification. -/
def parseNaturalIntegralGoal (goal : Lean.Expr) : MetaM (Option ParsedIntegralGoal) := do
  let parseSide (comparison : IntegralComparison) (integ bound : Lean.Expr) :=
    match parseIntegralTerm? integ with
    | some (fexpr, lo, hi) =>
        some ⟨comparison, integ, fexpr, lo, hi, bound⟩
    | none => none
  let fn := goal.getAppFn
  let args := goal.getAppArgs
  if fn.isConstOf ``Eq && args.size >= 3 then
    let lhs := args[args.size - 2]!
    let rhs := args[args.size - 1]!
    if let some parsed := parseSide .eq lhs rhs then return some parsed
    if let some parsed := parseSide .eq rhs lhs then return some parsed
    return none
  if fn.isConstOf ``LE.le && args.size >= 4 then
    let lhs := args[args.size - 2]!
    let rhs := args[args.size - 1]!
    if let some parsed := parseSide .upper lhs rhs then return some parsed
    if let some parsed := parseSide .lower rhs lhs then return some parsed
    return none
  if fn.isConstOf ``LT.lt && args.size >= 4 then
    let lhs := args[args.size - 2]!
    let rhs := args[args.size - 1]!
    if let some parsed := parseSide .upperStrict lhs rhs then return some parsed
    if let some parsed := parseSide .lowerStrict rhs lhs then return some parsed
    return none
  if fn.isConstOf ``GE.ge && args.size >= 4 then
    let lhs := args[args.size - 2]!
    let rhs := args[args.size - 1]!
    if let some parsed := parseSide .lower lhs rhs then return some parsed
    if let some parsed := parseSide .upper rhs lhs then return some parsed
    return none
  if fn.isConstOf ``GT.gt && args.size >= 4 then
    let lhs := args[args.size - 2]!
    let rhs := args[args.size - 1]!
    if let some parsed := parseSide .lowerStrict lhs rhs then return some parsed
    if let some parsed := parseSide .upperStrict rhs lhs then return some parsed
    return none
  return none

/-- Recognize a single natural integral comparison or a conjunction of them. -/
partial def isNaturalIntegralGoal (goal : Lean.Expr) : MetaM Bool := do
  if (← parseNaturalIntegralGoal goal).isSome then return true
  if goal.isAppOfArity ``And 2 then
    let args := goal.getAppArgs
    return (← isNaturalIntegralGoal args[0]!) && (← isNaturalIntegralGoal args[1]!)
  return false

private def exactIntegralAttemptTyped (parsed : ParsedIntegralGoal) :
    TacticM (Except IntegralFailure IntegralOutcome) := do
  let some a ← LeanCert.Meta.Numeral.toRat? parsed.lo
    | return .error <| .unsupported "lower endpoint is not rational"
  let some b ← LeanCert.Meta.Numeral.toRat? parsed.hi
    | return .error <| .unsupported "upper endpoint is not rational"
  let reified ←
    try Bridge.reifyFunction parsed.integrand
    catch e =>
      return .error <| .unsupported (← e.toMessageData.toString)
  let astValue ← unsafe evalExpr LeanCert.Core.Expr (mkConst ``LeanCert.Core.Expr) reified.ast
  let some poly := QPoly.ofExpr astValue
    | return .error <| .unsupported "integrand is not a rational polynomial"
  let value := poly.integralRat a b
  try
    let checkType ← mkAppM ``Eq #[
      ← mkAppM ``QPoly.checkExactIntegral #[reified.ast, toExpr a, toExpr b, toExpr value],
      mkConst ``Bool.true]
    let checkProof ← mkDecideProof checkType
    let proof ← mkAppM ``QPoly.integral_eq_of_check
      #[reified.ast, toExpr a, toExpr b, toExpr value, checkProof]
    let proofSyntax ← Term.exprToSyntax proof
    let evalEqSyntax ← Term.exprToSyntax reified.evalEq
    evalTactic (← `(tactic|
      have hIntegral := ($proofSyntax);
      have hfun := funext ($evalEqSyntax);
      rw [← hfun];
      norm_num [Rat.divInt_eq_div] at hIntegral ⊢ <;>
        first | exact hIntegral | linarith [hIntegral]))
    return .ok {
      route := .exactRational
      checker := ``QPoly.checkExactIntegral
      verifier := ``QPoly.integral_eq_of_check
    }
  catch e =>
    return .error <| .transportFailure (← e.toMessageData.toString)

private def mkIntervalRatExpr (a b : ℚ) : MetaM Lean.Expr := do
  unless a ≤ b do
    throwError "numerical integral bounds currently require lower endpoint ≤ upper endpoint"
  let leType ← mkAppM ``LE.le #[toExpr a, toExpr b]
  let leProof ← mkDecideProof leType
  mkAppM ``IntervalRat.mk #[toExpr a, toExpr b, leProof]

private partial def numericalIntegralAttemptTyped (parsed : ParsedIntegralGoal)
    (startN maxN : Nat) : TacticM (Except IntegralFailure IntegralOutcome) := do
  let some a ← LeanCert.Meta.Numeral.toRat? parsed.lo
    | return .error <| .unsupported "lower endpoint is not rational"
  let some b ← LeanCert.Meta.Numeral.toRat? parsed.hi
    | return .error <| .unsupported "upper endpoint is not rational"
  let some c ← LeanCert.Meta.Numeral.toRat? parsed.bound
    | return .error <| .unsupported "comparison bound is not rational"
  if b < a then
    let args := parsed.targetIntegral.getAppArgs
    unless args.size >= 4 do
      throwError "numerical integral: malformed interval-integral application"
    let mut swappedArgs := args
    swappedArgs := swappedArgs.set! (args.size - 3) parsed.hi
    swappedArgs := swappedArgs.set! (args.size - 2) parsed.lo
    let swapped := mkAppN parsed.targetIntegral.getAppFn swappedArgs
    let negBound ← mkAppM ``Neg.neg #[parsed.bound]
    let swappedSyntax ← Term.exprToSyntax swapped
    let negBoundSyntax ← Term.exprToSyntax negBound
    evalTactic <| ← match parsed.comparison with
      | .upper => `(tactic|
          rw [intervalIntegral.integral_symm];
          suffices $negBoundSyntax ≤ $swappedSyntax by linarith)
      | .lower => `(tactic|
          rw [intervalIntegral.integral_symm];
          suffices $swappedSyntax ≤ $negBoundSyntax by linarith)
      | .upperStrict => `(tactic|
          rw [intervalIntegral.integral_symm];
          suffices $negBoundSyntax < $swappedSyntax by linarith)
      | .lowerStrict => `(tactic|
          rw [intervalIntegral.integral_symm];
          suffices $swappedSyntax < $negBoundSyntax by linarith)
      | .eq => `(tactic|
          rw [intervalIntegral.integral_symm];
          suffices $swappedSyntax = $negBoundSyntax by linarith)
    let transformedComparison := match parsed.comparison with
      | .upper => IntegralComparison.lower
      | .lower => .upper
      | .upperStrict => .lowerStrict
      | .lowerStrict => .upperStrict
      | .eq => .eq
    let transformed : ParsedIntegralGoal := {
      comparison := transformedComparison
      targetIntegral := swapped
      integrand := parsed.integrand
      lo := parsed.hi
      hi := parsed.lo
      bound := negBound
    }
    match ← numericalIntegralAttemptTyped transformed startN maxN with
    | .ok outcome =>
        return .ok {
          outcome with
          enclosure := outcome.enclosure.map IntervalRat.neg
        }
    | .error failure => return .error failure
  if parsed.comparison == .eq then
    return .error <| .unsupported "numerical interval enclosures do not certify exact equality"
  if parsed.comparison == .upperStrict || parsed.comparison == .lowerStrict then
    return .error <| .unsupported
      "strict numerical integral bounds require a margin certificate"
  let reified ←
    try reifyWithReport parsed.integrand
    catch e =>
      return .error <| .unsupported
        s!"integrand is not supported: {← e.toMessageData.toString}"
  let supportProof ←
    try mkSupportedCoreProof reified.expr
    catch e =>
      return .error <| .unsupported
        s!"integrand is outside the supported expression language: \
          {← e.toMessageData.toString}"
  let interval ← mkIntervalRatExpr a b
  let domainProof ←
    try mkContinuousDomainValidProof reified.expr interval
    catch e =>
      return .error <| .domainObstruction
        s!"could not establish the integrand's mathematical domain: \
          {← e.toMessageData.toString}"
  let integrableProof ← mkAppM ``LeanCert.Validity.Integration.exprSupportedCore_intervalIntegrable
    #[reified.expr, supportProof, interval, domainProof]
  if startN == 0 then
    return .error <| .unsupported "partition search requires a positive starting count"
  let (theoremName, checkerName) :=
    if parsed.comparison == .upper then
      (``LeanCert.Validity.Integration.integral_partition_upper_of_check,
        ``LeanCert.Validity.Integration.checkIntegralPartitionUpperBound)
    else
      (``LeanCert.Validity.Integration.integral_partition_lower_of_check,
        ``LeanCert.Validity.Integration.checkIntegralPartitionLowerBound)
  let searchName :=
    if parsed.comparison == .upper then
      ``LeanCert.Validity.Integration.searchPartitionUpperCandidate
    else
      ``LeanCert.Validity.Integration.searchPartitionLowerCandidate
  let searchExpr ← mkAppM searchName
    #[reified.expr, interval, toExpr startN, toExpr maxN, toExpr c]
  let searchResult ← unsafe evalExpr
    LeanCert.Validity.Integration.IntegralPartitionSearchResult
    (mkConst ``LeanCert.Validity.Integration.IntegralPartitionSearchResult) searchExpr
  let (chosen, enclosure, attempts) ←
    match searchResult with
    | .success chosen enclosure attempts => pure (chosen, enclosure, attempts)
    | .exhausted lastPartitions lastEnclosure attempts =>
        return .error <| .exhausted startN maxN lastPartitions lastEnclosure attempts
    | .domainObstruction partitions attempts =>
        return .error <| .domainObstruction
          s!"partition evaluation failed at n={partitions} after {attempts} attempt(s)"
    | .invalidStart =>
        return .error <| .unsupported "partition search requires a positive starting count"
  let checker ← mkAppM checkerName
    #[reified.expr, interval, toExpr chosen, toExpr c]
  let checkType ← mkAppM ``Eq #[checker, mkConst ``Bool.true]
  let checkProof ← mkFreshExprMVar checkType
  let event ←
    match ← closeCertificateGoalTyped (← VerificationConfig.current)
        checkProof.mvarId! (tacticName := "integral_search") with
    | .accepted event => pure event
    | .rejected => return .error <| .rejected checkerName (some enclosure)
    | .failed failure =>
        return .error <| .verificationFailure (failure.message "integral_search")
  let chosenPositiveType ← mkAppM ``LT.lt #[toExpr 0, toExpr chosen]
  let chosenPositive ← mkDecideProof chosenPositiveType
  let proof ← mkAppM theoremName #[reified.expr, interval, toExpr chosen,
    chosenPositive, toExpr c, checkProof, integrableProof]
  try
    let proofSyntax ← Term.exprToSyntax proof
    unfoldReifiedDefinitions reified.unfolded
    evalTactic (← `(tactic|
      have hIntegral := ($proofSyntax);
      simp_all only [
        LeanCert.Core.Expr.eval_add,
        LeanCert.Core.Expr.eval_mul,
        LeanCert.Core.Expr.eval_neg,
        LeanCert.Core.Expr.eval_inv,
        LeanCert.Core.Expr.eval_const,
        LeanCert.Core.Expr.eval_var,
        LeanCert.Core.Expr.eval_sin,
        LeanCert.Core.Expr.eval_cos,
        LeanCert.Core.Expr.eval_exp,
        LeanCert.Core.Expr.eval_log,
        LeanCert.Core.Expr.eval_atan,
        LeanCert.Core.Expr.eval_arsinh,
        LeanCert.Core.Expr.eval_sqrt,
        Rat.divInt_eq_div,
        sq, pow_two, pow_succ, pow_zero, pow_one,
        sub_eq_add_neg, div_eq_mul_inv, one_mul, mul_one];
      first
      | exact hIntegral
      | (convert hIntegral using 1 <;> norm_num [Rat.divInt_eq_div])))
    return .ok {
      route := .checkedPartitions
      checker := checkerName
      verifier := theoremName
      verification := some event.toUsage
      partitionStart := some startN
      partitionMaximum := some maxN
      chosenPartitions := some chosen
      attempts := some attempts
      enclosure := some enclosure
    }
  catch e =>
    return .error <| .transportFailure (← e.toMessageData.toString)

/-- Exact integral strategy used by the semantic router. Every returned failure
restores the complete state from entry, including successful earlier
conjuncts. -/
partial def integralExactCoreTyped : TacticM (Except IntegralFailure (Array IntegralOutcome)) := do
  let original ← saveState
  let rec go : TacticM (Except IntegralFailure (Array IntegralOutcome)) := do
    let goal ← getMainGoal
    let goalType ← goal.getType
    if goalType.isAppOfArity ``And 2 then
      evalTactic (← `(tactic| constructor))
      let goals ← getGoals
      let mut outcomes := #[]
      for subgoal in goals do
        setGoals [subgoal]
        match ← go with
        | .ok child => outcomes := outcomes ++ child
        | .error failure => return .error failure
      return .ok outcomes
    else
      let some parsed ← parseNaturalIntegralGoal goalType
        | return .error <| .unsupported
            "expected an ordinary interval-integral equality or inequality"
      match ← exactIntegralAttemptTyped parsed with
      | .ok outcome => return .ok #[outcome]
      | .error failure => return .error failure
  try
    match ← go with
    | .ok outcomes => return .ok outcomes
    | .error failure =>
        original.restore
        return .error failure
  catch e =>
    original.restore
    return .error <| .internalFailure (← e.toMessageData.toString)

/-- Checked partition-search strategy used by the semantic router. -/
partial def integralSearchCoreTyped (startN maxN : Nat) :
    TacticM (Except IntegralFailure (Array IntegralOutcome)) := do
  let original ← saveState
  let rec go : TacticM (Except IntegralFailure (Array IntegralOutcome)) := do
    let goal ← getMainGoal
    let goalType ← goal.getType
    if goalType.isAppOfArity ``And 2 then
      evalTactic (← `(tactic| constructor))
      let goals ← getGoals
      let mut outcomes := #[]
      for subgoal in goals do
        setGoals [subgoal]
        match ← go with
        | .ok child => outcomes := outcomes ++ child
        | .error failure => return .error failure
      return .ok outcomes
    else
      let some parsed ← parseNaturalIntegralGoal goalType
        | return .error <| .unsupported
            "expected an ordinary interval-integral inequality"
      match ← numericalIntegralAttemptTyped parsed startN maxN with
      | .ok outcome => return .ok #[outcome]
      | .error failure => return .error failure
  try
    match ← go with
    | .ok outcomes => return .ok outcomes
    | .error failure =>
        original.restore
        return .error failure
  catch e =>
    original.restore
    return .error <| .internalFailure (← e.toMessageData.toString)

syntax (name := integralExactTac) "integral_exact" : tactic

@[tactic integralExactTac]
unsafe def elabIntegralExact : Tactic := fun _ => do
  match ← integralExactCoreTyped with
  | .ok _ => pure ()
  | .error failure => throwError "integral_exact: {repr failure}"

end LeanCert.Tactic
