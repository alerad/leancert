/-
Copyright (c) 2024 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Tactic.IntervalAuto.Basic
import LeanCert.Tactic.Verification
import LeanCert.Tactic.IntervalAuto.Bound
import LeanCert.Validity.Bounds
import LeanCert.Engine.Optimization.BoundVerify

/-!
# Subdivision-aware Bound Proving

The `interval_bound_subdiv` tactic uses interval subdivision when the direct
approach is too coarse. Candidate evaluation and certificate verification are
separate: search evaluates each node once, while every retained leaf closes
one fixed Boolean certificate exactly once.
-/

open Lean Meta Elab Tactic Term

namespace LeanCert.Tactic.Auto

open LeanCert.Meta
open LeanCert.Core
open LeanCert.Engine
open LeanCert.Validity

/-- Comparison certified by a subdivision proof tree. -/
inductive SubdivisionComparison where
  | upper
  | lower
  | strictUpper
  | strictLower
  deriving DecidableEq, Repr, Inhabited

/-- Runtime facts retained by one successful subdivision proof tree. -/
structure SubdivisionExecution where
  verification : LeanCert.Tactic.VerificationUsage := {}
  deepestDepthUsed : Nat := 0
  boxesExamined : Nat := 0
  certifiedLeaves : Nat := 0
  deriving Inhabited

/-- A proof together with the execution facts that produced it. -/
structure SubdivisionProof where
  proof : Lean.Expr
  enclosure : IntervalRat
  execution : SubdivisionExecution

/-- Reported result of the public subdivision strategy. Every retained leaf
uses the Rational interval backend. -/
structure SubdivisionOutcome where
  comparison : SubdivisionComparison
  taylorDepth : Nat
  maxDepth : Nat
  finalEnclosure : IntervalRat
  execution : SubdivisionExecution
  checker : Name
  verifier : Name
  deriving Inhabited

/-- Typed failures from recursive subdivision. -/
inductive SubdivisionFailure where
  | unsupported (expression detail : String)
  | domainObstruction (domain : Lean.Expr) (operation detail : String)
  | exhausted (maxDepth boxesExamined deepestDepth : Nat)
      (bestEnclosure : Option IntervalRat)
  | rejected (checker : Name) (detail : String)
  | transportFailure (detail : String)
  | internalFailure (detail : String)
  deriving Inhabited, Repr

private def throwSubdivisionFailure : SubdivisionFailure → TacticM α
  | .unsupported expression detail =>
      throwError "interval_bound_subdiv: unsupported expression {expression}:\n{detail}"
  | .domainObstruction _ operation detail =>
      throwError "interval_bound_subdiv: domain obstruction while checking {operation}:\n{detail}"
  | .exhausted maxDepth boxes deepest enclosure =>
      let enclosureDetail := match enclosure with
        | some I => s!"; last enclosure [{I.lo}, {I.hi}]"
        | none => ""
      throwError "interval_bound_subdiv: subdivision exhausted at configured depth \
        {maxDepth} after examining {boxes} boxes (deepest depth {deepest})\
        {enclosureDetail}"
  | .rejected checker detail =>
      throwError "interval_bound_subdiv: certificate {checker} was rejected:\n{detail}"
  | .transportFailure detail =>
      throwError "interval_bound_subdiv: proof transport failed:\n{detail}"
  | .internalFailure detail =>
      throwError "interval_bound_subdiv: internal certificate failure:\n{detail}"

private def SubdivisionExecution.combineChildren
    (depthUsed : Nat) (left right : SubdivisionExecution) : SubdivisionExecution := {
  verification := left.verification.combine right.verification
  deepestDepthUsed := max depthUsed
    (max left.deepestDepthUsed right.deepestDepthUsed)
  boxesExamined := 1 + left.boxesExamined + right.boxesExamined
  certifiedLeaves := left.certifiedLeaves + right.certifiedLeaves
}

private def SubdivisionFailure.addExamined
    (prior : SubdivisionExecution) : SubdivisionFailure → SubdivisionFailure
  | .exhausted maxDepth boxes deepest enclosure =>
      .exhausted maxDepth (prior.boxesExamined + boxes)
        (max prior.deepestDepthUsed deepest) enclosure
  | failure => failure

private def subdivisionChecker : SubdivisionComparison → Name
  | .upper => ``LeanCert.Validity.checkUpperBound
  | .lower => ``LeanCert.Validity.checkLowerBound
  | .strictUpper => ``LeanCert.Validity.checkStrictUpperBound
  | .strictLower => ``LeanCert.Validity.checkStrictLowerBound

private def subdivisionVerifier : SubdivisionComparison → Name
  | .upper => ``Validity.verify_upper_bound_Icc_core
  | .lower => ``Validity.verify_lower_bound_Icc_core
  | .strictUpper => ``Validity.verify_strict_upper_bound_Icc_core
  | .strictLower => ``Validity.verify_strict_lower_bound_Icc_core

private def subdivisionCombiner : SubdivisionComparison → Name
  | .upper => ``Validity.combine_upper_bound_general_split
  | .lower => ``Validity.combine_lower_bound_general_split
  | .strictUpper => ``Validity.combine_strict_upper_bound_general_split
  | .strictLower => ``Validity.combine_strict_lower_bound_general_split

private def enclosureProves (comparison : SubdivisionComparison)
    (enclosure : IntervalRat) (bound : ℚ) : Bool :=
  match comparison with
  | .upper => decide (enclosure.hi ≤ bound)
  | .lower => decide (bound ≤ enclosure.lo)
  | .strictUpper => decide (enclosure.hi < bound)
  | .strictLower => decide (bound < enclosure.lo)

/-- Evaluate one search node once, retaining a concrete enclosure for
classification and telemetry. This is untrusted candidate generation; final
acceptance still goes through the fixed Boolean checker. -/
private unsafe def evaluateSubdivisionNode (ast interval cfgExpr : Lean.Expr) :
    TacticM (Except SubdivisionFailure IntervalRat) := do
  let domainCheck ← mkAppM ``LeanCert.Engine.checkDomainValid1 #[ast, interval, cfgExpr]
  let domainValid ←
    try unsafe evalExpr Bool (mkConst ``Bool) domainCheck
    catch e =>
      return .error <| .internalFailure (← e.toMessageData.toString)
  unless domainValid do
    return .error <| .domainObstruction interval
      "Rational interval evaluation" "the checked evaluator rejected this interval"
  let enclosureExpr ← mkAppM ``LeanCert.Internal.Rational.evalTotalCore1
    #[ast, interval, cfgExpr]
  try
    return .ok <| ← unsafe evalExpr IntervalRat (mkConst ``IntervalRat) enclosureExpr
  catch e =>
    return .error <| .internalFailure (← e.toMessageData.toString)

/-- Comparison-parameterized subdivision recursion. -/
private unsafe def proveWithSubdiv
    (comparison : SubdivisionComparison)
    (ast supportProof loRatExpr hiRatExpr leProof boundRat cfgExpr : Lean.Expr)
    (bound : ℚ) (configuredMaxDepth remainingDepth depthUsed : Nat) :
    TacticM (Except SubdivisionFailure SubdivisionProof) := do
  let intervalRat ← mkAppM ``IntervalRat.mk #[loRatExpr, hiRatExpr, leProof]
  let enclosure ←
    match ← evaluateSubdivisionNode ast intervalRat cfgExpr with
    | .ok enclosure => pure enclosure
    | .error failure => return .error failure

  if enclosureProves comparison enclosure bound then
    let checkerName := subdivisionChecker comparison
    let checkExpr ← mkAppM checkerName #[ast, intervalRat, boundRat, cfgExpr]
    let certTy ← mkAppM ``Eq #[checkExpr, mkConst ``Bool.true]
    let certGoal ← mkFreshExprMVar certTy
    let event ←
      match ← LeanCert.Tactic.closeCertificateGoalTyped
          (← LeanCert.Tactic.VerificationConfig.current) certGoal.mvarId!
          (tacticName := "interval_bound_subdiv") with
      | .accepted event => pure event
      | .rejected =>
          return .error <| .rejected checkerName
            "the fixed leaf checker evaluated to false"
      | .failed failure =>
          return .error <| .internalFailure
            (failure.message "interval_bound_subdiv")
    let proof ← mkAppM (subdivisionVerifier comparison)
      #[ast, supportProof, loRatExpr, hiRatExpr, leProof, boundRat, cfgExpr, certGoal]
    return .ok {
      proof
      enclosure
      execution := {
        verification := event.toUsage
        deepestDepthUsed := depthUsed
        boxesExamined := 1
        certifiedLeaves := 1
      }
    }

  if remainingDepth == 0 then
    return .error <| .exhausted configuredMaxDepth 1 depthUsed (some enclosure)

  let some lo ← getLiteral? loRatExpr
    | return .error <| .unsupported (toString loRatExpr)
        "could not extract a rational lower endpoint"
  let some hi ← getLiteral? hiRatExpr
    | return .error <| .unsupported (toString hiRatExpr)
        "could not extract a rational upper endpoint"

  let mid : ℚ := (lo + hi) / 2
  let midExpr := toExpr mid
  let loLeMidExpr ← mkDecideProof (← mkAppM ``LE.le #[loRatExpr, midExpr])
  let midLeHiExpr ← mkDecideProof (← mkAppM ``LE.le #[midExpr, hiRatExpr])

  let left ← proveWithSubdiv comparison ast supportProof loRatExpr midExpr
    loLeMidExpr boundRat cfgExpr bound configuredMaxDepth
    (remainingDepth - 1) (depthUsed + 1)
  let left ←
    match left with
    | .ok proof => pure proof
    | .error failure =>
        return .error <| failure.addExamined {
          deepestDepthUsed := depthUsed
          boxesExamined := 1
        }

  let right ← proveWithSubdiv comparison ast supportProof midExpr hiRatExpr
    midLeHiExpr boundRat cfgExpr bound configuredMaxDepth
    (remainingDepth - 1) (depthUsed + 1)
  let right ←
    match right with
    | .ok proof => pure proof
    | .error failure =>
        return .error <| failure.addExamined {
          verification := left.execution.verification
          deepestDepthUsed := max depthUsed left.execution.deepestDepthUsed
          boxesExamined := 1 + left.execution.boxesExamined
          certifiedLeaves := left.execution.certifiedLeaves
        }

  let proof ← mkAppM (subdivisionCombiner comparison)
    #[ast, loRatExpr, midExpr, hiRatExpr, boundRat,
      loLeMidExpr, midLeHiExpr, left.proof, right.proof]
  return .ok {
    proof
    enclosure := {
      lo := min left.enclosure.lo right.enclosure.lo
      hi := max left.enclosure.hi right.enclosure.hi
      le := le_trans (min_le_left _ _)
        (le_trans left.enclosure.le (le_max_left _ _))
    }
    execution := SubdivisionExecution.combineChildren depthUsed
      left.execution right.execution
  }

private def closeSubdivisionTransport (proof : Lean.Expr) (fromSetIcc : Bool) :
    TacticM (Except SubdivisionFailure Unit) := do
  let proofSyntax ← Term.exprToSyntax proof
  try
    if fromSetIcc then
      evalTactic (← `(tactic| convert ($proofSyntax) using 3))
    else
      evalTactic (← `(tactic|
        simpa [IntervalRat.mem_iff_mem_Icc] using $proofSyntax))

    let sideGoals ← getGoals
    for sideGoal in sideGoals do
      setGoals [sideGoal]
      let tryClose (tactic : TacticM Unit) : TacticM Bool := do
        let saved ← saveState
        try
          tactic
          if (← getGoals).isEmpty then return true
          saved.restore
          return false
        catch _ =>
          saved.restore
          return false
      if ← tryClose (evalTactic (← `(tactic| rfl))) then continue
      if ← tryClose (evalTactic (← `(tactic| norm_num))) then continue
      if ← tryClose (evalTactic (← `(tactic| norm_cast))) then continue
      if ← tryClose (evalTactic (← `(tactic|
          norm_num; simp only [Rat.divInt_eq_div]; push_cast; rfl))) then continue
      if ← tryClose (evalTactic (← `(tactic|
          simp only [Rat.divInt_eq_div]; push_cast; rfl))) then continue
      if ← tryClose (evalTactic (← `(tactic|
          simp only [Rat.divInt_eq_div]; push_cast; ring))) then continue
      if ← tryClose (evalTactic (← `(tactic| congr 1 <;> norm_num))) then continue
      if ← tryClose (evalTactic (← `(tactic|
          simp only [sq, pow_two, pow_succ, pow_zero, pow_one, one_mul,
            mul_one]))) then continue
      if ← tryClose (evalTactic (← `(tactic| field_simp; ring))) then continue
      return .error <| .transportFailure
        s!"could not close side goal {← sideGoal.getType}"
    unless (← getGoals).isEmpty do
      return .error <| .transportFailure
        "subdivision theorem transport left unresolved proof obligations"
    return .ok ()
  catch e =>
    return .error <| .transportFailure (← e.toMessageData.toString)

private def comparisonOfGoal : BoundGoal → SubdivisionComparison
  | .forallLe .. => .upper
  | .forallGe .. => .lower
  | .forallLt .. => .strictUpper
  | .forallGt .. => .strictLower

private def partsOfGoal :
    BoundGoal → IntervalInfo × Lean.Expr × Lean.Expr
  | .forallLe _ interval func bound => (interval, func, bound)
  | .forallGe _ interval func bound => (interval, func, bound)
  | .forallLt _ interval func bound => (interval, func, bound)
  | .forallGt _ interval func bound => (interval, func, bound)

private unsafe def intervalBoundSubdivCoreTypedImpl
    (depth : Option Nat) (maxSubdiv : Nat) :
    TacticM (Except SubdivisionFailure SubdivisionOutcome) := do
  try intervalNormCore
  catch e =>
    return .error <| .unsupported "goal normalization" (← e.toMessageData.toString)

  try
    evalTactic (← `(tactic|
      intro _x _hx; simp only [ge_iff_le, gt_iff_lt]; revert _x _hx))
  catch _ =>
    try evalTactic (← `(tactic| simp only [ge_iff_le, gt_iff_lt]))
    catch _ => pure ()
  try
    evalTactic (← `(tactic|
      simp only [sq, pow_two, pow_succ, pow_zero, pow_one, one_mul, mul_one] at *))
  catch _ => pure ()

  let goal ← getMainGoal
  let goalType ← goal.getType
  let some boundGoal ← parseBoundGoal goalType
    | return .error <| .unsupported (toString goalType)
        "expected a univariate interval bound"
  let comparison := comparisonOfGoal boundGoal
  let (intervalInfo, func, boundExpr) := partsOfGoal boundGoal

  let ast ←
    try pure (← getAstWithReport func).expr
    catch e =>
      return .error <| .unsupported (toString func) (← e.toMessageData.toString)
  let boundRat ←
    try extractRatBound boundExpr
    catch e =>
      return .error <| .unsupported (toString boundExpr) (← e.toMessageData.toString)
  let some bound ← getLiteral? boundRat
    | return .error <| .unsupported (toString boundExpr)
        "the requested bound is not rational"
  let supportProof ←
    try pure (← mkSupportedCoreProof ast)
    catch e =>
      return .error <| .unsupported (toString func) (← e.toMessageData.toString)
  let some bounds ← getSubdivBounds intervalInfo
    | return .error <| .unsupported (toString goalType)
        "only literal Set.Icc or IntervalRat intervals support subdivision"
  let (_lo, _hi, loRatExpr, hiRatExpr, leProof, fromSetIcc) := bounds
  let transportGoals ← getGoals
  let preparedState ← saveState
  let depths : List Nat := match depth with
    | some n => [n]
    | none => [10, 15, 20, 25]
  let mut lastFailure : Option SubdivisionFailure := none

  for taylorDepth in depths do
    preparedState.restore
    let cfgExpr ← mkAppM ``EvalConfig.mk #[toExpr taylorDepth]
    match ← proveWithSubdiv comparison ast supportProof loRatExpr hiRatExpr leProof
        boundRat cfgExpr bound maxSubdiv maxSubdiv 0 with
    | .ok proof =>
        setGoals transportGoals
        match ← closeSubdivisionTransport proof.proof fromSetIcc with
        | .ok _ =>
            return .ok {
              comparison
              taylorDepth
              maxDepth := maxSubdiv
              finalEnclosure := proof.enclosure
              execution := proof.execution
              checker := subdivisionChecker comparison
              verifier := subdivisionVerifier comparison
            }
        | .error failure => return .error failure
    | .error failure@(.exhausted ..) =>
        lastFailure := some failure
    | .error failure@(.rejected ..) =>
        lastFailure := some failure
    | .error failure =>
        return .error failure

  return .error <| lastFailure.getD <|
    .exhausted maxSubdiv 0 0 none

/-- Typed and exception-total subdivision entry point. Every non-success
restores the complete caller tactic state. -/
unsafe def intervalBoundSubdivCoreTyped
    (depth : Option Nat) (maxSubdiv : Nat) :
    TacticM (Except SubdivisionFailure SubdivisionOutcome) := do
  let original ← saveState
  try
    match ← intervalBoundSubdivCoreTypedImpl depth maxSubdiv with
    | .ok outcome => return .ok outcome
    | .error failure =>
        original.restore
        return .error failure
  catch e =>
    original.restore
    return .error <| .internalFailure (← e.toMessageData.toString)

/-- Reporting compatibility wrapper preserving the historical throwing API. -/
unsafe def intervalBoundSubdivWithDepthReported
    (depth : Option Nat) (maxSubdiv : Nat) : TacticM SubdivisionOutcome := do
  match ← intervalBoundSubdivCoreTyped depth maxSubdiv with
  | .ok outcome => return outcome
  | .error failure => throwSubdivisionFailure failure

/-- Compatibility core retaining the historical `TacticM Unit` shape. -/
unsafe def intervalBoundSubdivWithDepth (depth : Option Nat) (maxSubdiv : Nat) :
    TacticM Unit := do
  match ← intervalBoundSubdivCoreTyped depth maxSubdiv with
  | .ok _ => pure ()
  | .error failure => throwSubdivisionFailure failure

/-- The interval_bound_subdiv tactic. -/
syntax (name := intervalBoundSubdivTac) "interval_bound_subdiv" (num)? (num)?
  (leancertTrustItem)? : tactic

@[tactic intervalBoundSubdivTac]
unsafe def elabIntervalBoundSubdiv : Tactic := fun stx => do
  let depthSyntax := stx[1].getOptional?
  let subdivSyntax := stx[2].getOptional?
  let trustSyntax := stx[3].getOptional?.map (⟨·⟩)
  let trust? ← LeanCert.Tactic.elabTrustItem? trustSyntax
  LeanCert.Tactic.withTrustMode trust? do
    let maxSubdiv := match subdivSyntax with
      | some n => n.toNat
      | none => 3
    let depth := depthSyntax.map (·.toNat)
    intervalBoundSubdivWithDepth depth maxSubdiv

end LeanCert.Tactic.Auto
