/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import Mathlib.Tactic.Basic
import LeanCert.Tactic.LeanCert.Config
import LeanCert.Tactic.LeanCert.Diagnostic.Evidence
import LeanCert.Tactic.LeanCert.Semantic.Prepare

/-!
# Semantic Solver Protocol

New semantic solvers return proof artifacts and typed expected outcomes.  They
do not mutate the user's original tactic goal.
-/

open Lean Meta

namespace LeanCert.Tactic.Solver

open LeanCert.Tactic.Diagnostic
open LeanCert.Tactic.Semantic

initialize registerTraceClass `LeanCert.solver

/-- Arithmetic implementation named in a user-facing report.  This type is
report-local on purpose: the semantic solver protocol must not depend on an
engine dispatcher merely to describe what happened. -/
inductive NumericalBackend where
  | rationalInterval
  | dyadicInterval
  | affineArithmetic
  | exactRational
  | checkedRationalPartitions
  deriving DecidableEq, Repr, Inhabited

/-- Static arithmetic policy selected before execution. It is deliberately
unable to claim which backend actually ran. -/
inductive BackendPolicy where
  | fixed (backend : NumericalBackend)
  | policy (description : String)
  | notApplicable
  | unknown
  deriving Repr, Inhabited

/-- A structured tactic invocation. Formatting belongs to the diagnostic
renderer, not to portfolio construction. -/
structure ProofSuggestion where
  tactic : String
  positionalArgs : Array String := #[]
  namedArgs : Array (String × String) := #[]
  trust : Option VerificationMode := none
  /-- Some legacy dedicated tactics honor the scoped trust option but do not
  yet accept inline `(trust := ...)` syntax. -/
  acceptsInlineTrust : Bool := true
  deriving Inhabited, Repr

/-- Aggregate of certificate closures retained by the final proof. Multiple
checks matter for subdivision, extrema, and conjunctions. -/
structure VerificationUsage where
  kernelChecks : Nat := 0
  nativeChecks : Nat := 0
  autoGateReasons : Array String := #[]
  kernelFallbacks : Nat := 0
  deriving Inhabited, Repr

def VerificationUsage.combine (left right : VerificationUsage) :
    VerificationUsage := {
  kernelChecks := left.kernelChecks + right.kernelChecks
  nativeChecks := left.nativeChecks + right.nativeChecks
  autoGateReasons := left.autoGateReasons ++ right.autoGateReasons
  kernelFallbacks := left.kernelFallbacks + right.kernelFallbacks
}

/-- Convert the verification subsystem's event log into the compact aggregate
used by reports. This is intentionally a one-way presentation boundary; proof
construction retains the richer event data in the dedicated tactic outcome. -/
def VerificationUsage.ofEvents
    (usage : LeanCert.Tactic.VerificationUsage) : VerificationUsage := {
  kernelChecks := usage.kernelChecks
  nativeChecks := usage.nativeChecks
  autoGateReasons := usage.autoGateReasons
  kernelFallbacks := usage.events.foldl (fun count event =>
    if event.cause == .autoNativeFallback then count + 1 else count) 0
}

/-- Compact, nonrecursive child data used by conjunction reports. -/
structure ChildReport where
  intent : GoalIntent
  strategy : String
  backend : Option NumericalBackend := none
  backendPolicy : BackendPolicy := .unknown
  verificationUsage : VerificationUsage := {}
  deriving Inhabited

/-- Why an optimization search stopped. Certification may still validate a
sound theorem after a search that stopped before reaching its target gap. -/
inductive OptimizationTermination where
  | toleranceReached
  | iterationLimit
  | queueExhausted
  | stopped
  deriving DecidableEq, Repr, Inhabited

/-- Structured facts from an optimization or optimization-guided discovery
run. Fields unavailable from Boolean-only certificate APIs remain `none`
rather than being reconstructed by rerunning the optimizer. -/
structure OptimizationStatistics where
  iterations : Option Nat := none
  configuredLimit : Nat
  tolerance : ℚ
  gap : Option ℚ := none
  converged : Option Bool := none
  remainingBoxes : Option Nat := none
  termination : Option OptimizationTermination := none
  deriving Inhabited, Repr

/-- Stable algorithm identity for reporting and failure classification.
User-facing `strategy` text may be polished without changing control flow. -/
inductive StrategyId where
  | legacy
  | exactNormalization
  | exactIntegral
  | partitionIntegral
  | subdivision
  | globalOptimization
  deriving DecidableEq, Repr, Inhabited

/-- Static solver intent.  It may state a backend policy, but cannot claim a
runtime winner. -/
structure SolverPlan where
  intent : GoalIntent
  solver : Name
  strategyId : StrategyId := .legacy
  strategy : String
  strategyDetail : Option String := none
  cost : Nat
  primaryProof : ProofSuggestion := { tactic := "leancert" }
  dedicatedProof : Option ProofSuggestion := none
  backendPolicy : BackendPolicy := .unknown
  verificationRequested : VerificationMode := .native
  checker : Option Name := none
  verifier : Option Name := none
  deriving Inhabited

/-- Runtime facts returned only by the successful isolated execution. Empty
execution data is the honest compatibility result for a legacy `TacticM Unit`
solver.

Reporting invariants:

1. `strategy` is algorithmic, never arithmetic or trust.
2. Static backend policy and observed execution use different types.
3. `verificationRequested` and retained `verificationUsage` are distinct.
4. `checker` is executable evidence; `verifier` is its Golden Theorem.
5. Enclosures are retained values, never recomputed for display.
6. Reporting metadata never participates in proof validation. -/
structure SolverExecution where
  backend : Option NumericalBackend := none
  verificationUsage : VerificationUsage := {}
  checker : Option Name := none
  verifier : Option Name := none
  enclosure : Option LeanCert.Core.IntervalRat := none
  optimization : Option OptimizationStatistics := none
  notes : Array String := #[]
  children : Array ChildReport := #[]
  deriving Inhabited

structure SolverReport where
  plan : SolverPlan
  execution : SolverExecution := {}
  deriving Inhabited

structure ProofArtifact where
  proof : Lean.Expr
  proposition : Lean.Expr
  report : SolverReport
  deriving Inhabited

/-- A typed non-success returned by a reporting-aware solver core. Keeping
proof success out of this type ensures that every proof still passes through
artifact validation before it can become an `AttemptOutcome.proved`. -/
inductive AttemptFailure where
  | notApplicable
  | unsupported (evidence : UnsupportedEvidence)
  | domainObstruction (evidence : DomainObstruction)
  | inconclusive (evidence : NumericalEvidence)
  | rejected (evidence : CandidateEvidence)
  | refuted (evidence : RefutationEvidence)
  | routerFailure (failure : RouterFailure)
  | internalError (solver : Name) (detail : String)
  deriving Inhabited

inductive AttemptOutcome where
  | proved (artifact : ProofArtifact)
  | notApplicable
  | unsupported (evidence : UnsupportedEvidence)
  | domainObstruction (evidence : DomainObstruction)
  | inconclusive (evidence : NumericalEvidence)
  | rejected (evidence : CandidateEvidence)
  | refuted (evidence : RefutationEvidence)
  | routerFailure (failure : RouterFailure)
  | internalError (solver : Name) (detail : String)
  deriving Inhabited

/-- Embed a core-level non-success into the portfolio outcome taxonomy. -/
def AttemptFailure.toOutcome : AttemptFailure → AttemptOutcome
  | .notApplicable => .notApplicable
  | .unsupported evidence => .unsupported evidence
  | .domainObstruction evidence => .domainObstruction evidence
  | .inconclusive evidence => .inconclusive evidence
  | .rejected evidence => .rejected evidence
  | .refuted evidence => .refuted evidence
  | .routerFailure failure => .routerFailure failure
  | .internalError solver detail => .internalError solver detail

/-- Portfolio control is centralized so individual loops cannot accidentally
assign different meanings to the same typed outcome. -/
inductive AttemptDisposition where
  | continue
  | stop
  | commit
  deriving DecidableEq, Repr, Inhabited

def AttemptOutcome.disposition : AttemptOutcome → AttemptDisposition
  | .proved _ => .commit
  | .notApplicable | .unsupported _ | .inconclusive _ | .rejected _ => .continue
  | .domainObstruction _ | .refuted _ | .routerFailure _ | .internalError .. => .stop

/-- A capability-driven semantic solver. -/
structure SemanticSolver where
  plan : SolverPlan
  supports : SemanticGoal → Bool
  attempt : Semantic.PreparedGoal → LeanCertConfig →
    Elab.Tactic.TacticM AttemptOutcome

private def backendInconclusiveDetail (plan : SolverPlan) : String :=
  match plan.strategyId with
  | .exactNormalization =>
      "Exact normalization did not close the prepared proposition."
  | .exactIntegral =>
      "Exact integration did not recognize the integrand as a rational polynomial \
        with supported constant divisions."
  | .partitionIntegral =>
      "Checked partition enclosures did not establish the requested integral comparison."
  | .subdivision =>
      "Subdivision reached its configured depth without obtaining a decisive enclosure."
  | .globalOptimization =>
      "Global optimization did not produce a verifier-ready bound within its iteration limit."
  | .legacy =>
      "The backend could not construct a complete certificate with the current settings."

/-- Compatibility policy for exception-based legacy tactic cores. New reported
cores must use `.internalError`; only the opaque `TacticM Unit` adapter may
translate an exception into the historical inconclusive result. -/
inductive ExceptionPolicy where
  | internalError
  | legacyInconclusive

/-- Validate a proof against the immutable proposition prepared for the
attempt, rather than trusting a proposition returned by solver code. -/
def validateProofArtifact (preparedProposition : Lean.Expr)
    (artifact : ProofArtifact) : MetaM (Except String Unit) := do
  let preparedProposition ← instantiateMVars preparedProposition
  if preparedProposition.hasMVar then
    return .error "prepared proposition contains unresolved metavariables"
  if preparedProposition.hasLooseBVars then
    return .error "prepared proposition contains loose bound variables"
  let proposition ← instantiateMVars artifact.proposition
  if proposition.hasMVar then
    return .error "proof artifact proposition contains unresolved metavariables"
  if proposition.hasLooseBVars then
    return .error "proof artifact proposition contains loose bound variables"
  unless ← isDefEq proposition preparedProposition do
    return .error s!"proof artifact proposition {← ppExpr proposition} does not match \
      prepared proposition {← ppExpr preparedProposition}"
  let proof ← instantiateMVars artifact.proof
  if proof.hasMVar then
    return .error "proof artifact contains unresolved metavariables"
  if proof.hasLooseBVars then
    return .error "proof artifact contains loose bound variables"
  let actualType ← inferType proof
  unless ← isDefEq actualType proposition do
    return .error s!"proof artifact has type {← ppExpr actualType}, expected \
      {← ppExpr proposition}"
  return .ok ()

/-- Run a report-producing proof procedure on an isolated metavariable and turn
a complete proof into a validated artifact. The execution metadata is retained
only if the proof and all transport goals succeed. -/
def proveWithTacticReportedResult (plan : SolverPlan) (proposition : Lean.Expr)
    (solver : Elab.Tactic.TacticM (Except AttemptFailure SolverExecution))
    (exceptionPolicy : ExceptionPolicy := .internalError) :
    Elab.Tactic.TacticM AttemptOutcome := do
  let originalGoals ← Elab.Tactic.getGoals
  let saved ← Elab.Tactic.saveState
  let proof ← mkFreshExprMVar proposition MetavarKind.syntheticOpaque
  Elab.Tactic.setGoals [proof.mvarId!]
  try
    let captured ← Mathlib.Tactic.withResetServerInfo solver
    if captured.msgs.hasErrors then
      let rendered ← captured.msgs.toList.mapM fun message => message.data.toString
      let detail := String.intercalate "\n" rendered
      trace[LeanCert.solver] "{plan.strategy} checker output:\n\
        {detail}"
      saved.restore
      match exceptionPolicy with
      | .internalError =>
          return .internalError plan.solver
            s!"solver logged error diagnostics without returning a typed failure:\n{detail}"
      | .legacyInconclusive =>
          return .rejected {
            checker := plan.checker
            detail := "The generated certificate was not accepted at the current \
              precision or strategy settings."
          }
    let some result := captured.result?
      | saved.restore
        return .internalError plan.solver
          "solver returned without execution metadata"
    let execution ←
      match result with
      | .ok execution => pure execution
      | .error failure =>
        saved.restore
        return failure.toOutcome
    let remaining ← Elab.Tactic.getGoals
    unless remaining.isEmpty do
      let rendered ← remaining.mapM fun goal => goal.withContext do
        return toString (← ppExpr (← goal.getType))
      saved.restore
      return .inconclusive {
        detail := s!"solver left {remaining.length} proof obligation(s):\n\
          {String.intercalate "\n" rendered}"
      }
    let proof ← instantiateMVars proof
    if proof.hasMVar then
      saved.restore
      return .internalError plan.solver
        "solver proof contains unresolved metavariables"
    let report : SolverReport := { plan, execution }
    let artifact : ProofArtifact := { proof, proposition, report }
    match ← validateProofArtifact proposition artifact with
    | .ok _ =>
        -- Keep environment extensions produced by successful tactics such as
        -- `native_decide`, but return control with exactly the caller's goals.
        Elab.Tactic.setGoals originalGoals
        return .proved artifact
    | .error detail =>
      saved.restore
      return .internalError plan.solver detail
  catch exception =>
    let detail ← exception.toMessageData.toString
    trace[LeanCert.solver] "{plan.strategy} raised during speculative execution:\n{detail}"
    saved.restore
    match exceptionPolicy with
    | .internalError => return .internalError plan.solver detail
    | .legacyInconclusive =>
        return .inconclusive { detail := backendInconclusiveDetail plan }

/-- Convenience wrapper for the common case where a reported solver can only
fail through the ordinary tactic protocol. -/
def proveWithTacticReported (plan : SolverPlan) (proposition : Lean.Expr)
    (solver : Elab.Tactic.TacticM SolverExecution) :
    Elab.Tactic.TacticM AttemptOutcome :=
  proveWithTacticReportedResult plan proposition do
    return .ok (← solver)

/-- Compatibility adapter for legacy tactic cores that do not yet expose
runtime metadata. Their static plan may describe a backend policy, but the
execution remains explicitly unknown. -/
def proveWithTactic (plan : SolverPlan) (proposition : Lean.Expr)
    (solver : Elab.Tactic.TacticM Unit) :
    Elab.Tactic.TacticM AttemptOutcome :=
  proveWithTacticReportedResult plan proposition (do
    solver
    return .ok {}) .legacyInconclusive

end LeanCert.Tactic.Solver
