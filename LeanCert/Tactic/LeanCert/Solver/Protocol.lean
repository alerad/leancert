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

structure SolverReport where
  intent : GoalIntent
  solver : Name
  method : String
  cost : Nat
  backend : Option String := none
  checker : Option Name := none
  verifier : Option Name := none
  enclosure : Option LeanCert.Core.IntervalRat := none
  deriving Inhabited

structure ProofArtifact where
  proof : Lean.Expr
  proposition : Lean.Expr
  report : SolverReport
  deriving Inhabited

inductive AttemptOutcome where
  | proved (artifact : ProofArtifact)
  | notApplicable
  | unsupported (evidence : UnsupportedEvidence)
  | domainObstruction (evidence : DomainObstruction)
  | inconclusive (evidence : NumericalEvidence)
  | rejected (evidence : CandidateEvidence)
  | refuted (evidence : RefutationEvidence)
  | internalError (solver : Name) (detail : String)
  deriving Inhabited

/-- A capability-driven semantic solver. -/
structure SemanticSolver where
  report : SolverReport
  supports : SemanticGoal → Bool
  attempt : Semantic.PreparedGoal → LeanCertConfig →
    Elab.Tactic.TacticM AttemptOutcome

private def backendInconclusiveDetail (report : SolverReport) : String :=
  if report.method == "integral_exact" then
    "Exact integration did not recognize the integrand as a rational polynomial \
      with supported constant divisions."
  else if report.method.startsWith "integral_search" then
    "Checked partition enclosures did not establish the requested integral comparison."
  else if report.method.startsWith "interval_bound_subdiv" then
    "Subdivision reached its configured depth without obtaining a decisive enclosure."
  else if report.method.startsWith "opt_bound" ||
      report.method.startsWith "multivariate_bound" then
    "Global optimization did not produce a verifier-ready bound within its iteration limit."
  else
    "The backend could not construct a complete certificate with the current settings."

/-- Validate a proof before it can be committed to the user's goal. -/
def validateProofArtifact (artifact : ProofArtifact) : MetaM (Except String Unit) := do
  let proposition ← instantiateMVars artifact.proposition
  if proposition.hasMVar then
    return .error "proof artifact proposition contains unresolved metavariables"
  if proposition.hasLooseBVars then
    return .error "proof artifact proposition contains loose bound variables"
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

/-- Run an existing proof procedure on an isolated metavariable and turn a
complete proof into a validated artifact.  The caller's goals are restored on
every non-success path; solver exceptions are implementation details attached
to an inconclusive typed outcome, never parsed by their message text. -/
def proveWithTactic (report : SolverReport) (proposition : Lean.Expr)
    (solver : Elab.Tactic.TacticM Unit) :
    Elab.Tactic.TacticM AttemptOutcome := do
  let originalGoals ← Elab.Tactic.getGoals
  let saved ← Elab.Tactic.saveState
  let proof ← mkFreshExprMVar proposition MetavarKind.syntheticOpaque
  Elab.Tactic.setGoals [proof.mvarId!]
  try
    let captured ← Mathlib.Tactic.withResetServerInfo solver
    if captured.msgs.hasErrors then
      let rendered ← captured.msgs.toList.mapM fun message => message.data.toString
      trace[LeanCert.solver] "{report.method} checker output:\n\
        {String.intercalate "\n" rendered}"
      saved.restore
      return .rejected {
        checker := report.checker
        detail := "The generated certificate was not accepted at the current \
          precision or strategy settings."
      }
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
      return .internalError report.solver
        "solver proof contains unresolved metavariables"
    let artifact : ProofArtifact := { proof, proposition, report }
    match ← validateProofArtifact artifact with
    | .ok _ =>
        -- Keep environment extensions produced by successful tactics such as
        -- `native_decide`, but return control with exactly the caller's goals.
        Elab.Tactic.setGoals originalGoals
        return .proved artifact
    | .error detail =>
      saved.restore
      return .internalError report.solver detail
  catch exception =>
    let detail ← exception.toMessageData.toString
    trace[LeanCert.solver] "{report.method} raised during speculative execution:\n{detail}"
    saved.restore
    return .inconclusive {
      detail := backendInconclusiveDetail report
    }

end LeanCert.Tactic.Solver
