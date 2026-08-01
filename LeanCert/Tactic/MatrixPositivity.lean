/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Engine.MatrixPositivity.Candidate
import LeanCert.Validity.MatrixPositivity
import LeanCert.Tactic.Verification

/-!
# Exact matrix positivity tactics

The initial front end accepts goals whose matrix is an explicit
`LeanCert.Engine.ratCastMatrix` of a closed rational square matrix. This keeps
discovery exact and makes unsupported symbolic matrices a typed, resumable
outcome for the portfolio router.
-/

open Lean Meta Elab Tactic

namespace LeanCert.Tactic

open LeanCert.Engine
open LeanCert.Validity

inductive MatrixPositivityCheckStage where
  | accepted
  | factorizationMismatch
  | negativeDiagonal
  | nonpositiveDiagonal
  deriving Repr, Inhabited, DecidableEq

structure MatrixPositivityInspection where
  dimension : Nat
  kind : MatrixPositivityKind
  certificateKind : String
  positivePivots : Nat
  zeroPivots : Nat
  negativePivots : Nat
  stage : MatrixPositivityCheckStage
  deriving Repr, Inhabited

inductive MatrixPositivityFailure where
  | unsupportedGoal (detail : String)
  | dimensionMismatch (expected actual : String)
  | generationFailed (report : AutomaticMatrixPositivityReport)
  | rejected (inspection : MatrixPositivityInspection)
  | verificationFailure (detail : String)
  | transportFailure (detail : String)
  | internalFailure (detail : String)
  deriving Repr, Inhabited

structure MatrixPositivityOutcome where
  inspection : MatrixPositivityInspection
  search : Option AutomaticMatrixPositivityReport := none
  checker : Name
  verifier : Name
  verification : VerificationEvent
  deriving Repr

private structure MatrixTarget where
  kind : MatrixPositivityKind
  dimension : Lean.Expr
  matrix : Lean.Expr

private def parseFinDimension? (type : Lean.Expr) : Option Lean.Expr := do
  guard (type.getAppFn.constName? == some ``Fin)
  type.getAppArgs.back?

private def parseMatrixTarget (target : Lean.Expr) :
    TacticM (Except MatrixPositivityFailure MatrixTarget) := do
  let kind ←
    if target.getAppFn.constName? == some ``Matrix.PosSemidef then
      pure MatrixPositivityKind.posSemidef
    else if target.getAppFn.constName? == some ``Matrix.PosDef then
      pure MatrixPositivityKind.posDef
    else
      return .error (.unsupportedGoal
        "expected `Matrix.PosSemidef` or `Matrix.PosDef`")
  let matrixTarget ←
    match target.getAppArgs.back? with
    | some matrix => pure matrix
    | none => return .error (.unsupportedGoal "matrix positivity target has no matrix argument")
  unless matrixTarget.getAppFn.constName? == some ``LeanCert.Engine.ratCastMatrix do
    return .error (.unsupportedGoal
      "automatic matrix positivity currently requires `ratCastMatrix` of an exact rational matrix")
  let args := matrixTarget.getAppArgs
  if args.size < 3 then
    return .error (.unsupportedGoal "malformed `ratCastMatrix` application")
  let rowType := args[args.size - 3]!
  let columnType := args[args.size - 2]!
  unless ← isDefEq rowType columnType do
    return .error (.unsupportedGoal "expected a square matrix")
  let dimension ←
    match parseFinDimension? rowType with
    | some dimension => pure dimension
    | none => return .error (.unsupportedGoal "expected matrix indices of the form `Fin n`")
  return .ok { kind, dimension, matrix := args[args.size - 1]! }

private def elaborateCertificate (certificateSyntax : TSyntax `term) (expectedType : Lean.Expr) :
    TacticM (Except (String × String) Lean.Expr) := do
  try
    let certificate ← Term.elabTerm certificateSyntax (some expectedType)
    let actualType ← instantiateMVars (← inferType certificate)
    unless ← isDefEq actualType expectedType do
      return .error (toString (← ppExpr expectedType), toString (← ppExpr actualType))
    return .ok certificate
  catch exception =>
    return .error (toString (← ppExpr expectedType), ← exception.toMessageData.toString)

private unsafe def evaluateReport (matrix config : Lean.Expr) :
    TacticM AutomaticMatrixPositivityReport := do
  let result ← mkAppM ``LeanCert.Engine.discoverMatrixPositivity #[matrix, config]
  let report ← mkAppM ``LeanCert.Engine.AutomaticMatrixPositivityResult.report #[result]
  evalExpr AutomaticMatrixPositivityReport
    (mkConst ``AutomaticMatrixPositivityReport) report

private def certificateFromReport (dimension : Lean.Expr)
    (report : AutomaticMatrixPositivityReport) : TacticM Lean.Expr := do
  mkAppM ``LeanCert.Engine.LDLTCertificate.ofLists
    #[dimension, toExpr report.lower, toExpr report.diagonal]

private def inspectPSD (dimension : Nat) (_matrix _certificate : Lean.Expr)
    (report : Option AutomaticMatrixPositivityReport) : TacticM MatrixPositivityInspection := do
  let positive := report.map (·.positivePivots) |>.getD 0
  let zeroCount := report.map (·.zeroPivots) |>.getD 0
  let negative := report.map (·.negativePivots) |>.getD 0
  pure {
    dimension
    kind := .posSemidef
    certificateKind := if report.isSome then "exact LDLT" else "explicit Gram/LDLT"
    positivePivots := positive
    zeroPivots := zeroCount
    negativePivots := negative
    stage := if negative > 0 then .negativeDiagonal
      else if report.isSome then .accepted else .factorizationMismatch
  }

private def inspectPosDef (dimension : Nat) (_matrix _certificate : Lean.Expr)
    (report : Option AutomaticMatrixPositivityReport) : TacticM MatrixPositivityInspection := do
  let positive := report.map (·.positivePivots) |>.getD 0
  let zeroCount := report.map (·.zeroPivots) |>.getD 0
  let negative := report.map (·.negativePivots) |>.getD 0
  pure {
    dimension
    kind := .posDef
    certificateKind := "exact LDLT"
    positivePivots := positive
    zeroPivots := zeroCount
    negativePivots := negative
    stage := if negative > 0 || zeroCount > 0 then .nonpositiveDiagonal
      else if report.isSome then .accepted else .factorizationMismatch
  }

private unsafe def verifyCandidate (saved : Lean.Elab.Tactic.SavedState) (goal : MVarId)
    (target : Lean.Expr) (spec : MatrixTarget) (certificate : Lean.Expr)
    (report : Option AutomaticMatrixPositivityReport) :
    TacticM (Except MatrixPositivityFailure MatrixPositivityOutcome) := do
  let dimensionNat ← evalExpr Nat (mkConst ``Nat) spec.dimension
  let checkerName := match spec.kind with
    | .posSemidef => ``LeanCert.Engine.matrixPSDCheck
    | .posDef => ``LeanCert.Engine.matrixPosDefCheck
  let verifierName := match spec.kind with
    | .posSemidef => ``LeanCert.Validity.verify_matrix_posSemidef
    | .posDef => ``LeanCert.Validity.verify_matrix_posDef
  let inspection ← match spec.kind with
    | .posSemidef => inspectPSD dimensionNat spec.matrix certificate report
    | .posDef => inspectPosDef dimensionNat spec.matrix certificate report
  let checker ← mkAppM checkerName #[spec.matrix, certificate]
  let certificateGoalType ← mkAppM ``Eq #[checker, mkConst ``Bool.true]
  let certificateProof ← mkFreshExprMVar certificateGoalType MetavarKind.syntheticOpaque
  match ← closeCertificateGoalTyped (← VerificationConfig.current)
      certificateProof.mvarId! (tacticName := "matrix positivity") with
  | .rejected =>
      saved.restore
      return .error (.rejected inspection)
  | .failed failure =>
      saved.restore
      return .error (.verificationFailure (failure.message "matrix positivity"))
  | .accepted event =>
      let inspection := { inspection with stage := .accepted }
      let proof ← mkAppM verifierName #[spec.matrix, certificate, certificateProof]
      let proof ← instantiateMVars proof
      if proof.hasMVar then
        saved.restore
        return .error (.transportFailure "the final proof contains unresolved metavariables")
      let proofType ← inferType proof
      unless ← isDefEq proofType target do
        let detail := s!"constructed proof of {← ppExpr proofType}, expected {← ppExpr target}"
        saved.restore
        return .error (.transportFailure detail)
      goal.assign proof
      pruneSolvedGoals
      return .ok {
        inspection
        search := report
        checker := checkerName
        verifier := verifierName
        verification := event
      }

/-- Typed manual matrix positivity core. -/
unsafe def matrixPositivityCoreTyped (kind : MatrixPositivityKind)
    (certificateSyntax : TSyntax `term) :
    TacticM (Except MatrixPositivityFailure MatrixPositivityOutcome) := do
  let saved ← saveState
  try
    let goal ← getMainGoal
    let target ← withMainContext do zetaReduce (← instantiateMVars (← goal.getType))
    let spec ← match ← parseMatrixTarget target with
      | .ok spec => pure spec
      | .error failure => saved.restore; return .error failure
    unless spec.kind == kind do
      saved.restore
      return .error (.unsupportedGoal "the tactic does not match the requested matrix property")
    let expectedType ← match kind with
      | .posSemidef => mkAppM ``LeanCert.Engine.PSDCertificate #[spec.dimension]
      | .posDef => mkAppM ``LeanCert.Engine.LDLTCertificate #[spec.dimension]
    let certificate ← match ← withMainContext do elaborateCertificate certificateSyntax expectedType with
      | .ok certificate => pure (← withMainContext do zetaReduce (← instantiateMVars certificate))
      | .error (expected, actual) =>
          saved.restore
          return .error (.dimensionMismatch expected actual)
    verifyCandidate saved goal target spec certificate none
  catch exception =>
    saved.restore
    return .error (.internalFailure (← exception.toMessageData.toString))

/-- Typed automatic exact rational matrix positivity core. -/
unsafe def matrixPositivityAutoCoreTyped (kind : MatrixPositivityKind)
    (maxDimension : Nat := 8) :
    TacticM (Except MatrixPositivityFailure MatrixPositivityOutcome) := do
  let saved ← saveState
  try
    let goal ← getMainGoal
    let target ← withMainContext do zetaReduce (← instantiateMVars (← goal.getType))
    let spec ← match ← parseMatrixTarget target with
      | .ok spec => pure spec
      | .error failure => saved.restore; return .error failure
    unless spec.kind == kind do
      saved.restore
      return .error (.unsupportedGoal "the tactic does not match the requested matrix property")
    let config ← mkAppM ``AutomaticMatrixPositivityConfig.mk #[toExpr maxDimension]
    let report ← evaluateReport spec.matrix config
    if let some _ := report.failure then
      saved.restore
      return .error (.generationFailed report)
    let rawCertificate ← certificateFromReport spec.dimension report
    let certificate ← match kind with
      | .posSemidef => mkAppM ``LeanCert.Engine.PSDCertificate.ldlt #[rawCertificate]
      | .posDef => pure rawCertificate
    verifyCandidate saved goal target spec certificate (some report)
  catch exception =>
    saved.restore
    return .error (.internalFailure (← exception.toMessageData.toString))

private def failureMessage : MatrixPositivityFailure → String
  | .unsupportedGoal detail => detail
  | .dimensionMismatch expected actual => s!"expected certificate type {expected}; got {actual}"
  | .generationFailed report => s!"exact LDLT discovery failed: {repr report.failure}"
  | .rejected inspection => s!"matrix certificate rejected at {repr inspection.stage}"
  | .verificationFailure detail => detail
  | .transportFailure detail => detail
  | .internalFailure detail => s!"internal matrix positivity failure: {detail}"

declare_syntax_cat matrixPositivityConfigItem
syntax "(" &"maxDimension" " := " num ")" : matrixPositivityConfigItem
syntax "(" &"trust" " := " leancertTrustMode ")" : matrixPositivityConfigItem

syntax (name := matrixPsdManual) "matrix_psd" " using " term:max
  matrixPositivityConfigItem* : tactic
syntax (name := matrixPsdAuto) "matrix_psd" matrixPositivityConfigItem* : tactic
syntax (name := matrixPosDefManual) "matrix_posdef" " using " term:max
  matrixPositivityConfigItem* : tactic
syntax (name := matrixPosDefAuto) "matrix_posdef" matrixPositivityConfigItem* : tactic
syntax (name := matrixPsdQuery) "matrix_psd?" matrixPositivityConfigItem* : tactic
syntax (name := matrixPosDefQuery) "matrix_posdef?" matrixPositivityConfigItem* : tactic

private structure MatrixPositivityConfig where
  maxDimension : Nat := 8
  trust : Option VerificationMode := none

private def parseMatrixPositivityConfig (items : Array Syntax) :
    TacticM MatrixPositivityConfig := do
  let mut config : MatrixPositivityConfig := {}
  for item in items do
    match item with
    | `(matrixPositivityConfigItem| (maxDimension := $n:num)) =>
        config := { config with maxDimension := n.getNat }
    | `(matrixPositivityConfigItem| (trust := $mode:leancertTrustMode)) =>
        let raw := mode.raw.reprint.getD ""
        let some parsed := VerificationMode.ofString? raw
          | throwErrorAt mode "invalid trust mode '{raw}'; expected kernel, native, or auto"
        config := { config with trust := some parsed }
    | _ => throwUnsupportedSyntax
  return config

@[tactic matrixPsdAuto]
unsafe def elabMatrixPsdAuto : Tactic := fun stx => do
  match stx with
  | `(tactic| matrix_psd $items:matrixPositivityConfigItem*) =>
      let config ← parseMatrixPositivityConfig items
      withTrustMode config.trust do
        match ← matrixPositivityAutoCoreTyped .posSemidef config.maxDimension with
        | .ok _ => pure ()
        | .error failure => throwError "matrix_psd: {failureMessage failure}"
  | _ => throwUnsupportedSyntax

@[tactic matrixPsdManual]
unsafe def elabMatrixPsdManual : Tactic := fun stx => do
  match stx with
  | `(tactic| matrix_psd using $certificate:term $items:matrixPositivityConfigItem*) =>
      let config ← parseMatrixPositivityConfig items
      withTrustMode config.trust do
        match ← matrixPositivityCoreTyped .posSemidef certificate with
        | .ok _ => pure ()
        | .error failure => throwError "matrix_psd: {failureMessage failure}"
  | _ => throwUnsupportedSyntax

@[tactic matrixPosDefAuto]
unsafe def elabMatrixPosDefAuto : Tactic := fun stx => do
  match stx with
  | `(tactic| matrix_posdef $items:matrixPositivityConfigItem*) =>
      let config ← parseMatrixPositivityConfig items
      withTrustMode config.trust do
        match ← matrixPositivityAutoCoreTyped .posDef config.maxDimension with
        | .ok _ => pure ()
        | .error failure => throwError "matrix_posdef: {failureMessage failure}"
  | _ => throwUnsupportedSyntax

@[tactic matrixPosDefManual]
unsafe def elabMatrixPosDefManual : Tactic := fun stx => do
  match stx with
  | `(tactic| matrix_posdef using $certificate:term $items:matrixPositivityConfigItem*) =>
      let config ← parseMatrixPositivityConfig items
      withTrustMode config.trust do
        match ← matrixPositivityCoreTyped .posDef certificate with
        | .ok _ => pure ()
        | .error failure => throwError "matrix_posdef: {failureMessage failure}"
  | _ => throwUnsupportedSyntax

@[tactic matrixPsdQuery]
unsafe def elabMatrixPsdQuery : Tactic := fun stx => do
  match stx with
  | `(tactic| matrix_psd? $items:matrixPositivityConfigItem*) =>
      let config ← parseMatrixPositivityConfig items
      withTrustMode config.trust do
        match ← matrixPositivityAutoCoreTyped .posSemidef config.maxDimension with
        | .ok outcome => logInfo m!"matrix_psd succeeded: {repr outcome.inspection}"
        | .error failure => throwError "matrix_psd?: {failureMessage failure}"
  | _ => throwUnsupportedSyntax

@[tactic matrixPosDefQuery]
unsafe def elabMatrixPosDefQuery : Tactic := fun stx => do
  match stx with
  | `(tactic| matrix_posdef? $items:matrixPositivityConfigItem*) =>
      let config ← parseMatrixPositivityConfig items
      withTrustMode config.trust do
        match ← matrixPositivityAutoCoreTyped .posDef config.maxDimension with
        | .ok outcome => logInfo m!"matrix_posdef succeeded: {repr outcome.inspection}"
        | .error failure => throwError "matrix_posdef?: {failureMessage failure}"
  | _ => throwUnsupportedSyntax

end LeanCert.Tactic
