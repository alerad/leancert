/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Tactic.LeanCert.Semantic.Parse
import LeanCert.Tactic.Verification
import LeanCert.Engine.RootFinding.KrawczykCandidate
import LeanCert.Validity.Krawczyk

/-!
# Manual and automatic Krawczyk certificate tactics

`system_unique_root using cert` is the I1 manual front end for the checked
Krawczyk engine. `system_unique_root` is the I2 automatic front end: it runs an
untrusted midpoint-Jacobian/interval-Newton search and submits the selected
candidate to the identical `krawczykCheck` and `verify_unique_system_root`
boundary.
-/

open Lean Meta Elab Tactic

namespace LeanCert.Tactic

open LeanCert.Core
open LeanCert.Engine
open LeanCert.Validity
open LeanCert.Tactic.Semantic

/-- The first failed component of the monolithic Krawczyk checker. This is
diagnostic data only; proof construction always closes `krawczykCheck = true`.
-/
inductive KrawczykCheckStage where
  | accepted
  | unsupportedAD
  | centerOutside
  | singularPreconditioner
  | contractionNotStrict
  | imageNotStrictlyInside
  deriving Repr, Inhabited, DecidableEq

/-- Retained computational facts from one inspection of the supplied
certificate. They are used for diagnostics and `system_unique_root?` output,
never as a substitute for the Boolean checker proof. -/
structure KrawczykInspection where
  dimension : Nat
  center : List ℚ
  contractionBound : ℚ
  stage : KrawczykCheckStage
  deriving Repr, Inhabited

def inspectKrawczyk {n : Nat} (F : Fin n → LeanCert.Core.Expr)
    (X : Fin n → IntervalRat)
    (cert : KrawczykCert n) (cfg : EvalConfig := {}) : KrawczykInspection :=
  let contraction := intervalMatrixBound
    (preconditionedJacobian cert.preconditioner (intervalJacobian F X cfg))
  let stage :=
    if !(decide (∀ i, (F i).checkADSupported = true)) then
      KrawczykCheckStage.unsupportedAD
    else if !(decide (centerInside X cert.center)) then
      .centerOutside
    else if !(decide (cert.preconditioner.det ≠ 0)) then
      .singularPreconditioner
    else if !(decide (contraction < 1)) then
      .contractionNotStrict
    else if !(decide (∀ i, intervalStrictInside
        (newtonImageEnclosure F X cert.center cert.preconditioner cfg i) (X i) = true)) then
      .imageNotStrictlyInside
    else
      .accepted
  {
    dimension := n
    center := List.ofFn cert.center
    contractionBound := contraction
    stage
  }

/-- Typed failures returned by the dedicated I1 core. -/
inductive SystemUniqueRootFailure where
  | unsupportedGoal (detail : String)
  | dimensionMismatch (expected actual : String)
  | generationFailed (report : AutomaticKrawczykReport)
  | rejected (inspection : KrawczykInspection)
  | verificationFailure (detail : String)
  | transportFailure (detail : String)
  | internalFailure (detail : String)
  deriving Inhabited, Repr

/-- Runtime facts retained by a successful manual Krawczyk proof. -/
structure SystemUniqueRootOutcome where
  inspection : KrawczykInspection
  search : Option AutomaticKrawczykReport := none
  checker : Name := ``LeanCert.Engine.krawczykCheck
  verifier : Name := ``LeanCert.Validity.verify_unique_system_root
  verification : VerificationEvent
  deriving Repr

private theorem swapSystemRootConjunction {n : Nat} (F : Fin n → LeanCert.Core.Expr)
    (X : Fin n → IntervalRat)
    (h : ∃! x, FinBoxMem x X ∧ SystemZero F x) :
    ∃! x, SystemZero F x ∧ FinBoxMem x X := by
  rcases h with ⟨x, hx, hunique⟩
  refine ⟨x, hx.symm, ?_⟩
  intro y hy
  exact hunique y hy.symm

private def elaborateCertificate (stx : TSyntax `term) (dimension : Lean.Expr) :
    TacticM (Except (String × String) Lean.Expr) := do
  let expectedType := mkApp (mkConst ``LeanCert.Engine.KrawczykCert) dimension
  let inferred ←
    try
      pure (some (← Term.elabTerm stx none))
    catch _ =>
      pure none
  match inferred with
  | some certificate =>
      let actualType ← instantiateMVars (← inferType certificate)
      unless ← isDefEq actualType expectedType do
        return .error (toString (← ppExpr expectedType), toString (← ppExpr actualType))
      return .ok certificate
  | none =>
      try
        return .ok (← Term.elabTerm stx (some expectedType))
      catch exception =>
        return .error (toString (← ppExpr expectedType),
          ← exception.toMessageData.toString)

private unsafe def evaluateInspection (spec : SystemRootSpec)
    (certificate cfg : Lean.Expr) :
    TacticM KrawczykInspection := do
  let expression ← mkAppM ``inspectKrawczyk #[spec.system, spec.box, certificate, cfg]
  trace[LeanCert.solver] "Krawczyk inspection expression: {← ppExpr expression}"
  evalExpr KrawczykInspection (mkConst ``KrawczykInspection) expression

private def parseSystemRootTarget (target : Lean.Expr) :
    TacticM (Except SystemUniqueRootFailure SystemRootSpec) := do
  match ← withMainContext do Semantic.parseGoal target with
  | .ok (.systemRoot spec) => return .ok spec
  | .ok _ => return .error (.unsupportedGoal
      "expected `∃! x : Fin n → ℝ, FinBoxMem x X ∧ SystemZero F x`")
  | .error failure => return .error (.unsupportedGoal failure.detail)

private unsafe def verifySystemUniqueRootCandidate
    (saved : Lean.Elab.Tactic.SavedState) (goal : MVarId) (target : Lean.Expr)
    (spec : SystemRootSpec) (certificate cfg : Lean.Expr)
    (search : Option AutomaticKrawczykReport := none) :
    TacticM (Except SystemUniqueRootFailure SystemUniqueRootOutcome) := do
  let inspection ← evaluateInspection spec certificate cfg
  let checker ← mkAppM ``LeanCert.Engine.krawczykCheck
    #[spec.system, spec.box, certificate, cfg]
  let certificateGoalType ← mkAppM ``Eq #[checker, mkConst ``Bool.true]
  let certificateProof ← mkFreshExprMVar certificateGoalType MetavarKind.syntheticOpaque
  let verificationConfig ← VerificationConfig.current
  match ← closeCertificateGoalTyped verificationConfig certificateProof.mvarId!
      (tacticName := "system_unique_root") with
  | .rejected =>
      saved.restore
      return .error (.rejected inspection)
  | .failed failure =>
      saved.restore
      return .error (.verificationFailure
        (failure.message "system_unique_root"))
  | .accepted event =>
      let golden ← mkAppM ``LeanCert.Validity.verify_unique_system_root
        #[spec.system, spec.box, certificate, cfg, certificateProof]
      let proof ←
        if spec.reversedConjunction then
          mkAppM ``swapSystemRootConjunction #[spec.system, spec.box, golden]
        else
          pure golden
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
      return .ok { inspection, search, verification := event }

/-- Reporting-aware manual-certificate core. Failure restores the caller's
complete tactic state; success assigns only a proof of the original goal. -/
unsafe def systemUniqueRootCoreTyped (certificateSyntax : TSyntax `term)
    (taylorDepth : Nat := 10) :
    TacticM (Except SystemUniqueRootFailure SystemUniqueRootOutcome) := do
  let saved ← saveState
  try
    let goal ← getMainGoal
    -- Normalize local `let` declarations in the target as well as in the
    -- candidate. This keeps the executable certificate closed while the final
    -- definitional-equality check still validates the user's original goal.
    let target ← withMainContext do
      zetaReduce (← instantiateMVars (← goal.getType))
    let spec ←
      match ← parseSystemRootTarget target with
      | .ok spec => pure spec
      | .error failure =>
          saved.restore
          return .error failure
    let certificateResult ← withMainContext do
      elaborateCertificate certificateSyntax spec.dimension
    let certificate ←
      match certificateResult with
      | .ok certificate => pure certificate
      | .error (expected, actual) =>
          saved.restore
          return .error (.dimensionMismatch expected actual)
    -- `evalExpr` cannot execute an expression that still refers to a local
    -- let declaration.  Zeta-reduce here so locally named certificates have
    -- exactly the same behavior as declarations and inline literals.
    let certificate ← withMainContext do
      zetaReduce (← instantiateMVars certificate)
    let cfg ← mkAppM ``LeanCert.Engine.EvalConfig.mk #[toExpr taylorDepth]
    verifySystemUniqueRootCandidate saved goal target spec certificate cfg
  catch exception =>
    saved.restore
    return .error (.internalFailure (← exception.toMessageData.toString))

/-- Reporting-aware I2 core. Candidate generation is untrusted; the selected
center and preconditioner are reconstructed as a typed certificate and replayed
through exactly the same checker/golden-theorem path as I1. -/
unsafe def systemUniqueRootAutomaticCoreTyped (maxIterations : Nat := 8)
    (maxDimension : Nat := 4) (taylorDepth : Nat := 10) :
    TacticM (Except SystemUniqueRootFailure SystemUniqueRootOutcome) := do
  let saved ← saveState
  try
    let goal ← getMainGoal
    let target ← withMainContext do
      zetaReduce (← instantiateMVars (← goal.getType))
    let spec ←
      match ← parseSystemRootTarget target with
      | .ok spec => pure spec
      | .error failure =>
          saved.restore
          return .error failure
    let cfg ← mkAppM ``LeanCert.Engine.EvalConfig.mk #[toExpr taylorDepth]
    let searchCfg ← mkAppM ``LeanCert.Engine.AutomaticKrawczykConfig.mk
      #[toExpr maxIterations, toExpr maxDimension, toExpr 20]
    let reportExpr ← mkAppM ``LeanCert.Engine.generateAutomaticKrawczyk
      #[spec.system, spec.box, cfg, searchCfg]
    let report ← evalExpr AutomaticKrawczykReport
      (mkConst ``AutomaticKrawczykReport) reportExpr
    if let some _ := report.failure then
      saved.restore
      return .error (.generationFailed report)
    let certificate ← mkAppM ``LeanCert.Engine.KrawczykCert.ofLists
      #[spec.dimension, toExpr report.center, toExpr report.preconditioner]
    verifySystemUniqueRootCandidate saved goal target spec certificate cfg (some report)
  catch exception =>
    saved.restore
    return .error (.internalFailure (← exception.toMessageData.toString))

private def checkStageMessage : KrawczykCheckStage → String
  | .accepted => "the checker rejected the certificate without a classified component failure"
  | .unsupportedAD =>
      "the system contains an expression outside the differentiable checked-AD fragment"
  | .centerOutside => "the proposed center is outside the target box"
  | .singularPreconditioner => "the proposed preconditioner is singular"
  | .contractionNotStrict => "the checked contraction bound is not strictly below 1"
  | .imageNotStrictlyInside =>
      "the checked Newton image is not strictly inside the target box"

private def generationFailureMessage : AutomaticKrawczykFailure → String
  | .invalidDimension => "automatic Krawczyk generation requires a positive dimension"
  | .dimensionLimit actual limit =>
      s!"system dimension {actual} exceeds the automatic limit {limit}; provide an explicit certificate"
  | .unsupportedAD =>
      "the system contains an expression outside the differentiable checked-AD fragment"
  | .singularPointJacobian attempt =>
      s!"the rational midpoint Jacobian was singular at attempt {attempt}"
  | .centerEscaped attempt =>
      s!"the interval-Newton refinement left the target box after attempt {attempt}"
  | .stagnated attempt =>
      s!"candidate refinement stagnated after attempt {attempt}"
  | .exhausted attempts =>
      s!"candidate search exhausted its configured budget after {attempts} attempt(s)"

private def failureMessage : SystemUniqueRootFailure → String
  | .unsupportedGoal detail =>
      s!"system_unique_root does not recognize this goal.\n{detail}"
  | .dimensionMismatch expected actual =>
      s!"Krawczyk certificate dimension mismatch.\nExpected: {expected}\nFound: {actual}"
  | .generationFailed report =>
      let detail := report.failure.map generationFailureMessage |>.getD
        "candidate generation returned no certificate"
      s!"Automatic Krawczyk candidate generation failed: {detail}.\n\
        Last center: {report.center}\n\
        Last checked contraction bound: {report.contractionBound}"
  | .rejected inspection =>
      s!"Krawczyk certificate rejected: {checkStageMessage inspection.stage}.\n\
        Checked contraction bound: {inspection.contractionBound}"
  | .verificationFailure detail => detail
  | .transportFailure detail =>
      s!"Krawczyk proof transport failed:\n{detail}"
  | .internalFailure detail =>
      s!"Krawczyk certification encountered an internal error:\n{detail}"

private def verificationLabel (event : VerificationEvent) : String :=
  match event.used with
  | .kernel => "kernel"
  | .native => "native"

private def requestedVerificationLabel : VerificationMode → String
  | .kernel => "kernel"
  | .native => "native"
  | .auto => "auto"

private unsafe def runSystemUniqueRoot (certificate : TSyntax `term) (taylorDepth : Nat)
    (explain : Bool) : TacticM Unit := do
  match ← systemUniqueRootCoreTyped certificate taylorDepth with
  | .error failure => throwError (failureMessage failure)
  | .ok outcome =>
      if explain then
        logInfo m!"LeanCert recognized: nonlinear system uniqueness

Selected strategy:
  manual Krawczyk contraction certificate

Certificate:
  Dimension: {outcome.inspection.dimension}
  Center: {outcome.inspection.center}
  Checked contraction bound: {outcome.inspection.contractionBound} < 1

Certificate verification:
  requested {requestedVerificationLabel outcome.verification.requested} → used {verificationLabel outcome.verification}
Checker: {outcome.checker}
Verifier: {outcome.verifier}

Suggested proof:
  by
    system_unique_root using {certificate.raw.reprint.getD "cert"}"

private unsafe def runSystemUniqueRootAutomatic (maxIterations maxDimension taylorDepth : Nat)
    (explain : Bool) : TacticM Unit := do
  match ← systemUniqueRootAutomaticCoreTyped maxIterations maxDimension taylorDepth with
  | .error failure => throwError (failureMessage failure)
  | .ok outcome =>
      if explain then
        let search := outcome.search.getD { dimension := outcome.inspection.dimension }
        logInfo m!"LeanCert recognized: nonlinear system uniqueness

Selected strategy:
  automatic Krawczyk candidate generation

Candidate search:
  Dimension: {search.dimension}
  Attempts: {search.attempts}
  Newton refinements: {search.refinements}
  Selected center: {search.center}
  Generated preconditioner: {search.preconditioner}
  Checked contraction bound: {outcome.inspection.contractionBound} < 1

Certificate verification:
  requested {requestedVerificationLabel outcome.verification.requested} → used {verificationLabel outcome.verification}
Checker: {outcome.checker}
Verifier: {outcome.verifier}

Suggested proof:
  by
    system_unique_root

Stable explicit certificate:
  center := {search.center}
  preconditioner := {search.preconditioner}"

declare_syntax_cat systemUniqueRootConfigItem
syntax "(" &"taylorDepth" " := " num ")" : systemUniqueRootConfigItem
syntax "(" &"maxIterations" " := " num ")" : systemUniqueRootConfigItem
syntax "(" &"maxDimension" " := " num ")" : systemUniqueRootConfigItem
syntax "(" &"trust" " := " leancertTrustMode ")" : systemUniqueRootConfigItem

syntax (name := systemUniqueRootTac) "system_unique_root" " using " term:max
  systemUniqueRootConfigItem* : tactic
syntax (name := systemUniqueRootQuestionTac) "system_unique_root?" " using " term:max
  systemUniqueRootConfigItem* : tactic
syntax (name := systemUniqueRootAutoTac) "system_unique_root"
  systemUniqueRootConfigItem* : tactic
syntax (name := systemUniqueRootAutoQuestionTac) "system_unique_root?"
  systemUniqueRootConfigItem* : tactic

private structure SystemUniqueRootConfig where
  taylorDepth : Nat := 10
  maxIterations : Nat := 8
  maxDimension : Nat := 4
  trust : Option VerificationMode := none

private def parseSystemUniqueRootConfig (items : Array Syntax) :
    TacticM SystemUniqueRootConfig := do
  let mut cfg : SystemUniqueRootConfig := {}
  for item in items do
    match item with
    | `(systemUniqueRootConfigItem| (taylorDepth := $n:num)) =>
        cfg := { cfg with taylorDepth := n.getNat }
    | `(systemUniqueRootConfigItem| (maxIterations := $n:num)) =>
        cfg := { cfg with maxIterations := n.getNat }
    | `(systemUniqueRootConfigItem| (maxDimension := $n:num)) =>
        cfg := { cfg with maxDimension := n.getNat }
    | `(systemUniqueRootConfigItem| (trust := $m:leancertTrustMode)) =>
        let raw := m.raw.reprint.getD ""
        let some mode := VerificationMode.ofString? raw
          | throwErrorAt m "invalid trust mode '{raw}'; expected kernel, native, or auto"
        cfg := { cfg with trust := some mode }
    | _ => throwUnsupportedSyntax
  return cfg

@[tactic systemUniqueRootTac]
unsafe def elabSystemUniqueRoot : Tactic := fun stx => do
  match stx with
  | `(tactic| system_unique_root using $certificate:term
      $items:systemUniqueRootConfigItem*) => do
      let cfg ← parseSystemUniqueRootConfig items
      withTrustMode cfg.trust do
        runSystemUniqueRoot certificate cfg.taylorDepth false
  | _ => throwUnsupportedSyntax

@[tactic systemUniqueRootQuestionTac]
unsafe def elabSystemUniqueRootQuestion : Tactic := fun stx => do
  match stx with
  | `(tactic| system_unique_root? using $certificate:term
      $items:systemUniqueRootConfigItem*) => do
      let cfg ← parseSystemUniqueRootConfig items
      withTrustMode cfg.trust do
        runSystemUniqueRoot certificate cfg.taylorDepth true
  | _ => throwUnsupportedSyntax

@[tactic systemUniqueRootAutoTac]
unsafe def elabSystemUniqueRootAuto : Tactic := fun stx => do
  match stx with
  | `(tactic| system_unique_root $items:systemUniqueRootConfigItem*) => do
      let cfg ← parseSystemUniqueRootConfig items
      withTrustMode cfg.trust do
        runSystemUniqueRootAutomatic cfg.maxIterations cfg.maxDimension cfg.taylorDepth false
  | _ => throwUnsupportedSyntax

@[tactic systemUniqueRootAutoQuestionTac]
unsafe def elabSystemUniqueRootAutoQuestion : Tactic := fun stx => do
  match stx with
  | `(tactic| system_unique_root? $items:systemUniqueRootConfigItem*) => do
      let cfg ← parseSystemUniqueRootConfig items
      withTrustMode cfg.trust do
        runSystemUniqueRootAutomatic cfg.maxIterations cfg.maxDimension cfg.taylorDepth true
  | _ => throwUnsupportedSyntax

end LeanCert.Tactic
