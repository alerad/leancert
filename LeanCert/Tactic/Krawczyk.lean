/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Tactic.LeanCert.Semantic.Parse
import LeanCert.Tactic.Verification
import LeanCert.Validity.Krawczyk

/-!
# Manual Krawczyk certificate tactic

`system_unique_root using cert` is the I1 front end for the existing checked
Krawczyk engine. Candidate construction is deliberately external to this
module; the supplied certificate is accepted only through `krawczykCheck` and
`verify_unique_system_root`.
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
  | rejected (inspection : KrawczykInspection)
  | verificationFailure (detail : String)
  | transportFailure (detail : String)
  | internalFailure (detail : String)
  deriving Inhabited, Repr

/-- Runtime facts retained by a successful manual Krawczyk proof. -/
structure SystemUniqueRootOutcome where
  inspection : KrawczykInspection
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
    let semantic ← withMainContext do
      Semantic.parseGoal target
    let spec ←
      match semantic with
      | .ok (.systemRoot spec) => pure spec
      | .ok _ =>
          saved.restore
          return .error (.unsupportedGoal
            "expected `∃! x : Fin n → ℝ, FinBoxMem x X ∧ SystemZero F x`")
      | .error failure =>
          saved.restore
          return .error (.unsupportedGoal failure.detail)
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
        return .ok { inspection, verification := event }
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

private def failureMessage : SystemUniqueRootFailure → String
  | .unsupportedGoal detail =>
      s!"system_unique_root does not recognize this goal.\n{detail}"
  | .dimensionMismatch expected actual =>
      s!"Krawczyk certificate dimension mismatch.\nExpected: {expected}\nFound: {actual}"
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

declare_syntax_cat systemUniqueRootConfigItem
syntax "(" &"taylorDepth" " := " num ")" : systemUniqueRootConfigItem
syntax "(" &"trust" " := " leancertTrustMode ")" : systemUniqueRootConfigItem

syntax (name := systemUniqueRootTac) "system_unique_root" " using " term:max
  systemUniqueRootConfigItem* : tactic
syntax (name := systemUniqueRootQuestionTac) "system_unique_root?" " using " term:max
  systemUniqueRootConfigItem* : tactic

private def parseSystemUniqueRootConfig (items : Array Syntax) :
    TacticM (Nat × Option VerificationMode) := do
  let mut depth := 10
  let mut trust : Option VerificationMode := none
  for item in items do
    match item with
    | `(systemUniqueRootConfigItem| (taylorDepth := $n:num)) =>
        depth := n.getNat
    | `(systemUniqueRootConfigItem| (trust := $m:leancertTrustMode)) =>
        let raw := m.raw.reprint.getD ""
        let some mode := VerificationMode.ofString? raw
          | throwErrorAt m "invalid trust mode '{raw}'; expected kernel, native, or auto"
        trust := some mode
    | _ => throwUnsupportedSyntax
  return (depth, trust)

@[tactic systemUniqueRootTac]
unsafe def elabSystemUniqueRoot : Tactic := fun stx => do
  match stx with
  | `(tactic| system_unique_root using $certificate:term
      $items:systemUniqueRootConfigItem*) => do
      let (depth, trust) ← parseSystemUniqueRootConfig items
      withTrustMode trust do
        runSystemUniqueRoot certificate depth false
  | _ => throwUnsupportedSyntax

@[tactic systemUniqueRootQuestionTac]
unsafe def elabSystemUniqueRootQuestion : Tactic := fun stx => do
  match stx with
  | `(tactic| system_unique_root? using $certificate:term
      $items:systemUniqueRootConfigItem*) => do
      let (depth, trust) ← parseSystemUniqueRootConfig items
      withTrustMode trust do
        runSystemUniqueRoot certificate depth true
  | _ => throwUnsupportedSyntax

end LeanCert.Tactic
