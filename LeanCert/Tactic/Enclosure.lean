/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Tactic.Extension.Execute
import LeanCert.Tactic.LeanCert.Semantic.Parse.Bound

/-! # Focused registered-enclosure tactic

`enclosure_bound` is the lightweight executable front end for downstream
`@[leancert_enclosure]` rules. It shares parsing, preparation, checked
execution, subdivision, and trust handling with `leancert`, but intentionally
does not import the semantic router or unrelated solver families.
-/

open Lean Meta Elab Tactic

namespace LeanCert.Tactic

open LeanCert.Tactic.Semantic
open LeanCert.Tactic.Extension

private structure EnclosureConfig where
  taylorDepth : Nat := 10
  subdivisions : Nat := 4
  trust : Option VerificationMode := none

declare_syntax_cat enclosureConfigItem
syntax "(" &"taylorDepth" " := " num ")" : enclosureConfigItem
syntax "(" &"subdivisions" " := " num ")" : enclosureConfigItem
syntax "(" &"trust" " := " leancertTrustMode ")" : enclosureConfigItem

private def elaborateEnclosureConfig (items : Array Syntax) :
    TacticM EnclosureConfig := do
  let mut cfg : EnclosureConfig := {}
  for item in items do
    match item with
    | `(enclosureConfigItem| (taylorDepth := $n:num)) =>
        cfg := { cfg with taylorDepth := n.getNat }
    | `(enclosureConfigItem| (subdivisions := $n:num)) =>
        cfg := { cfg with subdivisions := n.getNat }
    | `(enclosureConfigItem| (trust := $m:leancertTrustMode)) =>
        let raw := m.raw.reprint.getD ""
        let some mode := VerificationMode.ofString? raw
          | throwErrorAt m "invalid trust mode '{raw}'; expected kernel, native, or auto"
        cfg := { cfg with trust := some mode }
    | _ => throwUnsupportedSyntax
  return cfg

private def failureMessage : RegisteredEnclosureFailure → MessageData
  | .notApplicable =>
      m!"enclosure_bound did not find an applicable registered unary enclosure rule.\n\
         Expected a goal such as `∀ x ∈ Set.Icc a b, f x ≤ c` containing a function\n\
         registered with `@[leancert_enclosure]`."
  | .unsupported expression detail =>
      m!"enclosure_bound cannot evaluate `{expression}`.\n{detail}"
  | .domainObstruction operation detail =>
      m!"Domain obstruction while evaluating `{operation}`:\n{detail}\n\
         Narrow the interval or prove the required domain condition."
  | .inconclusive detail enclosure =>
      m!"Registered enclosure proof was inconclusive.\n{detail}\n\
         Last enclosure: {repr enclosure}"
  | .rejected checker enclosure detail =>
      m!"Registered enclosure candidate was rejected.\n{detail}\n\
         Checker: {repr checker}\nLast enclosure: {repr enclosure}"
  | .exhausted maxDepth boxes deepest leaves enclosure detail =>
      m!"Registered enclosure subdivision reached depth {maxDepth} after examining\n\
         {boxes} boxes (deepest depth {deepest}; {leaves} certified leaves).\n\
         Last failure: {detail}\nLast enclosure: {repr enclosure}\n\
         Increase `(subdivisions := ...)`, narrow the interval, or improve the registered candidate."
  | .verificationFailure detail =>
      m!"Registered enclosure certificate verification failed.\n{detail}"

private def successReport (cfg : EnclosureConfig) (mode : VerificationMode)
    (outcome : RegisteredEnclosureOutcome) : MessageData := Id.run do
  let kernelChecks := outcome.verification.kernelChecks
  let nativeChecks := outcome.verification.nativeChecks
  let mut retainedRules : Array (Name × Name × Name) := #[]
  for observation in outcome.observations do
    let identity := (observation.rule.functionName, observation.rule.checkerName,
      observation.rule.theoremName)
    unless retainedRules.any (fun existing => existing == identity) do
      retainedRules := retainedRules.push identity
  let ruleSummary := String.intercalate "\n" <| retainedRules.toList.map fun
      (functionName, checkerName, theoremName) =>
    s!"    {functionName}: checker `{checkerName}`, theorem `{theoremName}`"
  let subdivision :=
    match outcome.subdivision with
    | none => "  Subdivision: not needed"
    | some stats =>
        s!"  Subdivision: {stats.certifiedLeaves} certified leaves from \
          {stats.boxesExamined} examined boxes (deepest depth {stats.deepestDepthUsed} \
          of {stats.configuredMaxDepth})"
  return m!"LeanCert recognized: registered unary enclosure bound

Selected strategy:
  Proof-carrying enclosure composition with adaptive subdivision

Certificate generation:
  Registered certificates checked: {outcome.observations.size}
  Distinct registered rules retained: {retainedRules.size}
{ruleSummary}
  Core composition steps: {outcome.compositionSteps}
{subdivision}

Certificate verification:
  Requested trust: {mode.asString}
  Kernel checks: {kernelChecks}
  Native checks: {nativeChecks}

Suggested proof:
  by enclosure_bound (taylorDepth := {cfg.taylorDepth}) \
    (subdivisions := {cfg.subdivisions}) (trust := {mode.asString})"

private unsafe def runEnclosureBound (cfg : EnclosureConfig) (explain : Bool) :
    TacticM Unit := do
  let saved ← saveState
  let target ← instantiateMVars (← getMainTarget)
  let spec ←
    match ← parseBound? target with
    | some spec => pure spec
    | none =>
        saved.restore
        throwError "enclosure_bound expects a quantified interval-bound goal, for example \
          `∀ x ∈ Set.Icc a b, f x ≤ c`."
  let prepared ←
    match ← prepareGoal (.bound spec) with
    | .ok prepared => pure prepared
    | .error failure =>
        saved.restore
        throwError "enclosure_bound could not prepare the goal:\n{failure.detail}"
  let mode := (← VerificationConfig.current).mode
  match ← registeredEnclosureBoundSubdivCoreTyped
      prepared (-53) cfg.taylorDepth cfg.subdivisions with
  | .ok outcome =>
      if explain then logInfo (successReport cfg mode outcome)
  | .error failure =>
      saved.restore
      throwError (failureMessage failure)

/-- Prove a quantified interval bound using registered downstream enclosure
rules, checked core composition, and adaptive subdivision. -/
syntax (name := enclosureBoundTac) "enclosure_bound" enclosureConfigItem* : tactic

/-- Like `enclosure_bound`, and report the retained certificates, subdivision
statistics, verification route, and a stable suggested proof. -/
syntax (name := enclosureBoundQuestionTac) "enclosure_bound?" enclosureConfigItem* : tactic

@[tactic enclosureBoundTac]
unsafe def elabEnclosureBound : Tactic := fun stx => do
  let cfg ← elaborateEnclosureConfig stx[1].getArgs
  withTrustMode cfg.trust do runEnclosureBound cfg false

@[tactic enclosureBoundQuestionTac]
unsafe def elabEnclosureBoundQuestion : Tactic := fun stx => do
  let cfg ← elaborateEnclosureConfig stx[1].getArgs
  withTrustMode cfg.trust do runEnclosureBound cfg true

end LeanCert.Tactic
