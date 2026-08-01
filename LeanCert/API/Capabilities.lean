/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.API.Eval

/-!
# Backend capability registry

This module records backend support separately at the engine, public-API,
tactic, and automatic-selection layers. It is descriptive rather than a
dispatcher: numerical implementations remain in the engine and public façades.

The generated Markdown matrix is checked against the documentation by
`LeanCert.Test.CapabilityMatrix`, preventing the public support table from
drifting away from this executable registry.
-/

namespace LeanCert

open LeanCert.Engine

/-- Support at one product layer. Reasons make intentional omissions distinct
from capabilities that simply have not been promoted yet. -/
inductive SupportStatus where
  | supported
  | experimental (reason : String)
  | unavailable (reason : String)
  | notPlanned (reason : String)
  deriving Repr, DecidableEq

namespace SupportStatus

def label : SupportStatus → String
  | .supported => "supported"
  | .experimental _ => "experimental"
  | .unavailable _ => "unavailable"
  | .notPlanned _ => "not planned"

def reason : SupportStatus → Option String
  | .supported => none
  | .experimental reason | .unavailable reason | .notPlanned reason => some reason

def implemented : SupportStatus → Bool
  | .supported | .experimental _ => true
  | .unavailable _ | .notPlanned _ => false

end SupportStatus

/-- One operation/backend row in the cross-layer capability registry. -/
structure BackendCapability where
  operation : BackendOperation
  backend : ConcreteBackend
  engine : SupportStatus
  publicAPI : SupportStatus
  tactic : SupportStatus
  automatic : SupportStatus
  expressionFragment : String
  configuration : List String
  resultRepresentation : String
  domainChecked : Bool
  candidateDiscovery : Bool
  certificateChecker : Bool
  note : String := ""
  deriving Repr, DecidableEq

def backendOperationLabel : BackendOperation → String
  | .intervalEvaluation => "interval evaluation"
  | .checkedDerivative => "checked derivative"
  | .checkedGradient => "checked gradient"
  | .globalOptimization => "global optimization"
  | .partitionIntegration => "partition integration"
  | .rootExistence => "root existence"
  | .rootUniqueness => "root uniqueness"

def concreteBackendLabel : ConcreteBackend → String
  | .rational => "Rational"
  | .dyadic => "Dyadic"
  | .affine => "Affine"

private def supported : SupportStatus := .supported
private def noTactic : SupportStatus :=
  .notPlanned "programmatic checked operation; no dedicated tactic is planned"
private def notPromoted (reason : String) : SupportStatus := .unavailable reason
private def noAffineAD : SupportStatus :=
  .notPlanned "requires a proved dual-affine evaluator and evidence of tighter derivative bounds"
private def noAffineIntegration : SupportStatus :=
  .notPlanned "partition summation is not expected to retain enough affine correlation"
private def noAffineRoots : SupportStatus :=
  .notPlanned "depends on useful affine AD and contraction benchmarks"
private def noDyadicRoots : SupportStatus :=
  .unavailable "checked Dyadic root certificates have not been implemented"

/-- Authoritative operation/backend support registry. -/
def backendCapabilities : List BackendCapability := [
  { operation := .intervalEvaluation, backend := .rational,
    engine := supported, publicAPI := supported, tactic := supported, automatic := supported,
    expressionFragment := "arbitrary checked Expr", configuration := ["fixed Taylor depth 10"],
    resultRepresentation := "IntervalRat", domainChecked := true,
    candidateDiscovery := false, certificateChecker := true },
  { operation := .intervalEvaluation, backend := .dyadic,
    engine := supported, publicAPI := supported, tactic := supported, automatic := supported,
    expressionFragment := "arbitrary checked Expr", configuration := ["Taylor depth", "precision"],
    resultRepresentation := "IntervalDyadic → IntervalRat", domainChecked := true,
    candidateDiscovery := false, certificateChecker := true },
  { operation := .intervalEvaluation, backend := .affine,
    engine := supported, publicAPI := supported,
    tactic := notPromoted "the direct bound tactic does not expose explicit Affine selection",
    automatic := supported, expressionFragment := "arbitrary checked Expr",
    configuration := ["Taylor depth", "maximum noise symbols"],
    resultRepresentation := "AffineForm → IntervalRat", domainChecked := true,
    candidateDiscovery := false, certificateChecker := true,
    note := "some transcendental nodes conservatively concretize to intervals" },

  { operation := .checkedDerivative, backend := .rational,
    engine := supported, publicAPI := supported, tactic := noTactic, automatic := supported,
    expressionFragment := "domain-aware AD (including inv/log)", configuration := ["Taylor depth"],
    resultRepresentation := "DerivativeOutcome", domainChecked := true,
    candidateDiscovery := false, certificateChecker := true },
  { operation := .checkedDerivative, backend := .dyadic,
    engine := supported, publicAPI := supported, tactic := noTactic, automatic := supported,
    expressionFragment := "domain-aware AD (including inv/log)",
    configuration := ["Taylor depth", "precision"],
    resultRepresentation := "DerivativeOutcome", domainChecked := true,
    candidateDiscovery := false, certificateChecker := true },
  { operation := .checkedDerivative, backend := .affine,
    engine := noAffineAD, publicAPI := noAffineAD, tactic := noAffineAD, automatic := noAffineAD,
    expressionFragment := "none", configuration := [], resultRepresentation := "none",
    domainChecked := false, candidateDiscovery := false, certificateChecker := false },

  { operation := .checkedGradient, backend := .rational,
    engine := supported, publicAPI := supported, tactic := noTactic, automatic := supported,
    expressionFragment := "domain-aware AD (including inv/log)", configuration := ["Taylor depth"],
    resultRepresentation := "GradientOutcome", domainChecked := true,
    candidateDiscovery := false, certificateChecker := true },
  { operation := .checkedGradient, backend := .dyadic,
    engine := supported, publicAPI := supported, tactic := noTactic, automatic := supported,
    expressionFragment := "domain-aware AD (including inv/log)",
    configuration := ["Taylor depth", "precision"],
    resultRepresentation := "GradientOutcome", domainChecked := true,
    candidateDiscovery := false, certificateChecker := true },
  { operation := .checkedGradient, backend := .affine,
    engine := noAffineAD, publicAPI := noAffineAD, tactic := noAffineAD, automatic := noAffineAD,
    expressionFragment := "none", configuration := [], resultRepresentation := "none",
    domainChecked := false, candidateDiscovery := false, certificateChecker := false },

  { operation := .globalOptimization, backend := .rational,
    engine := supported, publicAPI := supported,
    tactic := notPromoted "tactic-side backend selection currently resolves to Dyadic",
    automatic := notPromoted "automatic optimization selects Dyadic",
    expressionFragment := "arbitrary checked Expr", configuration := ["fixed Taylor depth 10"],
    resultRepresentation := "GlobalResult", domainChecked := true,
    candidateDiscovery := true, certificateChecker := true },
  { operation := .globalOptimization, backend := .dyadic,
    engine := supported, publicAPI := supported, tactic := supported, automatic := supported,
    expressionFragment := "arbitrary checked Expr", configuration := ["Taylor depth", "precision"],
    resultRepresentation := "GlobalResult", domainChecked := true,
    candidateDiscovery := true, certificateChecker := true },
  { operation := .globalOptimization, backend := .affine,
    engine := supported, publicAPI := supported,
    tactic := notPromoted "tactic-side backend selection currently resolves to Dyadic",
    automatic := notPromoted "automatic optimization selects Dyadic",
    expressionFragment := "arbitrary checked Expr",
    configuration := ["Taylor depth", "maximum noise symbols"],
    resultRepresentation := "GlobalResult", domainChecked := true,
    candidateDiscovery := true, certificateChecker := true },

  { operation := .partitionIntegration, backend := .rational,
    engine := supported, publicAPI := supported, tactic := supported, automatic := supported,
    expressionFragment := "arbitrary checked Expr", configuration := ["fixed Taylor depth 10", "partitions"],
    resultRepresentation := "IntegralOutcome", domainChecked := true,
    candidateDiscovery := true, certificateChecker := true },
  { operation := .partitionIntegration, backend := .dyadic,
    engine := supported, publicAPI := supported,
    tactic := notPromoted "checked implementation is not yet wired into the theorem tactic/router",
    automatic := notPromoted "automatic selection awaits comparative integration benchmarks",
    expressionFragment := "arbitrary checked Expr",
    configuration := ["Taylor depth", "precision", "partitions"],
    resultRepresentation := "IntegralOutcome", domainChecked := true,
    candidateDiscovery := false, certificateChecker := true },
  { operation := .partitionIntegration, backend := .affine,
    engine := noAffineIntegration, publicAPI := noAffineIntegration,
    tactic := noAffineIntegration, automatic := noAffineIntegration,
    expressionFragment := "none", configuration := [], resultRepresentation := "none",
    domainChecked := false, candidateDiscovery := false, certificateChecker := false },

  { operation := .rootExistence, backend := .rational,
    engine := supported, publicAPI := supported, tactic := supported, automatic := supported,
    expressionFragment := "checked continuous expressions", configuration := ["fixed Taylor depth 10"],
    resultRepresentation := "sign-change certificate", domainChecked := true,
    candidateDiscovery := true, certificateChecker := true },
  { operation := .rootExistence, backend := .dyadic,
    engine := noDyadicRoots, publicAPI := noDyadicRoots, tactic := noDyadicRoots,
    automatic := noDyadicRoots, expressionFragment := "none", configuration := [],
    resultRepresentation := "none", domainChecked := false,
    candidateDiscovery := false, certificateChecker := false },
  { operation := .rootExistence, backend := .affine,
    engine := noAffineRoots, publicAPI := noAffineRoots, tactic := noAffineRoots,
    automatic := noAffineRoots, expressionFragment := "none", configuration := [],
    resultRepresentation := "none", domainChecked := false,
    candidateDiscovery := false, certificateChecker := false },

  { operation := .rootUniqueness, backend := .rational,
    engine := supported, publicAPI := supported, tactic := supported, automatic := supported,
    expressionFragment := "ADSupported", configuration := ["Taylor depth"],
    resultRepresentation := "Newton/Krawczyk certificate", domainChecked := true,
    candidateDiscovery := true, certificateChecker := true },
  { operation := .rootUniqueness, backend := .dyadic,
    engine := noDyadicRoots, publicAPI := noDyadicRoots, tactic := noDyadicRoots,
    automatic := noDyadicRoots, expressionFragment := "none", configuration := [],
    resultRepresentation := "none", domainChecked := false,
    candidateDiscovery := false, certificateChecker := false },
  { operation := .rootUniqueness, backend := .affine,
    engine := noAffineRoots, publicAPI := noAffineRoots, tactic := noAffineRoots,
    automatic := noAffineRoots, expressionFragment := "none", configuration := [],
    resultRepresentation := "none", domainChecked := false,
    candidateDiscovery := false, certificateChecker := false }
]

def allBackendOperations : List BackendOperation := [
  .intervalEvaluation, .checkedDerivative, .checkedGradient,
  .globalOptimization, .partitionIntegration, .rootExistence, .rootUniqueness
]

def allConcreteBackends : List ConcreteBackend := [.rational, .dyadic, .affine]

/-- Every operation/backend pair must have exactly one registry row. -/
def capabilityRegistryComplete : Bool :=
  allBackendOperations.all fun operation =>
    allConcreteBackends.all fun backend =>
      (backendCapabilities.filter fun row =>
        row.operation == operation && row.backend == backend).length == 1

/-- Engine-layer registry claims agree with the executable dispatcher table. -/
def capabilityEngineMatchesDispatcher : Bool :=
  backendCapabilities.all fun row =>
    row.engine.implemented == backendSupports row.backend row.operation

private def yesNo (value : Bool) : String := if value then "yes" else "no"

def BackendCapability.markdownRow (capability : BackendCapability) : String :=
  let configs := if capability.configuration.isEmpty then "—"
    else String.intercalate ", " capability.configuration
  let note := if capability.note.isEmpty then "—" else capability.note
  s!"| {backendOperationLabel capability.operation} | {concreteBackendLabel capability.backend} | {capability.engine.label} | {capability.publicAPI.label} | {capability.tactic.label} | {capability.automatic.label} | {capability.expressionFragment} | {configs} | {capability.resultRepresentation} | {yesNo capability.domainChecked} | {note} |"

/-- Markdown rendered from `backendCapabilities`. Documentation tests require
this exact generated block to remain present in the backend-selection page. -/
def capabilityMatrixMarkdown : String :=
  String.intercalate "\n" <| [
    "| Operation | Backend | Engine | Public API | Tactic | Automatic | Expression fragment | Configuration | Result | Domain checked | Note |",
    "|---|---|---|---|---|---|---|---|---|---|---|"
  ] ++ backendCapabilities.map BackendCapability.markdownRow

end LeanCert
