/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Tactic.LeanCert.Diagnostic.Evidence
import LeanCert.Tactic.LeanCert.Solver.Protocol

/-!
# User-Facing Diagnostic Rendering

All public output is rendered here.  Solver internals may retain kernel
expressions in debug traces, but ordinary failures and `leancert?` reports use
mathematical language.
-/

namespace LeanCert.Tactic.Diagnostic

open LeanCert.Tactic.Semantic
open LeanCert.Tactic.Solver

/-- A bounded decimal rendering for user-facing numerical evidence.  The
underlying checker continues to use the exact rational value. -/
def formatRatApprox (value : ℚ) (digits : Nat := 6) : String :=
  let numerator := value.num
  let denominator := value.den
  if denominator == 1 then
    toString numerator
  else
    let (sign, magnitude) :=
      if numerator < 0 then ("-", -numerator) else ("", numerator)
    let integerPart := magnitude / denominator
    let scale := 10 ^ digits
    let fractionalPart := magnitude % denominator
    let scaled := fractionalPart * scale / denominator
    let rawDigits := toString scaled
    let padding := String.ofList (List.replicate (digits - rawDigits.length) '0')
    s!"{sign}{integerPart}.{padding}{rawDigits}"

def intentLabel : GoalIntent → String
  | .integralBound => "definite integral bound"
  | .uniqueRoot => "unique real root"
  | .rootExists => "real root existence"
  | .noRoot => "nonvanishing on an interval"
  | .argmin => "existence of a minimizer"
  | .argmax => "existence of a maximizer"
  | .existentialMinimum => "discovered lower bound"
  | .existentialMaximum => "discovered upper bound"
  | .finiteSum => "finite sum"
  | .multivariateBound => "multivariate bound"
  | .intervalBound => "univariate interval bound"
  | .pointInequality => "closed numerical comparison"
  | .certificateCheck => "closed certificate check"
  | .conjunction => "conjunction of numerical theorems"

def attemptOutcome : AttemptOutcome → String
  | .unsupported evidence =>
      let unfoldedText :=
        if evidence.unfolded.isEmpty then ""
        else s!"\nLeanCert successfully unfolded: {String.intercalate ", "
          (evidence.unfolded.toList.map toString)}"
      s!"Could not reify the remaining expression:\n  {evidence.expression}{unfoldedText}"
  | .rejected evidence =>
      match evidence.enclosure with
      | some interval =>
          s!"The candidate certificate was rejected.\nComputed enclosure: \
            [{interval.lo}, {interval.hi}]"
      | none =>
          s!"{evidence.detail}\nTry increasing `taylorDepth`, enabling subdivision, \
            or using the corresponding dedicated tactic for finer control."
  | .domainObstruction evidence => s!"Domain obstruction: {evidence.reason}"
  | .inconclusive evidence => evidence.detail
  | .refuted evidence =>
      let detail := evidence.detail.map (fun value => s!"\n{value}") |>.getD ""
      s!"Certified counterexample: {evidence.witness}{detail}"
  | .notApplicable => "The solver does not apply to this theorem."
  | .proved _ => "The solver proved the theorem."
  | .routerFailure _ => "A nested semantic route failed."
  | .internalError solver _ =>
      s!"LeanCert encountered an internal proof-construction error in `{solver}`. \
        Enable `set_option trace.LeanCert.solver true` when reporting this bug."

private def attemptLedger (attempts : Array AttemptDiagnostic) : String :=
  if attempts.isEmpty then "  No applicable strategy ran."
  else
    String.intercalate "\n" <| attempts.toList.zipIdx.map fun (attempt, index) =>
      s!"  {index + 1}. {attempt.strategy}\n     {attempt.outcome}"

def routerFailure (verbosity : DiagnosticVerbosity) : RouterFailure → String
  | .unsupportedGoal goal detail =>
      s!"LeanCert could not recognize this theorem shape.\n\nGoal:\n  {goal}\n\n\
        {detail}\n\nLeanCert handles numerical comparisons, interval bounds, roots, \
        extrema, finite sums, integrals, and conjunctions of supported numerical theorems."
  | .unsupportedExpression expression detail =>
      s!"LeanCert recognized the theorem, but could not translate a numerical expression.\n\n\
        Unsupported expression:\n  {expression}\n\n{detail}\n\n\
        Unfold a reducible wrapper or reformulate it with a supported arithmetic \
        or transcendental operation."
  | .unsupportedDomain intent details =>
      s!"LeanCert recognized: {intentLabel intent}\n\nThe domain is not supported:\n\
        {String.intercalate "\n" details.toList}"
  | .domainObstruction intent reason =>
      s!"LeanCert recognized: {intentLabel intent}\n\nDomain obstruction:\n  {reason}\n\n\
        Narrow the domain or prove the required positivity/nonzero condition. \
        Increasing numerical precision does not repair an invalid domain."
  | .portfolioExhausted intent attempts spent budget =>
      match verbosity with
      | .compact =>
          s!"LeanCert recognized a {intentLabel intent}, but no strategy proved it \
            within cost budget {budget} (spent {spent}).\n\n\
            Run `leancert?` on the same goal for the attempted strategies and \
            detailed next steps."
      | .explain =>
          s!"LeanCert recognized: {intentLabel intent}\n\nAttempts:\n\
            {attemptLedger attempts}\n\nBudget: spent {spent} of {budget}\n\nNext steps:\n\
            • Check whether the requested statement is true.\n\
            • Increase `(taylorDepth := ...)`, `(subdivisions := ...)`, or \
              `(maxIterations := ...)` when the corresponding attempt was inconclusive.\n\
            • Use `interval_refute` to search for a certified counterexample."
  | .certifiedRefutation intent? evidence =>
      let recognized := intent?.map (fun intent =>
        s!"LeanCert recognized: {intentLabel intent}\n\n") |>.getD ""
      let detail := evidence.detail.map (fun value => s!"\n{value}") |>.getD ""
      s!"{recognized}The statement is false.\n\nCertified counterexample: \
        {evidence.witness}{detail}"
  | .childFailure index total intent? detail =>
      let label := intent?.map intentLabel |>.getD "numerical theorem"
      s!"LeanCert recognized a conjunction, but child {index} of {total} failed: \
        {label}\n\n{detail}"
  | .conjunctionFailure detail =>
      s!"LeanCert recognized a conjunction, but a child theorem failed.\n\n{detail}"
  | .internalError detail =>
      s!"LeanCert encountered an internal proof-construction error.\n\n{detail}\n\n\
        Enable `set_option trace.LeanCert.solver true` and \
        `set_option trace.LeanCert.router true` when reporting this bug."

def numericalBackend : NumericalBackend → String
  | .rationalInterval => "Rational interval evaluation"
  | .dyadicInterval => "Dyadic interval evaluation"
  | .affineArithmetic => "Affine arithmetic"
  | .exactRational => "exact rational arithmetic"
  | .checkedRationalPartitions => "checked Rational partition integration"

private def effectiveBackend (report : SolverReport) :
    Option NumericalBackend × BackendPolicy :=
  match report.execution.backend with
  | some observed => (some observed, report.plan.backendPolicy)
  | none => (none, report.plan.backendPolicy)

private def renderBackend :
    Option NumericalBackend × BackendPolicy → Option String
  | (some backend, _) => some (numericalBackend backend)
  | (none, .fixed backend) =>
      some s!"Configured backend: {numericalBackend backend}\n  Execution was not \
        observed by the legacy solver adapter."
  | (none, .policy description) =>
      some s!"Policy: {description}\n  The legacy adapter does not yet expose \
        the winning backend."
  | (none, .notApplicable) => none
  | (none, .unknown) => some "not observed by the legacy solver adapter"

private def verificationMode : VerificationMode → String
  | .native => "native"
  | .kernel => "kernel"
  | .auto => "auto"

private def renderVerification (report : SolverReport) : Option String :=
  let usage := report.execution.verificationUsage
  let requested := verificationMode report.plan.verificationRequested
  if usage.kernelChecks == 0 && usage.nativeChecks == 0 then
    match report.plan.strategyId with
    | .exactNormalization => some "not required by this proof strategy"
    | .exactIntegral =>
        some "kernel proof construction; trust selection not applicable"
    | _ =>
        some s!"requested {requested}; actual route not observed by the legacy adapter"
  else
    let used :=
      if usage.kernelChecks > 0 && usage.nativeChecks > 0 then
        s!"mixed: {usage.kernelChecks} kernel, {usage.nativeChecks} native"
      else if usage.kernelChecks > 0 then
        if usage.kernelChecks == 1 then "kernel"
        else s!"kernel ({usage.kernelChecks} checks)"
      else if usage.nativeChecks == 1 then "native"
      else s!"native ({usage.nativeChecks} checks)"
    let reasons :=
      if usage.autoGateReasons.isEmpty then ""
      else s!"\n  Auto gate: {String.intercalate "; " usage.autoGateReasons.toList}"
    let fallback :=
      if usage.kernelFallbacks == 0 then ""
      else s!"\n  {usage.kernelFallbacks} kernel attempt(s) fell back to native"
    some s!"requested {requested} → used {used}{reasons}{fallback}"

private def invocation (proof : ProofSuggestion) : String :=
  let positional :=
    if proof.positionalArgs.isEmpty then ""
    else " " ++ String.intercalate " " proof.positionalArgs.toList
  let named := proof.namedArgs.toList.map fun (key, value) =>
    s!"({key} := {value})"
  let named :=
    if named.isEmpty then "" else " " ++ String.intercalate " " named
  let trust :=
    match proof.trust with
    | some mode =>
        if proof.acceptsInlineTrust then s!" (trust := {verificationMode mode})"
        else ""
    | none => ""
  s!"{proof.tactic}{positional}{named}{trust}"

private def renderProof (proof : ProofSuggestion) : String :=
  match proof.trust with
  | some mode =>
      if proof.acceptsInlineTrust then
        s!"by\n    {invocation proof}"
      else
        s!"by\n    set_option leancert.trust \"{verificationMode mode}\" in\n\
          {invocation proof}"
  | none => s!"by\n    {invocation proof}"

private def renderChildren (children : Array ChildReport) : String :=
  if children.isEmpty then ""
  else
    let rows := children.toList.zipIdx.map fun (child, index) =>
      let backend :=
        match child.backend with
        | some value => s!"; {numericalBackend value}"
        | none =>
            match child.backendPolicy with
            | .fixed value => s!"; configured backend: {numericalBackend value}"
            | .policy value => s!"; backend policy: {value}"
            | .notApplicable => ""
            | .unknown => "; backend not observed"
      s!"  {index + 1}. {intentLabel child.intent} — {child.strategy}{backend}"
    s!"\n\nChild theorems:\n{String.intercalate "\n" rows}"

private def renderOptimization (statistics : Option OptimizationStatistics) : String :=
  match statistics with
  | none => ""
  | some statistics =>
      let actual := statistics.iterations.map
        (fun value => s!"\n  Iterations used: {value}") |>.getD ""
      let gap := statistics.gap.map
        (fun value => s!"\n  Final certified gap: {value}") |>.getD ""
      let converged := statistics.converged.map
        (fun value => s!"\n  Within requested tolerance: {value}") |>.getD ""
      let remaining := statistics.remainingBoxes.map
        (fun value => s!"\n  Remaining boxes: {value}") |>.getD ""
      s!"\n\nOptimization:\n  Configured iteration limit: {statistics.configuredLimit}\n  \
        Tolerance: {statistics.tolerance}{actual}{gap}{converged}{remaining}"

def successReport (report : SolverReport) : String :=
  let plan := report.plan
  let detail := plan.strategyDetail.map (fun value => s!"\n  {value}") |>.getD ""
  let executionNotes :=
    if report.execution.notes.isEmpty then ""
    else "\n" ++ String.intercalate "\n"
      (report.execution.notes.toList.map fun value => s!"  {value}")
  let backend :=
    match renderBackend (effectiveBackend report) with
    | some value => s!"\n\nNumerical computation:\n  {value}"
    | none => ""
  let verification :=
    match renderVerification report with
    | some value => s!"\n\nCertificate verification:\n  {value}"
    | none => ""
  let checker :=
    (report.execution.checker <|> plan.checker).map
      (fun value => s!"\nChecker: {value}") |>.getD ""
  let verifier :=
    (report.execution.verifier <|> plan.verifier).map
      (fun value => s!"\nVerifier: {value}") |>.getD ""
  let optimization := renderOptimization report.execution.optimization
  let advanced :=
    plan.dedicatedProof.map (fun proof =>
      s!"\n\nAdvanced control:\n  {renderProof proof}") |>.getD ""
  s!"LeanCert recognized: {intentLabel plan.intent}\n\n\
    Selected strategy:\n  {plan.strategy}{detail}{executionNotes}{backend}{verification}\
    {checker}{verifier}{optimization}\n\nSuggested proof:\n  {renderProof plan.primaryProof}\
    {advanced}{renderChildren report.execution.children}"

end LeanCert.Tactic.Diagnostic
