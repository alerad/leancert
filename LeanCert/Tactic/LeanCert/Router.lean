/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Tactic.LeanCert.Config
import LeanCert.Tactic.LeanCert.Bridge.ReifiedFunction
import LeanCert.Tactic.LeanCert.Diagnostic.Render
import LeanCert.Tactic.LeanCert.Integral
import LeanCert.Tactic.LeanCert.Semantic.Parse
import LeanCert.Tactic.LeanCert.Semantic.Prepare
import LeanCert.Tactic.LeanCert.Solver.Protocol
import LeanCert.Tactic.Discovery
import LeanCert.Tactic.FinSumExpand
import LeanCert.Engine.Search.CounterExample

/-!
# Semantic LeanCert Router

`leancert` classifies the mathematical shape of the goal and runs a small,
deterministic portfolio through isolated, validated proof artifacts. It is a
semantic front door, not a new numerical engine.
-/

open Lean Meta Elab Tactic

namespace LeanCert.Tactic

open LeanCert.Tactic.Discovery
open LeanCert.Tactic.Semantic
open LeanCert.Tactic.Solver
open LeanCert.Engine.Optimization
open LeanCert.Engine.Search

initialize registerTraceClass `LeanCert.router

private structure SolverSpec where
  report : SolverPlan
  solve : TacticM Unit
  /-- Migrated cores can return execution facts. Legacy cores leave this empty
  and are reported as policy/unknown rather than fabricating telemetry. -/
  solveReported : Option (TacticM SolverExecution) := none
  /-- Recursive routes can return a typed public failure without converting it
  into an implementation exception inside speculative execution. -/
  solveReportedResult :
    Option (TacticM (Except Diagnostic.RouterFailure SolverExecution)) := none
  cost : Nat := 1
  /-- Comparisons accepted by this solver. `none` means the solver accepts the
  full comparison language for its intent. -/
  comparisons : Option (Array Semantic.Comparison) := none

private def suggestion (tactic : String) (args : Array String := #[])
    (acceptsInlineTrust : Bool := true) : ProofSuggestion :=
  { tactic, positionalArgs := args, acceptsInlineTrust }

private def primarySuggestion (cfg : LeanCertConfig)
    (mode : VerificationMode) : ProofSuggestion := Id.run do
  let mut namedArgs : Array (String × String) := #[]
  if cfg.budget != 6 then namedArgs := namedArgs.push ("budget", toString cfg.budget)
  if cfg.taylorDepth != 10 then
    namedArgs := namedArgs.push ("taylorDepth", toString cfg.taylorDepth)
  if cfg.subdivisions != 4 then
    namedArgs := namedArgs.push ("subdivisions", toString cfg.subdivisions)
  if cfg.maxIterations != 1000 then
    namedArgs := namedArgs.push ("maxIterations", toString cfg.maxIterations)
  return {
    tactic := "leancert"
    namedArgs
    trust := if cfg.trust.isSome || mode != .native then some mode else none
  }

private def report (intent : GoalIntent) (strategy : String)
    (cfg : LeanCertConfig) (mode : VerificationMode)
    (backend : BackendReport := .unknown)
    (dedicatedProof : Option ProofSuggestion := none)
    (strategyDetail : Option String := none)
    (strategyKind : StrategyKind := .legacy) : SolverPlan :=
  let dedicatedProof := dedicatedProof.map fun proof =>
    if proof.tactic == "norm_num" || proof.tactic == "integral_exact" then proof
    else {
      proof with
      trust := if cfg.trust.isSome || mode != .native then some mode else none
    }
  {
    intent
    solver := `LeanCert.Tactic.leancert
    strategyKind
    strategy
    strategyDetail
    cost := 1
    primaryProof := primarySuggestion cfg mode
    dedicatedProof
    backend
    verificationRequested := mode
  }

private def numSyntax (n : Nat) : TSyntax `num :=
  ⟨Syntax.mkNumLit (toString n)⟩

private def subdivisionAttempt (cfg : LeanCertConfig) : TacticM Unit := do
  let depth := numSyntax cfg.taylorDepth
  let subdivisions := numSyntax cfg.subdivisions
  evalTactic (← `(tactic| interval_bound_subdiv $depth:num $subdivisions:num))

private def subdivisionAttemptReported (cfg : LeanCertConfig) :
    TacticM SolverExecution := do
  let outcome ← Auto.intervalBoundSubdivWithDepthReported
    (some cfg.taylorDepth) cfg.subdivisions
  return {
    backend := .used .rationalInterval
    verificationUsage :=
      Solver.VerificationUsage.ofEvents outcome.execution.verification
    checker := some outcome.checker
    verifier := some outcome.verifier
    notes := #[
      s!"deepest recursive depth used: {outcome.execution.deepestDepthUsed}",
      s!"certified leaves: {outcome.execution.leafChecks}"
    ]
  }

private def pointAttempt (depth : Nat) : TacticM Unit := do
  let depth := numSyntax depth
  evalTactic (← `(tactic| interval_auto $depth:num))

private def pointAttemptReported (depth : Nat) : TacticM SolverExecution := do
  Auto.intervalNormCore
  let goal ← getMainGoal
  let goalType ← goal.getType
  let outcome ← Auto.proveClosedExpressionBoundReported goal goalType depth
  let mut notes := #[s!"Taylor depth: {outcome.taylorDepth}"]
  if let some precision := outcome.precision then
    notes := notes.push s!"precision: {precision}"
  return {
    backend := .used <|
      if outcome.dyadic then .dyadicInterval else .rationalInterval
    verificationUsage :=
      Solver.VerificationUsage.ofEvents outcome.verification
    checker := some outcome.checker
    verifier := some outcome.verifier
    notes
  }

private def directBoundAttemptReported (depth : Nat) : TacticM SolverExecution := do
  let outcome ← Auto.intervalBoundCoreReported depth
  let mut notes := #[s!"Taylor depth: {outcome.taylorDepth}"]
  if let some precision := outcome.precision then
    notes := notes.push s!"precision: {precision}"
  return {
    backend := .used <|
      if outcome.dyadic then .dyadicInterval else .rationalInterval
    verificationUsage :=
      Solver.VerificationUsage.ofEvents outcome.verification
    checker := outcome.checker
    verifier := outcome.verifier
    notes
  }

private def finSumAttemptReported (precision : Int) (depth : Nat) :
    TacticM SolverExecution := do
  let outcome ← finSumBoundCoreReported precision depth
  let notes := #[
    s!"precision: {outcome.precision}",
    s!"Taylor depth: {outcome.taylorDepth}"
  ]
  let notes :=
    match outcome.termCount with
    | some count => notes.push s!"terms: {count}"
    | none => notes
  return {
    backend := .used .dyadicInterval
    verificationUsage :=
      Solver.VerificationUsage.ofEvents outcome.verification
    checker := some outcome.checker
    verifier := some outcome.verifier
    notes
  }

private def integralExecution (backend : BackendReport)
    (outcomes : Array IntegralOutcome) : SolverExecution := Id.run do
  let mut usage : Solver.VerificationUsage := {}
  let mut notes : Array String := #[]
  for outcome in outcomes do
    if let some verification := outcome.verification then
      usage := usage.combine (Solver.VerificationUsage.ofEvents verification)
    if let some start := outcome.partitionStart then
      notes := notes.push s!"partition search starts at {start}"
    if let some maximum := outcome.partitionMaximum then
      notes := notes.push s!"partition search maximum {maximum}"
  let checker := outcomes[0]?.map (·.checker)
  let verifier := outcomes[0]?.map (·.verifier)
  return { backend, verificationUsage := usage, checker, verifier, notes }

private def checkedExecution (backend : BackendReport)
    (verification : LeanCert.Tactic.VerificationUsage)
    (checker verifier : Name) (notes : Array String := #[]) : SolverExecution := {
  backend
  verificationUsage := Solver.VerificationUsage.ofEvents verification
  checker := some checker
  verifier := some verifier
  notes
}

private def rootExistsAttemptReported (depth : Nat) : TacticM SolverExecution := do
  let outcome ← intervalRootsCoreReported depth
  return checkedExecution (.policy "checked root certificate arithmetic")
    outcome.verification outcome.checker outcome.verifier
    #[s!"Taylor depth: {outcome.taylorDepth}"]

private unsafe def uniqueRootAttemptReported (depth : Nat) :
    TacticM SolverExecution := do
  let outcome ← intervalUniqueRootCoreReported depth
  return checkedExecution (.policy "checked Newton certificate arithmetic")
    outcome.verification outcome.checker outcome.verifier
    #[s!"Taylor depth: {outcome.taylorDepth}"]

private def noRootAttemptReported (depth : Nat) : TacticM SolverExecution := do
  let outcome ← Auto.rootBoundCoreReported depth
  return checkedExecution (.policy "checked no-root certificate arithmetic")
    outcome.verification outcome.checker outcome.verifier
    #[s!"Taylor depth: {outcome.taylorDepth}"]

private def optimizationAttemptReported (maxIterations : Nat)
    (useMonotonicity : Bool) (depth : Nat) : TacticM SolverExecution := do
  let outcome ← Auto.optBoundCoreReported maxIterations useMonotonicity depth
  return checkedExecution
    (.policy "legacy checked global-optimization certificate")
    outcome.verification outcome.checker outcome.verifier #[
      s!"maximum iterations: {outcome.maxIterations}",
      s!"Taylor depth: {outcome.taylorDepth}",
      s!"monotonicity pruning: {outcome.useMonotonicity}"
    ]

private def multivariateAttemptReported (maxIterations : Nat)
    (tolerance : ℚ) (useMonotonicity : Bool) (depth : Nat) :
    TacticM SolverExecution := do
  let outcome ← Auto.multivariateBoundCoreReported maxIterations tolerance
    useMonotonicity depth
  return checkedExecution
    (.policy "legacy checked global-optimization certificate")
    outcome.verification outcome.checker outcome.verifier #[
      s!"maximum iterations: {outcome.maxIterations}",
      s!"tolerance: {outcome.tolerance}",
      s!"Taylor depth: {outcome.taylorDepth}",
      s!"monotonicity pruning: {outcome.useMonotonicity}"
    ]

/-- The deterministic strategy portfolio for a recognized goal intent. -/
private unsafe def portfolio (intent : GoalIntent) (cfg : LeanCertConfig)
    (mode : VerificationMode) : Array SolverSpec :=
  let d := cfg.taylorDepth
  let d2 := d + 10
  let d3 := d + 20
  match intent with
  | .pointInequality => #[
      { report := report intent "exact normalization" cfg mode .notApplicable
          (some (suggestion "norm_num")),
        solve := do evalTactic (← `(tactic| norm_num)) },
      { report := report intent s!"direct point enclosure (Taylor depth {d})" cfg mode
          (.policy "checked interval tactic portfolio")
          (some (suggestion "interval_auto" #[toString d])),
        solve := pointAttempt d
        solveReported := some (pointAttemptReported d) },
      { report := report intent s!"direct point enclosure (Taylor depth {d2})" cfg mode
          (.policy "checked interval tactic portfolio")
          (some (suggestion "interval_auto" #[toString d2])),
        solve := pointAttempt d2
        solveReported := some (pointAttemptReported d2) }]
  | .intervalBound => #[
      { report := report intent s!"direct interval enclosure (Taylor depth {d})" cfg mode
          (.policy "Dyadic-first, then checked Rational fallback")
          (some (suggestion "certify_bound" #[toString d])),
        solve := Auto.intervalBoundCore d
        solveReported := some (directBoundAttemptReported d) },
      { report := report intent s!"direct interval enclosure (Taylor depth {d2})" cfg mode
          (.policy "Dyadic-first, then checked Rational fallback")
          (some (suggestion "certify_bound" #[toString d2])),
        solve := Auto.intervalBoundCore d2
        solveReported := some (directBoundAttemptReported d2) },
      { report := report intent "recursive interval subdivision" cfg mode
          (.used .rationalInterval)
          (some (suggestion "interval_bound_subdiv"
            #[toString d, toString cfg.subdivisions]))
          (some s!"Taylor depth {d}; maximum recursive depth {cfg.subdivisions}")
          .subdivision,
        solve := subdivisionAttempt cfg
        solveReported := some (subdivisionAttemptReported cfg) },
      { report := report intent
          (if cfg.useMonotonicity then s!"opt_bound {cfg.maxIterations} mono"
           else s!"opt_bound {cfg.maxIterations}") cfg mode
          (.policy "legacy checked global-optimization certificate")
          (if cfg.taylorDepth == 10 then
            some (suggestion "opt_bound"
              (if cfg.useMonotonicity then #[toString cfg.maxIterations, "mono"]
               else #[toString cfg.maxIterations]))
           else none)
          (strategyKind := .globalOptimization),
        solve := Auto.optBoundCore cfg.maxIterations cfg.useMonotonicity d
        solveReported := some
          (optimizationAttemptReported cfg.maxIterations cfg.useMonotonicity d)
        cost := 3 }]
  | .multivariateBound => #[
      { report := report intent s!"multivariate_bound {cfg.maxIterations}"
          cfg mode (.policy "legacy checked global-optimization certificate")
          (if !cfg.useMonotonicity && d == 10 then
            some (suggestion "multivariate_bound" #[toString cfg.maxIterations])
           else none)
          (strategyKind := .globalOptimization),
        solve := Auto.multivariateBoundCore cfg.maxIterations (1 / 1000)
          cfg.useMonotonicity d
        solveReported := some <|
          multivariateAttemptReported cfg.maxIterations (1 / 1000)
            cfg.useMonotonicity d
        cost := 3 },
      { report := report intent s!"multivariate_bound {2 * cfg.maxIterations}"
          cfg mode (.policy "legacy checked global-optimization certificate")
          none (strategyKind := .globalOptimization),
        solve := Auto.multivariateBoundCore (2 * cfg.maxIterations) (1 / 10000)
          cfg.useMonotonicity d2
        solveReported := some <|
          multivariateAttemptReported (2 * cfg.maxIterations) (1 / 10000)
            cfg.useMonotonicity d2
        cost := 4 }]
  | .rootExists => #[
      { report := report intent "endpoint sign-change certificate" cfg mode
          (.policy "checked root certificate arithmetic")
          (some (suggestion "interval_roots" #[toString d])),
        solve := intervalRootsCore d
        solveReported := some (rootExistsAttemptReported d) },
      { report := report intent "endpoint sign-change certificate" cfg mode
          (.policy "checked root certificate arithmetic")
          (some (suggestion "interval_roots" #[toString d2])),
        solve := intervalRootsCore d2
        solveReported := some (rootExistsAttemptReported d2) },
      { report := report intent "endpoint sign-change certificate" cfg mode
          (.policy "checked root certificate arithmetic")
          (some (suggestion "interval_roots" #[toString d3])),
        solve := intervalRootsCore d3
        solveReported := some (rootExistsAttemptReported d3) }]
  | .uniqueRoot => #[
      { report := report intent "interval Newton contraction" cfg mode
          (.policy "checked Newton certificate arithmetic")
          (some (suggestion "interval_unique_root" #[toString d])),
        solve := intervalUniqueRootCore d
        solveReported := some (uniqueRootAttemptReported d) },
      { report := report intent "interval Newton contraction" cfg mode
          (.policy "checked Newton certificate arithmetic")
          (some (suggestion "interval_unique_root" #[toString d2])),
        solve := intervalUniqueRootCore d2
        solveReported := some (uniqueRootAttemptReported d2) },
      { report := report intent "interval Newton contraction" cfg mode
          (.policy "checked Newton certificate arithmetic")
          (some (suggestion "interval_unique_root" #[toString d3])),
        solve := intervalUniqueRootCore d3
        solveReported := some (uniqueRootAttemptReported d3) }]
  | .noRoot => #[
      { report := report intent "zero-exclusion enclosure" cfg mode
          (.policy "checked interval tactic portfolio")
          (some (suggestion "root_bound" #[toString d])),
        solve := Auto.rootBoundCore d
        solveReported := some (noRootAttemptReported d) },
      { report := report intent "zero-exclusion enclosure" cfg mode
          (.policy "checked interval tactic portfolio")
          (some (suggestion "root_bound" #[toString d2])),
        solve := Auto.rootBoundCore d2
        solveReported := some (noRootAttemptReported d2) },
      { report := report intent "zero-exclusion enclosure" cfg mode
          (.policy "checked interval tactic portfolio")
          (some (suggestion "root_bound" #[toString d3])),
        solve := Auto.rootBoundCore d3
        solveReported := some (noRootAttemptReported d3) }]
  | .existentialMinimum => #[
      { report := report intent "guided lower-bound discovery and certification" cfg mode
          (.policy "legacy optimization followed by checked interval certification")
          (some (suggestion "interval_minimize" #[toString d])), solve := intervalMinimizeCore d },
      { report := report intent "multivariate lower-bound discovery and certification" cfg mode
          (.policy "legacy optimization followed by checked certification")
          (some (suggestion "interval_minimize_mv" #[toString d])), solve := intervalMinimizeMvCore d },
      { report := report intent "guided lower-bound discovery and certification" cfg mode
          (.policy "legacy optimization followed by checked interval certification")
          (some (suggestion "interval_minimize" #[toString d2])), solve := intervalMinimizeCore d2 }]
  | .existentialMaximum => #[
      { report := report intent "guided upper-bound discovery and certification" cfg mode
          (.policy "legacy optimization followed by checked interval certification")
          (some (suggestion "interval_maximize" #[toString d])), solve := intervalMaximizeCore d },
      { report := report intent "multivariate upper-bound discovery and certification" cfg mode
          (.policy "legacy optimization followed by checked certification")
          (some (suggestion "interval_maximize_mv" #[toString d])), solve := intervalMaximizeMvCore d },
      { report := report intent "guided upper-bound discovery and certification" cfg mode
          (.policy "legacy optimization followed by checked interval certification")
          (some (suggestion "interval_maximize" #[toString d2])), solve := intervalMaximizeCore d2 }]
  | .argmin => #[
      { report := report intent "attained minimum certification" cfg mode
          (.policy "candidate search followed by checked bounds")
          (some (suggestion "interval_argmin" #[toString d])), solve := intervalArgminCore d },
      { report := report intent "attained minimum certification" cfg mode
          (.policy "candidate search followed by checked bounds")
          (some (suggestion "interval_argmin" #[toString d2])), solve := intervalArgminCore d2 }]
  | .argmax => #[
      { report := report intent "attained maximum certification" cfg mode
          (.policy "candidate search followed by checked bounds")
          (some (suggestion "interval_argmax" #[toString d])), solve := intervalArgmaxCore d },
      { report := report intent "attained maximum certification" cfg mode
          (.policy "candidate search followed by checked bounds")
          (some (suggestion "interval_argmax" #[toString d2])), solve := intervalArgmaxCore d2 }]
  | .finiteSum => #[
      { report := report intent "reflective finite-sum certificate" cfg mode
          (.used .dyadicInterval) (some (suggestion "finsum_bound")),
        solve := finSumBoundCore (-53) 10
        solveReported := some (finSumAttemptReported (-53) 10) },
      { report := report intent "reflective finite-sum certificate" cfg mode
          (.used .dyadicInterval) (some (suggestion "finsum_bound" #["80"])),
        solve := finSumBoundCore (-80) 10
        solveReported := some (finSumAttemptReported (-80) 10) }]
  | .certificateCheck => #[
      { report := report intent "closed Boolean certificate verification" cfg mode
          .notApplicable,
        solve := do
          discard <| LeanCert.Tactic.closeCertificateGoal
            (← LeanCert.Tactic.VerificationConfig.current) (← getMainGoal)
            (tacticName := "leancert"),
        solveReported := some do
          let event ← LeanCert.Tactic.closeCertificateGoalReported
            (← LeanCert.Tactic.VerificationConfig.current) (← getMainGoal)
            (tacticName := "leancert")
          return {
            verificationUsage :=
              Solver.VerificationUsage.ofEvents event.toUsage
          }
        cost := 0 }]
  | .integralBound => #[
      { report := report intent "integral_exact" cfg mode (.used .exactRational)
          (some (suggestion "integral_exact")) (strategyKind := .exactIntegral),
        solve := integralExactCore
        solveReported := some do
          return integralExecution (.used .exactRational)
            (← integralExactCoreReported)
        cost := 0 },
      { report := report intent "integral_search 16 512" cfg mode
          (.used .checkedRationalPartitions) (strategyKind := .partitionIntegral),
        solve := integralSearchCore 16 512
        solveReported := some do
          return integralExecution (.used .checkedRationalPartitions)
            (← integralSearchCoreReported 16 512) },
      { report := report intent "integral_search 16 4096" cfg mode
          (.used .checkedRationalPartitions) (strategyKind := .partitionIntegral),
        solve := integralSearchCore 16 4096
        solveReported := some do
          return integralExecution (.used .checkedRationalPartitions)
            (← integralSearchCoreReported 16 4096) },
      { report := report intent "integral_search 16 16384" cfg mode
          (.used .checkedRationalPartitions) (strategyKind := .partitionIntegral),
        solve := integralSearchCore 16 16384
        solveReported := some do
          return integralExecution (.used .checkedRationalPartitions)
            (← integralSearchCoreReported 16 16384) }]
  | .conjunction => #[]

private def Semantic.SemanticGoal.comparison? :
    Semantic.SemanticGoal → Option Semantic.Comparison
  | .point spec => some spec.comparison
  | .bound spec => some spec.comparison
  | .integral spec => some spec.comparison
  | .finiteSum spec => some spec.comparison
  | _ => none

private def SolverSpec.isApplicableTo
    (spec : SolverSpec) (goal : Semantic.SemanticGoal) : Bool :=
  match spec.comparisons, goal.comparison? with
  | some accepted, some comparison => accepted.contains comparison
  | some _, none => false
  | none, _ => true

private def outcomeSummary (outcome : AttemptOutcome) : String :=
  Diagnostic.attemptOutcome outcome

private def throwRouterFailure {α : Type}
    (verbosity : Diagnostic.DiagnosticVerbosity)
    (failure : Diagnostic.RouterFailure) : TacticM α :=
  throwError "{Diagnostic.routerFailure verbosity failure}"

private def trySolver (spec : SolverSpec) : TacticM AttemptOutcome := do
  let goal ← getMainGoal
  let proposition ← goal.getType
  match spec.solveReportedResult, spec.solveReported with
  | some solve, _ =>
      Solver.proveWithTacticReportedResult { spec.report with cost := spec.cost }
        proposition solve
  | none, some solve =>
      Solver.proveWithTacticReported { spec.report with cost := spec.cost }
        proposition solve
  | none, none =>
      Solver.proveWithTactic { spec.report with cost := spec.cost } proposition spec.solve

private partial def normalizedBoundProposition (spec : Semantic.BoundSpec) :
    MetaM Lean.Expr := do
  let rec visit (index : Nat) (arguments : Array Lean.Expr) : MetaM Lean.Expr := do
    if h : index < spec.boundVars.size then
      let boundVar := spec.boundVars[index]
      withLocalDeclD boundVar.userName boundVar.type fun x => do
        let conclusion ← visit (index + 1) (arguments.push x)
        let membership ← mkAppM ``Membership.mem #[boundVar.domain.original, x]
        let implication ← mkArrow membership conclusion
        mkForallFVars #[x] implication
    else
      let lhs := (mkAppN spec.lhs arguments).headBeta
      let rhs := (mkAppN spec.rhs arguments).headBeta
      match spec.comparison with
      | .le => mkAppM ``LE.le #[lhs, rhs]
      | .lt => mkAppM ``LT.lt #[lhs, rhs]
      | _ => pure spec.original
  visit 0 #[]

private def canonicalRootProposition (spec : Semantic.RootSpec) : MetaM Lean.Expr := do
  withLocalDeclD spec.boundVar.userName spec.boundVar.type fun x => do
    let membership ← mkAppM ``Membership.mem #[spec.boundVar.domain.original, x]
    let value := (mkApp spec.function x).headBeta
    let zero ← mkAppOptM ``OfNat.ofNat
      #[some spec.boundVar.type, some (mkRawNatLit 0), none]
    let equation ← mkAppM ``Eq #[value, zero]
    let predicate ← mkAppM ``And #[membership, equation]
    let predicate ← mkLambdaFVars #[x] predicate
    match spec.kind with
    | .exists => mkAppM ``Exists #[predicate]
    | .unique => mkAppM ``ExistsUnique #[predicate]
    | .excluded => pure spec.original

private def canonicalExtremumProposition (spec : Semantic.ExtremumSpec) :
    MetaM Lean.Expr := do
  withLocalDeclD spec.boundVar.userName spec.boundVar.type fun x => do
    let xMembership ← mkAppM ``Membership.mem #[spec.boundVar.domain.original, x]
    let extremalBody ← withLocalDeclD `y spec.boundVar.type fun y => do
      let yMembership ← mkAppM ``Membership.mem #[spec.boundVar.domain.original, y]
      let xValue := (mkApp spec.function x).headBeta
      let yValue := (mkApp spec.function y).headBeta
      let comparison ←
        if spec.kind == .minimum then mkAppM ``LE.le #[xValue, yValue]
        else mkAppM ``LE.le #[yValue, xValue]
      let implication ← mkArrow yMembership comparison
      mkForallFVars #[y] implication
    let predicate ← mkAppM ``And #[xMembership, extremalBody]
    mkAppM ``Exists #[← mkLambdaFVars #[x] predicate]

/-- Adapt a legacy numerical engine to the comparison normalized by the
semantic parser. The numerical engine sees `lhs - rhs ⋚ 0`; the resulting proof
is transported back with the ordinary ordered-ring equivalence. -/
private def trySolverFor (spec : SolverSpec) (semantic : Semantic.SemanticGoal) :
    TacticM AttemptOutcome := do
  let runSpec : TacticM SolverExecution :=
    match spec.solveReported with
    | some solve => solve
    | none => do
        spec.solve
        return {}
  let action ←
    match semantic with
    | .bound boundSpec =>
        if boundSpec.normalizedDifference then
          let normalized ← normalizedBoundProposition boundSpec
          let normalizedSyntax ← Term.exprToSyntax normalized
          pure do
            if boundSpec.comparison == .lt then
              evalTactic (← `(tactic|
                suffices hnormalized : $normalizedSyntax by
                  simpa only [sub_neg] using hnormalized))
            else
              evalTactic (← `(tactic|
                suffices hnormalized : $normalizedSyntax by
                  simpa only [sub_nonpos] using hnormalized))
            runSpec
        else
          pure runSpec
    | .root rootSpec =>
        if rootSpec.kind == .excluded then
          pure runSpec
        else
          let canonical ← canonicalRootProposition rootSpec
          let canonicalSyntax ← Term.exprToSyntax canonical
          pure do
            if rootSpec.equationReversed then
              evalTactic (← `(tactic|
                suffices hnormalized : $canonicalSyntax by
                  simpa only [and_comm, eq_comm] using hnormalized))
            else
              evalTactic (← `(tactic|
                suffices hnormalized : $canonicalSyntax by
                  simpa only [and_comm, sub_eq_zero] using hnormalized))
            runSpec
    | _ => pure runSpec
  let goal ← getMainGoal
  let proposition ← goal.getType
  Solver.proveWithTacticReported { spec.report with cost := spec.cost }
    proposition action

/-- Temporary adapter for the existing numerical engines. The production
router speaks only the typed `SemanticSolver` protocol; individual engines can
then migrate from this adapter to consuming prepared payloads directly. -/
private def SolverSpec.toSemanticSolver (spec : SolverSpec) : SemanticSolver := {
  plan := { spec.report with cost := spec.cost }
  supports := spec.isApplicableTo
  attempt := fun prepared _ => trySolverFor spec prepared.semantic
}

private def commitArtifact (artifact : ProofArtifact) : TacticM SolverReport := do
  let goal ← getMainGoal
  goal.assign artifact.proof
  replaceMainGoal []
  return artifact.report

private def rejectUnsupportedPreparedFunctions (prepared : Semantic.PreparedGoal)
    (verbosity : Diagnostic.DiagnosticVerbosity) : TacticM Unit := do
  for function in prepared.functions do
    match function with
    | .ready .. => pure ()
    | .deferred source detail =>
        trace[LeanCert.router] "proof-carrying bridge preparation deferred for \
          {source}:\n{detail}"
    | .unsupported source detail =>
        trace[LeanCert.router] "reification preparation failed for {source}:\n{detail}"
        throwRouterFailure verbosity <|
          Diagnostic.RouterFailure.unsupportedExpression (toString source)
          s!"LeanCert already unfolded reducible user definitions.\n{detail}"

private def preparedReified? (prepared : Semantic.PreparedGoal) (source : Lean.Expr) :
    MetaM (Option Bridge.ReifiedFunction) := do
  for function in prepared.functions do
    match function with
    | .ready candidate reified _ =>
        if ← isDefEq candidate source then return some reified
    | .unsupported .. | .deferred .. => pure ()
  return none

/-- Search for a checked rational witness after a unary bound portfolio fails.

This is diagnostic evidence, not a proof attempt: the original goal state is
never changed.  Comparison normalization lets this handle upper and lower
bounds while preserving the function's original syntax for reification. -/
private unsafe def certifiedBoundRefutation?
    (semantic : Semantic.SemanticGoal)
    (prepared : Semantic.PreparedGoal)
    (cfg : LeanCertConfig) : TacticM (Option Diagnostic.RefutationEvidence) := do
  let .bound spec := semantic
    | return none
  if spec.boundVars.size != 1 || cfg.budget == 0 then
    return none
  let some domain := prepared.domains[0]?
    | return none
  let .closedRat _ interval _ := domain
    | return none
  if spec.comparison != .le && spec.comparison != .lt then
    return none
  try
    let intervalValue ← unsafe evalExpr LeanCert.Core.IntervalRat
      (mkConst ``LeanCert.Core.IntervalRat) interval
    let searchCfg : GlobalOptConfig := {
      maxIterations := cfg.maxIterations
      taylorDepth := cfg.taylorDepth + 10
      tolerance := 1 / 10000
    }
    let result ← withLocalDeclD `x (mkConst ``Real) fun x => do
      let lhsBody := (mkApp spec.lhs x).headBeta
      let rhsBody := (mkApp spec.rhs x).headBeta
      let lhsUses := lhsBody.containsFVar x.fvarId!
      let rhsUses := rhsBody.containsFVar x.fvarId!
      if lhsUses == rhsUses then
        return (.ok none)
      let functionBody := if lhsUses then lhsBody else rhsBody
      let boundBody := if lhsUses then rhsBody else lhsBody
      let some limit ← extractRatFromReal boundBody
        | return (.ok none)
      let functionSource := if lhsUses then spec.lhs else spec.rhs
      let reflected ←
        match ← preparedReified? prepared functionSource with
        | some reflected => pure reflected
        | none =>
            let function ← mkLambdaFVars #[x] functionBody
            Bridge.reifyFunction function
      let ast ← unsafe evalExpr LeanCert.Core.Expr
        (mkConst ``LeanCert.Core.Expr) reflected.ast
      if spec.comparison == .le then
        if lhsUses then
          match findViolation ast [intervalValue] limit searchCfg with
          | .ok result => return .ok result
          | .error _ => return findViolationDiv ast [intervalValue] limit searchCfg
        else
          match findViolationLower ast [intervalValue] limit searchCfg with
          | .ok result => return .ok result
          | .error _ => return findViolationLowerDiv ast [intervalValue] limit searchCfg
      else if lhsUses then
        return findViolationStrict ast [intervalValue] limit searchCfg
      else
        return findViolationStrictLower ast [intervalValue] limit searchCfg
    match result with
    | .error error =>
        trace[LeanCert.router] "counterexample search failed: {repr error}"
        return none
    | .ok none =>
        trace[LeanCert.router] "counterexample search found no certified witness"
        return none
    | .ok (some counterexample) =>
        let point := (counterexample.point.map fun value =>
          s!"{value} (≈ {Diagnostic.formatRatApprox value})")
          |>.intersperse ", " |> String.join
        return some {
          witness := s!"({point})"
          detail := some s!"At this point, the checked function value is approximately \
            enclosed by [{Diagnostic.formatRatApprox counterexample.valueLo}, \
            {Diagnostic.formatRatApprox counterexample.valueHi}], which violates \
            the requested comparison. The certificate uses exact rational endpoints."
        }
  catch exception =>
    trace[LeanCert.router] "counterexample preparation failed: \
      {← exception.toMessageData.toString}"
    return none

/-- Select the numerical portfolio associated with a parsed semantic atom. -/
private def intentOfSemanticGoal (goal : Semantic.SemanticGoal) : MetaM (Option GoalIntent) := do
  match goal with
  | .point _ => return some .pointInequality
  | .integral _ => return some .integralBound
  | .finiteSum _ => return some .finiteSum
  | .certificateCheck .. => return some .certificateCheck
  | .allOf .. => return some .conjunction
  | .bound spec =>
      return some (if spec.boundVars.size > 1 then .multivariateBound else .intervalBound)
  | .root spec =>
      return some <| match spec.kind with
        | .exists => .rootExists
        | .unique => .uniqueRoot
        | .excluded => .noRoot
  | .extremum spec =>
      return some (if spec.kind == .minimum then .argmin else .argmax)
  | .discovery spec =>
      return some (if spec.kind == .minimum then .existentialMinimum
        else .existentialMaximum)

/-- Classify and solve the main goal.  On success, return the exact strategy report. -/
unsafe def runLeanCert (cfg : LeanCertConfig)
    (verbosity : Diagnostic.DiagnosticVerbosity := .compact) : TacticM SolverReport := do
  let verificationMode := (← VerificationConfig.current).mode
  let goal ← getMainGoal
  let goalType ← instantiateMVars (← goal.getType)
  let semanticResult ← goal.withContext do Semantic.parseGoal goalType
  let normalizationIntent ← (match semanticResult with
    | .ok semantic => do
        pure ((← intentOfSemanticGoal semantic).getD .certificateCheck)
    | .error _ => pure .certificateCheck : TacticM GoalIntent)
  let normalizationReport := report normalizationIntent "exact normalization"
    cfg verificationMode .notApplicable (some (suggestion "norm_num"))
  let normalizationSpec : SolverSpec := {
    report := normalizationReport
    cost := 0
    solve := do evalTactic (← `(tactic| norm_num))
  }
  match ← trySolver normalizationSpec with
  | .proved artifact => return ← commitArtifact artifact
  | _ => pure ()
  let (semantic, prepared) ← goal.withContext do
    let semantic ←
      match semanticResult with
      | .ok semantic => pure semantic
      | .error failure =>
          throwRouterFailure verbosity <| Diagnostic.RouterFailure.unsupportedGoal
            (toString goalType) failure.detail
    let prepared ←
      match ← Semantic.prepareGoal semantic with
      | .ok prepared => pure prepared
      | .error failure =>
          throwError "leancert: internal preparation failure.\n\nGoal:\n{goalType}\n\n\
            {failure.detail}\n\nThis is a LeanCert bug: semantic normalization failed \
            before any numerical strategy ran."
    return (semantic, prepared)

  if let .allOf _ _ := semantic then
    let conjunctionSpec : SolverSpec := {
      report := report .conjunction "recursive semantic routing"
        cfg verificationMode .notApplicable
      cost := 0
      solve := do
        evalTactic (← `(tactic| try simp only [forall_and]))
        evalTactic (← `(tactic| constructor))
        while !(← getGoals).isEmpty do
          discard <| runLeanCert cfg verbosity
      solveReportedResult := some do
        evalTactic (← `(tactic| try simp only [forall_and]))
        evalTactic (← `(tactic| constructor))
        let childGoals ← getGoals
        let mut children : Array ChildReport := #[]
        let mut usage : Solver.VerificationUsage := {}
        for (childGoal, index) in childGoals.zipIdx do
          setGoals [childGoal]
          let childIntent? ← childGoal.withContext do
            let childType ← instantiateMVars (← childGoal.getType)
            match ← Semantic.parseGoal childType with
            | .ok childSemantic => return ← intentOfSemanticGoal childSemantic
            | .error _ => return none
          let child ←
            try
              runLeanCert cfg verbosity
            catch exception =>
              let detail ← exception.toMessageData.toString
              return .error <| Diagnostic.RouterFailure.childFailure
                (index + 1) childGoals.length childIntent? detail
          let backend :=
            match child.execution.backend with
            | .unknown => child.plan.backend
            | observed => observed
          children := children.push {
            intent := child.plan.intent
            strategy := child.plan.strategy
            backend
            verificationUsage := child.execution.verificationUsage
          }
          usage := usage.combine child.execution.verificationUsage
        setGoals []
        return .ok { children, verificationUsage := usage }
    }
    match ← trySolver conjunctionSpec
    with
    | .proved artifact => return ← commitArtifact artifact
    | .routerFailure failure =>
        throwRouterFailure verbosity failure
    | outcome =>
        throwRouterFailure verbosity <|
          Diagnostic.RouterFailure.conjunctionFailure (outcomeSummary outcome)

  if let .bound _ := semantic then
    if prepared.domains.any (fun domain => domain.isProvablyEmpty) then
      let vacuitySpec : SolverSpec := {
        report := report .intervalBound "empty-domain normalization"
          cfg verificationMode .notApplicable
        cost := 0
        solve := do evalTactic (← `(tactic| simp [Set.mem_Icc]))
      }
      match ← trySolver vacuitySpec
      with
      | .proved artifact => return ← commitArtifact artifact
      | outcome =>
          throwError "leancert: proved that the quantified domain is empty, but \
            transporting that fact to the theorem failed.\n{outcomeSummary outcome}"
    if prepared.domains.any (fun domain => match domain with
        | .unsupported .. => true
        | _ => false) then
      let details := prepared.domains.toList.filterMap fun domain =>
        match domain with
        | .unsupported source reason =>
            let topology := match source.kind with
              | .open => "open interval `Set.Ioo`"
              | .leftOpen => "left-open interval `Set.Ioc`"
              | .rightOpen => "right-open interval `Set.Ico`"
              | .unorderedClosed => "unordered interval `Set.uIcc`"
              | .closed => "closed interval `Set.Icc`"
              | .intervalRat => "rational interval"
            let explanation := match reason with
              | .topology _ => "this topology has no verifier transport yet"
              | .nonRationalEndpoint which endpoint =>
                  s!"the {which} endpoint is not rational: {endpoint}"
              | .unsupportedCarrier type =>
                  s!"the carrier type is not supported: {type}"
              | .unsupportedSyntax rendered =>
                  s!"the domain syntax is not supported: {rendered}"
            some s!"  • {topology}: {explanation}"
        | _ => none
      throwRouterFailure verbosity <|
        Diagnostic.RouterFailure.unsupportedDomain .intervalBound details.toArray
    if prepared.domains.any (fun domain => match domain with
        | .symbolicClosed .. => true
        | _ => false) then
      throwRouterFailure verbosity <|
        Diagnostic.RouterFailure.unsupportedDomain .intervalBound #[
          "  • at least one endpoint is symbolic; current certificate backends \
            require rational endpoints"
        ]
    rejectUnsupportedPreparedFunctions prepared verbosity

  if let .root spec := semantic then
    if prepared.domains.any (fun domain => domain.isProvablyEmpty) then
      throwError "leancert: recognized a root-existence theorem, but proved that \
        its search domain is empty. No witness can inhabit this interval."
    if prepared.domains.any (fun domain => match domain with
        | .unsupported .. | .symbolicClosed .. => true
        | _ => false) then
      let rootIntent := match spec.kind with
        | .exists => GoalIntent.rootExists
        | .unique => .uniqueRoot
        | .excluded => .noRoot
      throwRouterFailure verbosity <|
        Diagnostic.RouterFailure.unsupportedDomain rootIntent #[
          "  • the root domain cannot be normalized to a supported closed rational interval"
        ]
    rejectUnsupportedPreparedFunctions prepared verbosity
    let mut candidates : Array Lean.Expr := #[]
    if let some loExpr := spec.boundVar.domain.lo then
      if let some hiExpr := spec.boundVar.domain.hi then
        if let some lo ← LeanCert.Meta.Numeral.toRat? loExpr then
          if let some hi ← LeanCert.Meta.Numeral.toRat? hiExpr then
            for index in List.range 17 do
              let candidate := lo + (hi - lo) * index / 16
              let candidateExpr ←
                mkAppOptM ``Rat.cast #[mkConst ``Real, none, toExpr candidate]
              candidates := candidates.push candidateExpr
    if spec.kind == .exists || spec.kind == .unique then
      for candidate in candidates do
        let candidateSyntax ← Term.exprToSyntax candidate
        let exactReport := report
          (if spec.kind == .exists then .rootExists else .uniqueRoot)
          "exact rational root candidate" cfg verificationMode
          (.used .exactRational)
        let exactSpec : SolverSpec := {
          report := exactReport
          cost := 0
          solve := do
            if spec.kind == .exists then
              evalTactic (← `(tactic|
                refine ⟨$candidateSyntax, ?_, ?_⟩ <;>
                  norm_num [Set.mem_Icc]))
            else
              evalTactic (← `(tactic|
                refine ⟨$candidateSyntax,
                  (by constructor <;> norm_num [Set.mem_Icc]), ?_⟩;
                intro y hy;
                rcases hy with ⟨hyMem, hyRoot⟩;
                simp only [Set.mem_Icc] at hyMem;
                norm_num at hyRoot ⊢;
                nlinarith))
        }
        match ← trySolver exactSpec with
        | .proved artifact => return ← commitArtifact artifact
        | _ => pure ()

  if let .extremum spec := semantic then
    if prepared.domains.any (fun domain => domain.isProvablyEmpty) then
      throwError "leancert: recognized an optimizer-existence theorem, but \
        proved that its domain is empty."
    if prepared.domains.any (fun domain => match domain with
        | .unsupported .. | .symbolicClosed .. => true
        | _ => false) then
      throwError "leancert: recognized an optimizer-existence theorem, but its \
        domain cannot be normalized to a supported closed rational interval."
    rejectUnsupportedPreparedFunctions prepared verbosity
    let some lo := spec.boundVar.domain.lo
      | throwError "leancert: optimizer existence requires a closed interval with endpoints"
    let some hi := spec.boundVar.domain.hi
      | throwError "leancert: optimizer existence requires a closed interval with endpoints"
    if spec.existenceOnly then
      let intent := if spec.kind == .minimum then GoalIntent.argmin else GoalIntent.argmax
      let canonical ← canonicalExtremumProposition spec
      let canonicalSyntax ← Term.exprToSyntax canonical
      let evtReport := report intent
        (if spec.kind == .minimum then "compact extreme-value theorem (minimum)"
         else "compact extreme-value theorem (maximum)")
        cfg verificationMode .notApplicable
      let evtSpec : SolverSpec := {
        report := evtReport
        cost := 0
        solve := do
          evalTactic (← `(tactic|
            suffices hnormalized : $canonicalSyntax by
              simpa only [and_comm] using hnormalized))
          let reflected ←
            match ← preparedReified? prepared spec.function with
            | some reflected => pure reflected
            | none => Bridge.reifyFunction spec.function
          let continuity ← LeanCert.Meta.mkContinuousOnProofIcc reflected.ast lo hi
          let evalEqSyntax ← Term.exprToSyntax reflected.evalEq
          let continuitySyntax ← Term.exprToSyntax continuity
          let functionSyntax ← Term.exprToSyntax spec.function
          let loSyntax ← Term.exprToSyntax lo
          let hiSyntax ← Term.exprToSyntax hi
          if spec.kind == .minimum then
            evalTactic (← `(tactic|
              have heval := $evalEqSyntax;
              have hcontEval := $continuitySyntax;
              have hcont : ContinuousOn $functionSyntax (Set.Icc $loSyntax $hiSyntax) :=
                hcontEval.congr (fun x _ => (heval x).symm);
              have hne : (Set.Icc $loSyntax $hiSyntax).Nonempty :=
                Set.nonempty_Icc.mpr (by norm_num);
              obtain ⟨x, hx, hmin⟩ :=
                isCompact_Icc.exists_isMinOn hne hcont;
              refine ⟨x, hx, ?_⟩;
              exact isMinOn_iff.mp hmin))
          else
            evalTactic (← `(tactic|
              have heval := $evalEqSyntax;
              have hcontEval := $continuitySyntax;
              have hcont : ContinuousOn $functionSyntax (Set.Icc $loSyntax $hiSyntax) :=
                hcontEval.congr (fun x _ => (heval x).symm);
              have hne : (Set.Icc $loSyntax $hiSyntax).Nonempty :=
                Set.nonempty_Icc.mpr (by norm_num);
              obtain ⟨x, hx, hmax⟩ :=
                isCompact_Icc.exists_isMaxOn hne hcont;
              refine ⟨x, hx, ?_⟩;
              exact isMaxOn_iff.mp hmax))
      }
      match ← trySolver evtSpec with
      | .proved artifact => return ← commitArtifact artifact
      | outcome =>
          trace[LeanCert.router] "compact extreme-value theorem unavailable: \
            {outcomeSummary outcome}"

  if let .finiteSum spec := semantic then
    if spec.comparison == .eq then
      let equalityReport := report .finiteSum "exact finite-sum expansion"
        cfg verificationMode (.used .exactRational)
        (some (suggestion "finsum_expand"))
      let equalitySpec : SolverSpec := {
        report := equalityReport
        cost := 0
        solve := do evalTactic (← `(tactic| finsum_expand; norm_num))
      }
      match ← trySolver equalitySpec with
      | .proved artifact => return ← commitArtifact artifact
      | outcome =>
              throwError "leancert: recognized a finite-sum equality, but exact expansion failed.\n\
            {outcomeSummary outcome}"

  rejectUnsupportedPreparedFunctions prepared verbosity

  let some intent ← intentOfSemanticGoal semantic
    | throwError "leancert: parsed a semantic goal whose solver has not been migrated"

  let solvers := (portfolio intent cfg verificationMode).map SolverSpec.toSemanticSolver
  let mut failures : Array (String × AttemptOutcome) := #[]
  let mut spent := 0
  for solver in solvers do
    unless solver.supports semantic do
      continue
    if spent + solver.plan.cost > cfg.budget then
      continue
    spent := spent + solver.plan.cost
    trace[LeanCert.router] "trying {solver.plan.strategy} for {repr intent}"
    match ← solver.attempt prepared cfg with
    | .proved artifact =>
      trace[LeanCert.router] "succeeded with {artifact.report.plan.strategy}"
      return ← commitArtifact artifact
    | outcome =>
        trace[LeanCert.router] "{solver.plan.strategy} failed: {outcomeSummary outcome}"
        failures := failures.push (solver.plan.strategy, outcome)

  if let some refutation ← certifiedBoundRefutation? semantic prepared cfg then
    throwRouterFailure verbosity <|
      Diagnostic.RouterFailure.certifiedRefutation (some intent) refutation
  let attempts : Array Diagnostic.AttemptDiagnostic := failures.map fun (strategy, outcome) => {
    strategy
    outcome := outcomeSummary outcome
  }
  throwRouterFailure verbosity <|
    Diagnostic.RouterFailure.portfolioExhausted intent attempts spent cfg.budget

/-- One inline configuration item accepted by `leancert`. -/
declare_syntax_cat leanCertConfigItem
declare_syntax_cat leanCertTrustMode
syntax ident : leanCertTrustMode
syntax &"auto" : leanCertTrustMode
syntax "(" &"budget" " := " num ")" : leanCertConfigItem
syntax "(" &"taylorDepth" " := " num ")" : leanCertConfigItem
syntax "(" &"subdivisions" " := " num ")" : leanCertConfigItem
syntax "(" &"maxIterations" " := " num ")" : leanCertConfigItem
syntax "(" &"trust" " := " leanCertTrustMode ")" : leanCertConfigItem

private def elaborateInlineConfig (items : Array Syntax) : TacticM LeanCertConfig := do
  let mut cfg : LeanCertConfig := {}
  for item in items do
    match item with
    | `(leanCertConfigItem| (budget := $n:num)) =>
        cfg := { cfg with budget := n.getNat }
    | `(leanCertConfigItem| (taylorDepth := $n:num)) =>
        cfg := { cfg with taylorDepth := n.getNat }
    | `(leanCertConfigItem| (subdivisions := $n:num)) =>
        cfg := { cfg with subdivisions := n.getNat }
    | `(leanCertConfigItem| (maxIterations := $n:num)) =>
        cfg := { cfg with maxIterations := n.getNat }
    | `(leanCertConfigItem| (trust := $m:leanCertTrustMode)) =>
        let raw := m.raw.reprint.getD ""
        let some mode := VerificationMode.ofString? raw
          | throwErrorAt m "invalid trust mode '{raw}'; expected kernel, native, or auto"
        cfg := { cfg with trust := some mode }
    | _ => throwUnsupportedSyntax
  return cfg

/-- `leancert` selects a solver from the semantic shape of the goal. -/
syntax (name := leanCertTac) "leancert" leanCertConfigItem* : tactic

/-- `leancert?` proves the goal and reports the successful dedicated tactic. -/
syntax (name := leanCertQuestionTac) "leancert?" leanCertConfigItem* : tactic

@[tactic leanCertTac]
unsafe def elabLeanCert : Tactic := fun stx => do
  let cfg ← elaborateInlineConfig stx[1].getArgs
  withTrustMode cfg.trust do
    discard <| runLeanCert cfg Diagnostic.DiagnosticVerbosity.compact

@[tactic leanCertQuestionTac]
unsafe def elabLeanCertQuestion : Tactic := fun stx => do
  let cfg ← elaborateInlineConfig stx[1].getArgs
  withTrustMode cfg.trust do
    let result ← runLeanCert cfg Diagnostic.DiagnosticVerbosity.explain
    logInfo m!"{Diagnostic.successReport result}"

end LeanCert.Tactic
