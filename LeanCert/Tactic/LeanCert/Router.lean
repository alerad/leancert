/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Tactic.LeanCert.Config
import LeanCert.Tactic.LeanCert.Parse
import LeanCert.Tactic.LeanCert.Transaction

/-!
# Semantic LeanCert Router

`leancert` classifies the mathematical shape of the goal and runs a small,
deterministic portfolio of existing tactics transactionally.  It is a semantic
front door, not a new numerical engine.
-/

open Lean Meta Elab Tactic

namespace LeanCert.Tactic

open LeanCert.Tactic.Discovery

initialize registerTraceClass `LeanCert.router

private structure SolverSpec where
  report : SolverReport
  solve : TacticM Unit

private def report (intent : GoalIntent) (method : String)
    (backend : Option String := none) : SolverReport :=
  { intent, method, backend }

private def numSyntax (n : Nat) : TSyntax `num :=
  ⟨Syntax.mkNumLit (toString n)⟩

private def subdivisionAttempt (cfg : LeanCertConfig) : TacticM Unit := do
  let depth := numSyntax cfg.taylorDepth
  let subdivisions := numSyntax cfg.subdivisions
  evalTactic (← `(tactic| interval_bound_subdiv $depth:num $subdivisions:num))

private def pointAttempt (depth : Nat) : TacticM Unit := do
  let depth := numSyntax depth
  evalTactic (← `(tactic| interval_auto $depth:num))

/-- The deterministic strategy portfolio for a recognized goal intent. -/
private unsafe def portfolio (intent : GoalIntent) (cfg : LeanCertConfig) : Array SolverSpec :=
  let d := cfg.taylorDepth
  let d2 := d + 10
  let d3 := d + 20
  match intent with
  | .pointInequality => #[
      { report := report intent "norm_num", solve := do evalTactic (← `(tactic| norm_num)) },
      { report := report intent s!"interval_auto {d}" (some "rational interval"),
        solve := pointAttempt d },
      { report := report intent s!"interval_auto {d2}" (some "rational interval"),
        solve := pointAttempt d2 }]
  | .intervalBound => #[
      { report := report intent s!"interval_bound {d}" (some "rational interval"),
        solve := Auto.intervalBoundCore d },
      { report := report intent s!"interval_bound {d2}" (some "rational interval"),
        solve := Auto.intervalBoundCore d2 },
      { report := report intent s!"interval_bound_subdiv {d} {cfg.subdivisions}"
          (some "subdivision"), solve := subdivisionAttempt cfg },
      { report := report intent
          (if cfg.useMonotonicity then s!"opt_bound {cfg.maxIterations} mono"
           else s!"opt_bound {cfg.maxIterations}") (some "global optimization"),
        solve := Auto.optBoundCore cfg.maxIterations cfg.useMonotonicity d }]
  | .multivariateBound => #[
      { report := report intent s!"multivariate_bound {cfg.maxIterations}"
          (some "global optimization"),
        solve := Auto.multivariateBoundCore cfg.maxIterations (1 / 1000) cfg.useMonotonicity d },
      { report := report intent s!"multivariate_bound {2 * cfg.maxIterations}"
          (some "global optimization"),
        solve := Auto.multivariateBoundCore (2 * cfg.maxIterations) (1 / 10000)
          cfg.useMonotonicity d2 }]
  | .rootExists => #[
      { report := report intent s!"interval_roots {d}", solve := intervalRootsCore d },
      { report := report intent s!"interval_roots {d2}", solve := intervalRootsCore d2 },
      { report := report intent s!"interval_roots {d3}", solve := intervalRootsCore d3 }]
  | .uniqueRoot => #[
      { report := report intent s!"interval_unique_root {d}", solve := intervalUniqueRootCore d },
      { report := report intent s!"interval_unique_root {d2}", solve := intervalUniqueRootCore d2 },
      { report := report intent s!"interval_unique_root {d3}", solve := intervalUniqueRootCore d3 }]
  | .noRoot => #[
      { report := report intent s!"root_bound {d}", solve := Auto.rootBoundCore d },
      { report := report intent s!"root_bound {d2}", solve := Auto.rootBoundCore d2 },
      { report := report intent s!"root_bound {d3}", solve := Auto.rootBoundCore d3 }]
  | .existentialMinimum => #[
      { report := report intent s!"interval_minimize {d}", solve := intervalMinimizeCore d },
      { report := report intent s!"interval_minimize_mv {d}", solve := intervalMinimizeMvCore d },
      { report := report intent s!"interval_minimize {d2}", solve := intervalMinimizeCore d2 }]
  | .existentialMaximum => #[
      { report := report intent s!"interval_maximize {d}", solve := intervalMaximizeCore d },
      { report := report intent s!"interval_maximize_mv {d}", solve := intervalMaximizeMvCore d },
      { report := report intent s!"interval_maximize {d2}", solve := intervalMaximizeCore d2 }]
  | .argmin => #[
      { report := report intent s!"interval_argmin {d}", solve := intervalArgminCore d },
      { report := report intent s!"interval_argmin {d2}", solve := intervalArgminCore d2 }]
  | .argmax => #[
      { report := report intent s!"interval_argmax {d}", solve := intervalArgmaxCore d },
      { report := report intent s!"interval_argmax {d2}", solve := intervalArgmaxCore d2 }]
  | .finiteSum => #[
      { report := report intent "finsum_bound" (some "dyadic interval"),
        solve := finSumBoundCore (-53) 10 },
      { report := report intent "finsum_bound 80" (some "dyadic interval"),
        solve := finSumBoundCore (-80) 10 }]
  | .certificateCheck => #[
      { report := report intent "native_decide" (some "closed LeanCert checker"),
        solve := do evalTactic (← `(tactic| native_decide)) }]
  | .integralBound => #[
      { report := report intent "integral_exact" (some "exact rational polynomial"),
        solve := integralExactCore },
      { report := report intent "integral_search 16 512" (some "checked rational partitions"),
        solve := integralSearchCore 16 512 },
      { report := report intent s!"interval_integrate {d}" (some "explicit enclosure"),
        solve := intervalIntegrateCore d },
      { report := report intent "integral_search 16 4096" (some "checked rational partitions"),
        solve := integralSearchCore 16 4096 },
      { report := report intent "integral_search 16 16384" (some "checked rational partitions"),
        solve := integralSearchCore 16 16384 }]

private def failureSummary : AttemptFailure → String
  | .unsupportedExpression remaining _ => s!"unsupported expression: {remaining}"
  | .certificateRejected _ => "certificate checker rejected the candidate"
  | .incompleteProof goals =>
      s!"solver left {goals.size} goal(s), beginning with: {goals[0]?.getD "<unknown>"}"
  | .invalidDomain detail => s!"invalid domain: {detail}"
  | .budgetExhausted _ => "strategy budget exhausted"
  | .internalFailure detail => detail

/-- Classify and solve the main goal.  On success, return the exact strategy report. -/
unsafe def runLeanCert (cfg : LeanCertConfig) : TacticM SolverReport := do
  if cfg.budget = 0 then
    throwError "leancert: `budget` must be positive"
  let goal ← getMainGoal
  let goalType ← goal.getType
  let some intent ← classifyGoal goalType
    | throwError "leancert: unsupported goal shape.\n\nGoal:\n{goalType}\n\n\
        Try a dedicated LeanCert tactic, or use `set_option trace.LeanCert.router true` \
        while extending the semantic classifier."

  let specs := (portfolio intent cfg).toList.take cfg.budget
  let mut failures : Array (String × AttemptFailure) := #[]
  for spec in specs do
    trace[LeanCert.router] "trying {spec.report.method} for {repr intent}"
    match ← runAttempt spec.report spec.solve with
    | .ok result =>
        trace[LeanCert.router] "succeeded with {result.method}"
        return result
    | .error failure =>
        trace[LeanCert.router] "{spec.report.method} failed: {failureSummary failure}"
        failures := failures.push (spec.report.method, failure)

  let details := failures.toList.map (fun (method, failure) =>
    s!"  • {method}: {failureSummary failure}")
  throwError "leancert: recognized {repr intent}, but no strategy closed the goal \
    within budget {cfg.budget}.\n{String.intercalate "\n" details}"

/-- One inline configuration item accepted by `leancert`. -/
declare_syntax_cat leanCertConfigItem
syntax "(" &"budget" " := " num ")" : leanCertConfigItem
syntax "(" &"taylorDepth" " := " num ")" : leanCertConfigItem
syntax "(" &"subdivisions" " := " num ")" : leanCertConfigItem
syntax "(" &"maxIterations" " := " num ")" : leanCertConfigItem

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
    | _ => throwUnsupportedSyntax
  return cfg

/-- `leancert` selects a solver from the semantic shape of the goal. -/
syntax (name := leanCertTac) "leancert" leanCertConfigItem* : tactic

/-- `leancert?` proves the goal and reports the successful dedicated tactic. -/
syntax (name := leanCertQuestionTac) "leancert?" leanCertConfigItem* : tactic

@[tactic leanCertTac]
unsafe def elabLeanCert : Tactic := fun stx => do
  let cfg ← elaborateInlineConfig stx[1].getArgs
  discard <| runLeanCert cfg

@[tactic leanCertQuestionTac]
unsafe def elabLeanCertQuestion : Tactic := fun stx => do
  let cfg ← elaborateInlineConfig stx[1].getArgs
  let result ← runLeanCert cfg
  logInfo m!"Try this: {result.method}"

end LeanCert.Tactic
