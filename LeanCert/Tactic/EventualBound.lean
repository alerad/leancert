/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Tactic.IntervalAuto.Extract
import LeanCert.Validity.Eventual

/-!
# Eventual-bound certification and cutoff discovery

The fixed-cutoff checker is trusted only through its Golden Theorem. Cutoff
search is deterministic but untrusted: its sole output is a candidate fed back
to `checkReciprocalPowerUpper` before proof construction.
-/

open Lean Elab Tactic

namespace LeanCert.Tactic

open Lean Meta
open LeanCert.Tactic.Auto

/-- Expected failures of eventual-bound parsing, search, and certification. -/
inductive EventualBoundFailure where
  | unsupportedTail (expression detail : String)
  | invalidParameters (detail : String)
  | rejectedCutoff (cutoff : Nat)
  | searchExhausted (checks lastCutoff : Nat)
  | transportFailure (detail : String)
  | internalFailure (detail : String)
  deriving Inhabited, Repr

/-- Search facts retained from the single candidate-generation run. -/
structure EventualSearchStatistics where
  cutoff : Nat
  checks : Nat
  configuredLimit : Nat
  exponentialSteps : Nat
  refinementSteps : Nat
  lowerBracket : Nat
  upperBracket : Nat
  refinementComplete : Bool
  deriving Inhabited, Repr

/-- Runtime facts returned by successful eventual-bound certification. -/
structure EventualBoundOutcome where
  cutoff : Nat
  discovered : Bool
  checker : Name := ``LeanCert.Validity.checkReciprocalPowerUpper
  verifier : Name := ``LeanCert.Validity.verify_reciprocal_power_upper
  search : Option EventualSearchStatistics := none
  deriving Inhabited, Repr

private inductive CutoffRequest where
  | fixed (cutoff : Nat)
  | discover

private structure ParsedReciprocalPowerGoal where
  coefficient : ℚ
  bound : ℚ
  exponent : Nat
  cutoff : CutoffRequest

private def binaryArgs? (e : Expr) (name : Name) : Option (Expr × Expr) :=
  if !e.isAppOf name then none
  else
    let args := e.getAppArgs
    if h : 2 ≤ args.size then
      some (args[args.size - 2], args[args.size - 1])
    else none

private def parseUniversal (target : Expr) (request : CutoffRequest) :
    MetaM (Except EventualBoundFailure ParsedReciprocalPowerGoal) := do
  let .forallE _ indexType tailBody _ := target
    | return .error (.unsupportedTail (toString target)
        "expected `∀ n : Nat, N ≤ n → ...`")
  unless indexType.isConstOf ``Nat do
    return .error (.unsupportedTail (toString target)
      "the tail index must have type `Nat`")
  let .forallE _ tailHypothesis conclusion _ := tailBody
    | return .error (.unsupportedTail (toString target)
        "expected the tail hypothesis `N ≤ n`")
  let cutoffExpr ←
    match binaryArgs? tailHypothesis ``LE.le with
    | some (cutoff, _) => pure cutoff
    | none =>
        match binaryArgs? tailHypothesis ``GE.ge with
        | some (_, cutoff) => pure cutoff
        | none => return .error (.unsupportedTail (toString tailHypothesis)
            "expected the tail hypothesis `N ≤ n`")
  let request ←
    match request with
    | .discover => pure .discover
    | .fixed _ =>
        let some cutoff ← getNatValue? cutoffExpr
          | return .error (.unsupportedTail (toString cutoffExpr)
              "the cutoff is not a natural-number literal")
        pure (.fixed cutoff)
  let some (lhs, boundExpr) := binaryArgs? conclusion ``LE.le
    | return .error (.unsupportedTail (toString conclusion)
        "expected an eventual upper-bound comparison")
  let some (qExpr, denominator) := binaryArgs? lhs ``HDiv.hDiv
    | return .error (.unsupportedTail (toString lhs)
        "expected a quotient `q / (n : ℝ) ^ k`")
  let exponentExpr :=
    match binaryArgs? denominator ``HPow.hPow with
    | some (_, exponent) => exponent
    | none => toExpr (1 : Nat)
  let some coefficient ← extractRatFromReal qExpr
    | return .error (.unsupportedTail (toString qExpr)
        "the coefficient is not a rational literal")
  let some bound ← extractRatFromReal boundExpr
    | return .error (.unsupportedTail (toString boundExpr)
        "the comparison bound is not a rational literal")
  let some exponent ← getNatValue? exponentExpr
    | return .error (.unsupportedTail (toString exponentExpr)
        "the reciprocal-power exponent is not a natural-number literal")
  return .ok { coefficient, bound, exponent, cutoff := request }

/-- Parse either a fixed universal goal or an existential cutoff goal. -/
private def parseReciprocalPowerGoal : TacticM
    (Except EventualBoundFailure ParsedReciprocalPowerGoal) := do
  let target ← instantiateMVars (← getMainTarget)
  if target.isAppOfArity ``Exists 2 then
    let args := target.getAppArgs
    unless args[0]!.isConstOf ``Nat do
      return .error (.unsupportedTail (toString target)
        "the cutoff witness must have type `Nat`")
    let .lam _ _ body _ := args[1]!
      | return .error (.unsupportedTail (toString target)
          "could not inspect the existential cutoff body")
    parseUniversal (body.instantiate1 (toExpr (1 : Nat))) .discover
  else
    parseUniversal target (.fixed 0)

private def accepts (q bound : ℚ) (k cutoff : Nat) : Bool :=
  LeanCert.Validity.checkReciprocalPowerUpper q bound k cutoff

private partial def exponentialSearch (q bound : ℚ) (k : Nat)
    (limit checks lo hi steps : Nat) :
    Except EventualBoundFailure (Nat × Nat × Nat × Nat) :=
  if checks ≥ limit then .error (.searchExhausted checks lo)
  else if accepts q bound k hi then .ok (lo, hi, checks + 1, steps + 1)
  else exponentialSearch q bound k limit (checks + 1) hi (2 * hi) (steps + 1)

private partial def binaryRefine (q bound : ℚ) (k limit : Nat)
    (checks lo hi steps : Nat) : Nat × Nat × Nat × Nat × Bool :=
  if lo + 1 ≥ hi then (lo, hi, checks, steps, true)
  else if checks ≥ limit then (lo, hi, checks, steps, false)
  else
    let mid := (lo + hi) / 2
    if accepts q bound k mid then
      binaryRefine q bound k limit (checks + 1) lo mid (steps + 1)
    else
      binaryRefine q bound k limit (checks + 1) mid hi (steps + 1)

/-- Untrusted exponential search followed by bounded binary refinement. Every
accepted result is independently replayed by the H1 checker. -/
def discoverReciprocalPowerCutoff (q bound : ℚ) (k maxChecks : Nat) :
    Except EventualBoundFailure EventualSearchStatistics := do
  if q < 0 then throw (.invalidParameters "the coefficient must be nonnegative")
  if k = 0 then throw (.invalidParameters "the exponent must be positive")
  if maxChecks = 0 then throw (.searchExhausted 0 0)
  if accepts q bound k 1 then
    return {
      cutoff := 1
      checks := 1
      configuredLimit := maxChecks
      exponentialSteps := 0
      refinementSteps := 0
      lowerBracket := 0
      upperBracket := 1
      refinementComplete := true
    }
  if bound < 0 || (0 < q && bound = 0) then
    throw (.invalidParameters
      "a nonnegative reciprocal-power tail cannot satisfy this upper bound")
  let (lo, hi, checks, exponentialSteps) ←
    exponentialSearch q bound k maxChecks 1 1 2 0
  let (lo, hi, checks, refinementSteps, complete) :=
    binaryRefine q bound k maxChecks checks lo hi 0
  return {
    cutoff := hi
    checks
    configuredLimit := maxChecks
    exponentialSteps
    refinementSteps
    lowerBracket := lo
    upperBracket := hi
    refinementComplete := complete
  }

private def closeWithCutoff (parsed : ParsedReciprocalPowerGoal) (cutoff : Nat) :
    TacticM Unit := do
  unless accepts parsed.coefficient parsed.bound parsed.exponent cutoff do
    throwError "the final reciprocal-power certificate was rejected"
  if let .discover := parsed.cutoff then
    let cutoffSyntax ← Term.exprToSyntax (toExpr cutoff)
    evalTactic (← `(tactic| refine ⟨$cutoffSyntax, ?_⟩))
  let q ← Term.exprToSyntax (toExpr parsed.coefficient)
  let bound ← Term.exprToSyntax (toExpr parsed.bound)
  let exponent ← Term.exprToSyntax (toExpr parsed.exponent)
  let cutoff ← Term.exprToSyntax (toExpr cutoff)
  evalTactic (← `(tactic|
    convert LeanCert.Validity.verify_reciprocal_power_upper
      ($q : ℚ) ($bound : ℚ) $exponent $cutoff
        (by norm_num [LeanCert.Validity.checkReciprocalPowerUpper]) using 1 <;>
      norm_num))
  unless (← getUnsolvedGoals).isEmpty do
    throwError "eventual-bound proof transport left unsolved goals"

/-- Reporting-aware core shared by the dedicated tactic and semantic router. -/
def eventualBoundCoreTyped (cutoff? : Option Nat) (maxChecks : Nat := 1000) :
    TacticM (Except EventualBoundFailure EventualBoundOutcome) := do
  let saved ← saveState
  try
    if let some cutoff := cutoff? then
      let cutoffSyntax ← Term.exprToSyntax (toExpr cutoff)
      evalTactic (← `(tactic| refine ⟨$cutoffSyntax, ?_⟩))
    let parsed ←
      match ← parseReciprocalPowerGoal with
      | .ok parsed => pure parsed
      | .error failure => saved.restore; return .error failure
    let (cutoff, search?) ←
      match cutoff?, parsed.cutoff with
      | some cutoff, _ => pure (cutoff, none)
      | none, .fixed cutoff => pure (cutoff, none)
      | none, .discover =>
          match discoverReciprocalPowerCutoff parsed.coefficient parsed.bound
              parsed.exponent maxChecks with
          | .ok statistics => pure (statistics.cutoff, some statistics)
          | .error failure => saved.restore; return .error failure
    unless accepts parsed.coefficient parsed.bound parsed.exponent cutoff do
      saved.restore
      return .error (.rejectedCutoff cutoff)
    try closeWithCutoff parsed cutoff
    catch exception =>
      saved.restore
      return .error (.transportFailure (← exception.toMessageData.toString))
    return .ok { cutoff, discovered := search?.isSome, search := search? }
  catch exception =>
    saved.restore
    return .error (.internalFailure (← exception.toMessageData.toString))

private def failureMessage : EventualBoundFailure → String
  | .unsupportedTail expression detail =>
      s!"Unsupported eventual tail:\n  {expression}\n\n{detail}\n\nThe current certificate language supports nonnegative rational multiples of reciprocal powers."
  | .invalidParameters detail => s!"Eventual-bound parameters are invalid: {detail}."
  | .rejectedCutoff cutoff => s!"The eventual-bound checker rejected cutoff N = {cutoff}."
  | .searchExhausted checks last =>
      s!"Cutoff discovery exhausted its check budget after {checks} candidate(s); last cutoff: {last}. Try `(maxIterations := ...)` or provide `using N`."
  | .transportFailure detail => s!"Eventual-bound proof transport failed:\n{detail}"
  | .internalFailure detail => s!"Eventual-bound certification encountered an internal error:\n{detail}"

private def runEventualBound (cutoff? : Option (TSyntax `term))
    (maxChecks : Nat) (explain : Bool) : TacticM Unit := do
  let cutoffValue? ← cutoff?.mapM fun cutoff => do
    let expression ← Term.elabTerm cutoff (some (mkConst ``Nat))
    let some value ← getNatValue? expression
      | throwErrorAt cutoff "the cutoff must be a natural-number literal"
    pure value
  match ← eventualBoundCoreTyped cutoffValue? maxChecks with
  | .error failure => throwError (failureMessage failure)
  | .ok outcome =>
      if explain then
        let search := match outcome.search with
          | none => "  Source: explicit cutoff"
          | some statistics =>
              s!"  Source: automatic discovery\n  Candidates checked: {statistics.checks}\n  Discovered cutoff: N = {statistics.cutoff}\n  Minimality refinement complete: {statistics.refinementComplete}"
        logInfo m!"LeanCert recognized: eventual natural-number upper bound

Selected strategy:
  reciprocal-power tail certificate

Cutoff:
{search}

Certificate verification:
  kernel (`norm_num`)

Suggested stable proof:
  by
    eventual_bound using {outcome.cutoff}"

declare_syntax_cat eventualBoundConfigItem
syntax "(" &"maxIterations" " := " num ")" : eventualBoundConfigItem
syntax (name := eventualBoundTac) "eventual_bound" (" using " term)?
  eventualBoundConfigItem* : tactic
syntax (name := eventualBoundQuestionTac) "eventual_bound?" (" using " term)?
  eventualBoundConfigItem* : tactic

private def parseMaxChecks (items : Array Syntax) : TacticM Nat := do
  let mut maxChecks := 1000
  for item in items do
    match item with
    | `(eventualBoundConfigItem| (maxIterations := $n:num)) =>
        maxChecks := n.getNat
    | _ => throwUnsupportedSyntax
  return maxChecks

elab_rules : tactic
  | `(tactic| eventual_bound $[using $cutoff]? $items:eventualBoundConfigItem*) => do
      runEventualBound cutoff (← parseMaxChecks items) false
  | `(tactic| eventual_bound? $[using $cutoff]? $items:eventualBoundConfigItem*) => do
      runEventualBound cutoff (← parseMaxChecks items) true

end LeanCert.Tactic
