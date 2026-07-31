/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Tactic.IntervalAuto.Extract
import LeanCert.Validity.Eventual

/-!
# Fixed-cutoff eventual-bound tactic

`eventual_bound` closes an explicit natural-number tail bound using an
executable LeanCert certificate.  The initial certificate language covers
nonnegative rational multiples of reciprocal powers.
-/

open Lean Elab Tactic

namespace LeanCert.Tactic

open Lean Meta
open LeanCert.Tactic.Auto

private def binaryArgs? (e : Expr) (name : Name) : Option (Expr × Expr) :=
  if !e.isAppOf name then none
  else
    let args := e.getAppArgs
    if h : 2 ≤ args.size then
      some (args[args.size - 2], args[args.size - 1])
    else none

private structure ParsedReciprocalPowerGoal where
  coefficient : ℚ
  bound : ℚ
  exponent : Nat
  cutoff : Nat

private def parseReciprocalPowerGoal : TacticM ParsedReciprocalPowerGoal := do
  let target ← instantiateMVars (← getMainTarget)
  let .forallE _ _ tailBody _ := target
    | throwError "expected `∀ n : Nat, N ≤ n → ...`"
  let .forallE _ tailHypothesis conclusion _ := tailBody
    | throwError "expected the tail hypothesis `N ≤ n`"
  let cutoffExpr ←
    match binaryArgs? tailHypothesis ``LE.le with
    | some (cutoff, _) => pure cutoff
    | none =>
        match binaryArgs? tailHypothesis ``GE.ge with
        | some (_, cutoff) => pure cutoff
        | none => throwError "expected the tail hypothesis `N ≤ n`"
  let some (lhs, boundExpr) := binaryArgs? conclusion ``LE.le
    | throwError "expected an upper-bound inequality"
  let some (qExpr, denominator) := binaryArgs? lhs ``HDiv.hDiv
    | throwError "expected a quotient `q / (n : ℝ) ^ k`; got {lhs} with head {lhs.getAppFn.constName?}"
  let exponent :=
    match binaryArgs? denominator ``HPow.hPow with
    | some (_, exponent) => exponent
    | none => toExpr (1 : Nat)
  let some q ← extractRatFromReal qExpr
    | throwError "the reciprocal-power coefficient is not a rational literal"
  let some bound ← extractRatFromReal boundExpr
    | throwError "the comparison bound is not a rational literal"
  let some exponent ← getNatValue? exponent
    | throwError "the reciprocal-power exponent is not a natural-number literal"
  let some cutoff ← getNatValue? cutoffExpr
    | throwError "the cutoff is not a natural-number literal"
  pure { coefficient := q, bound, exponent, cutoff }

private def runEventualBound (cutoff? : Option (TSyntax `term))
    (explain : Bool) : TacticM Unit := do
  let saved ← saveState
  try
    if let some cutoff := cutoff? then
      evalTactic (← `(tactic| refine ⟨$cutoff, ?_⟩))
    let parsed ← parseReciprocalPowerGoal
    unless 0 ≤ parsed.coefficient && 0 < parsed.exponent && 0 < parsed.cutoff &&
        parsed.coefficient / (parsed.cutoff : ℚ) ^ parsed.exponent ≤ parsed.bound do
      throwError "the reciprocal-power certificate was rejected"
    let q ← Term.exprToSyntax (toExpr parsed.coefficient)
    let bound ← Term.exprToSyntax (toExpr parsed.bound)
    let exponent ← Term.exprToSyntax (toExpr parsed.exponent)
    let cutoff ← Term.exprToSyntax (toExpr parsed.cutoff)
    evalTactic (← `(tactic|
      convert LeanCert.Validity.verify_reciprocal_power_upper
        ($q : ℚ) ($bound : ℚ) $exponent $cutoff
          (by norm_num [LeanCert.Validity.checkReciprocalPowerUpper]) using 1 <;>
        norm_num))
    unless (← getUnsolvedGoals).isEmpty do
      throwError "the reciprocal-power certificate was rejected"
    if explain then
      let cutoffLine := cutoff?.map
        (fun cutoff => s!"\nCutoff:\n  N = {cutoff}") |>.getD
          "\nCutoff:\n  read from the universal goal"
      logInfo m!"LeanCert recognized: fixed-cutoff eventual upper bound

Selected strategy:
  reciprocal-power tail certificate{cutoffLine}

Tail rule:
  nonnegative rational multiple of 1 / n^k
  endpoint checked exactly; global decay proved symbolically

Certificate verification:
  kernel (`norm_num`)

Suggested proof:
  by
    {if cutoff?.isSome then s!"eventual_bound using {cutoff?.get!}" else "eventual_bound"}"
  catch exception =>
    saved.restore
    let detail ← exception.toMessageData.toString
    throwError "Eventual bound certification failed.\n\n\
      H1 currently accepts goals of the form\n  \
      `∀ n : Nat, N ≤ n → q / (n : ℝ) ^ k ≤ c`\n\
      with `q ≥ 0`, `k > 0`, and `N > 0`. For existential goals, write\n  \
      `eventual_bound using N`.\n\n\
      The cutoff may be too small, or the tail expression may be outside this\n\
      initial certificate language.\n\nUnderlying elaboration detail:\n{detail}"

syntax (name := eventualBoundTac) "eventual_bound" (" using " term)? : tactic
syntax (name := eventualBoundQuestionTac) "eventual_bound?" (" using " term)? : tactic

elab_rules : tactic
  | `(tactic| eventual_bound $[using $cutoff]?) =>
      runEventualBound cutoff false
  | `(tactic| eventual_bound? $[using $cutoff]?) =>
      runEventualBound cutoff true

end LeanCert.Tactic
