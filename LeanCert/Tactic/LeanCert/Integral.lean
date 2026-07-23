/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import Mathlib.Tactic
import LeanCert.Engine.Algebra.QPolyIntegral
import LeanCert.Meta.Numeral
import LeanCert.Meta.ProveSupported
import LeanCert.Tactic.LeanCert.Config
import LeanCert.Tactic.LeanCert.Normalize
import LeanCert.Validity.Integration

/-!
# Natural integral goals

This module parses ordinary interval-integral equalities and inequalities.  It
first tries exact rational-polynomial integration, then falls back to LeanCert's
checked partition search for non-polynomial expressions.
-/

open Lean Meta Elab Tactic

namespace LeanCert.Tactic

open LeanCert.Core LeanCert.Engine LeanCert.Meta

inductive IntegralComparison where
  | eq | upper | lower
  deriving Repr, BEq

structure ParsedIntegralGoal where
  comparison : IntegralComparison
  targetIntegral : Lean.Expr
  integrand : Lean.Expr
  lo : Lean.Expr
  hi : Lean.Expr
  bound : Lean.Expr

private def parseIntegralTerm? (e : Lean.Expr) : Option (Lean.Expr × Lean.Expr × Lean.Expr) :=
  if e.getAppFn.constName? == some ``intervalIntegral && e.getAppNumArgs >= 4 then
    let args := e.getAppArgs
    -- The final explicit arguments are function, lower endpoint, upper
    -- endpoint, and measure; universe/typeclass parameters precede them.
    some (args[args.size - 4]!, args[args.size - 3]!, args[args.size - 2]!)
  else none

/-- Parse `integral = c`, `integral ≤ c`, and `c ≤ integral`, including the
corresponding reversed equality.  Bounds and endpoints are validated as
rationals by the solver rather than by classification. -/
def parseNaturalIntegralGoal (goal : Lean.Expr) : MetaM (Option ParsedIntegralGoal) := do
  let parseSide (comparison : IntegralComparison) (integ bound : Lean.Expr) :=
    match parseIntegralTerm? integ with
    | some (fexpr, lo, hi) =>
        some ⟨comparison, integ, fexpr, lo, hi, bound⟩
    | none => none
  match_expr goal with
  | Eq _ lhs rhs =>
      if let some parsed := parseSide .eq lhs rhs then return some parsed
      if let some parsed := parseSide .eq rhs lhs then return some parsed
      return none
  | LE.le _ lhs rhs =>
      if let some parsed := parseSide .upper lhs rhs then return some parsed
      if let some parsed := parseSide .lower rhs lhs then return some parsed
      return none
  | _ => return none

/-- Recognize a single natural integral comparison or a conjunction of them. -/
partial def isNaturalIntegralGoal (goal : Lean.Expr) : MetaM Bool := do
  if (← parseNaturalIntegralGoal goal).isSome then return true
  if goal.isAppOfArity ``And 2 then
    let args := goal.getAppArgs
    return (← isNaturalIntegralGoal args[0]!) && (← isNaturalIntegralGoal args[1]!)
  return false

private def exactIntegralAttempt (parsed : ParsedIntegralGoal) : TacticM Unit := do
  let some a ← LeanCert.Meta.Numeral.toRat? parsed.lo
    | throwError "exact integral: lower endpoint is not rational: {parsed.lo}"
  let some b ← LeanCert.Meta.Numeral.toRat? parsed.hi
    | throwError "exact integral: upper endpoint is not rational"
  let reified ← reifyWithReport parsed.integrand
  let astValue ← unsafe evalExpr LeanCert.Core.Expr (mkConst ``LeanCert.Core.Expr) reified.expr
  let some poly := QPoly.ofExpr astValue
    | throwError "exact integral: integrand is not a rational polynomial"
  let value := poly.integralRat a b
  let checkType ← mkAppM ``Eq #[
    ← mkAppM ``QPoly.checkExactIntegral #[reified.expr, toExpr a, toExpr b, toExpr value],
    mkConst ``Bool.true]
  let checkProof ← mkDecideProof checkType
  let proof ← mkAppM ``QPoly.integral_eq_of_check
    #[reified.expr, toExpr a, toExpr b, toExpr value, checkProof]
  let proofSyntax ← Term.exprToSyntax proof
  unfoldReifiedDefinitions reified.unfolded
  evalTactic (← `(tactic|
    have hIntegral := ($proofSyntax);
    simp_all only [
      LeanCert.Core.Expr.eval_add,
      LeanCert.Core.Expr.eval_mul,
      LeanCert.Core.Expr.eval_neg,
      LeanCert.Core.Expr.eval_inv,
      LeanCert.Core.Expr.eval_const,
      LeanCert.Core.Expr.eval_var,
      Rat.divInt_eq_div,
      sq, pow_two, pow_succ, pow_zero, pow_one,
      sub_eq_add_neg, div_eq_mul_inv, one_mul, mul_one];
    linarith [hIntegral]))

private def mkIntervalRatExpr (a b : ℚ) : MetaM Lean.Expr := do
  unless a ≤ b do
    throwError "numerical integral bounds currently require lower endpoint ≤ upper endpoint"
  let leType ← mkAppM ``LE.le #[toExpr a, toExpr b]
  let leProof ← mkDecideProof leType
  mkAppM ``IntervalRat.mk #[toExpr a, toExpr b, leProof]

private def numericalIntegralAttempt (parsed : ParsedIntegralGoal)
    (startN maxN : Nat) : TacticM Unit := do
  let some a ← LeanCert.Meta.Numeral.toRat? parsed.lo
    | throwError "numerical integral: lower endpoint is not rational"
  let some b ← LeanCert.Meta.Numeral.toRat? parsed.hi
    | throwError "numerical integral: upper endpoint is not rational"
  let some c ← LeanCert.Meta.Numeral.toRat? parsed.bound
    | throwError "numerical integral: comparison bound is not rational"
  if parsed.comparison == .eq then
    throwError "numerical interval enclosures do not certify exact equality"
  let reified ← reifyWithReport parsed.integrand
  let supportProof ← mkSupportedCoreProof reified.expr
  let interval ← mkIntervalRatExpr a b
  let integrableProof ← mkAppM ``LeanCert.Validity.Integration.exprSupportedCore_intervalIntegrable
    #[reified.expr, supportProof, interval]
  let startPositiveType ← mkAppM ``LT.lt #[toExpr 0, toExpr startN]
  let startPositive ← mkDecideProof startPositiveType
  let (theoremName, checkerName) :=
    if parsed.comparison == .upper then
      (``LeanCert.Validity.Integration.integral_search_upper_of_check,
        ``LeanCert.Validity.Integration.checkIntegralSearchUpperBound)
    else
      (``LeanCert.Validity.Integration.integral_search_lower_of_check,
        ``LeanCert.Validity.Integration.checkIntegralSearchLowerBound)
  let checker ← mkAppM checkerName
    #[reified.expr, interval, toExpr startN, toExpr maxN, toExpr c]
  let checkerPassed ← unsafe evalExpr Bool (mkConst ``Bool) checker
  unless checkerPassed do
    let boundExpr ← mkAppM ``LeanCert.Validity.Integration.integratePartitionChecked
      #[reified.expr, interval, toExpr maxN]
    let optionIntervalType := mkApp (mkConst ``Option) (mkConst ``IntervalRat)
    let checkedBound ← unsafe evalExpr (Option IntervalRat) optionIntervalType boundExpr
    match checkedBound with
    | some enclosure =>
        throwError "checked partition search reached enclosure \
          [{enclosure.lo}, {enclosure.hi}], which does not prove the requested \
          {if parsed.comparison == .upper then "upper" else "lower"} bound {c}"
    | none =>
        throwError "checked partition evaluation rejected the integrand domain \
          or could not construct an enclosure"
  let checkType ← mkAppM ``Eq #[checker, mkConst ``Bool.true]
  let checkProof ← mkDecideProof checkType
  let proof ← mkAppM theoremName #[reified.expr, interval, toExpr startN, toExpr maxN,
    startPositive, toExpr c, checkProof, integrableProof]
  let proofSyntax ← Term.exprToSyntax proof
  unfoldReifiedDefinitions reified.unfolded
  evalTactic (← `(tactic|
    have hIntegral := ($proofSyntax);
    simp_all only [
      LeanCert.Core.Expr.eval_add,
      LeanCert.Core.Expr.eval_mul,
      LeanCert.Core.Expr.eval_neg,
      LeanCert.Core.Expr.eval_inv,
      LeanCert.Core.Expr.eval_const,
      LeanCert.Core.Expr.eval_var,
      LeanCert.Core.Expr.eval_sin,
      LeanCert.Core.Expr.eval_cos,
      LeanCert.Core.Expr.eval_exp,
      LeanCert.Core.Expr.eval_log,
      LeanCert.Core.Expr.eval_atan,
      LeanCert.Core.Expr.eval_arsinh,
      LeanCert.Core.Expr.eval_sqrt,
      Rat.divInt_eq_div,
      sq, pow_two, pow_succ, pow_zero, pow_one,
      sub_eq_add_neg, div_eq_mul_inv, one_mul, mul_one];
    exact hIntegral))

/-- Exact integral strategy used by the semantic router. -/
partial def integralExactCore : TacticM Unit := do
  let goal ← getMainGoal
  let goalType ← goal.getType
  if goalType.isAppOfArity ``And 2 then
    evalTactic (← `(tactic| constructor))
    let goals ← getGoals
    for subgoal in goals do
      setGoals [subgoal]
      integralExactCore
  else
    let some parsed ← parseNaturalIntegralGoal goalType
      | throwError "integral_exact: expected an ordinary interval-integral equality or inequality"
    exactIntegralAttempt parsed

/-- Checked partition-search strategy used by the semantic router. -/
partial def integralSearchCore (startN maxN : Nat) : TacticM Unit := do
  let goal ← getMainGoal
  let goalType ← goal.getType
  if goalType.isAppOfArity ``And 2 then
    evalTactic (← `(tactic| constructor))
    let goals ← getGoals
    for subgoal in goals do
      setGoals [subgoal]
      integralSearchCore startN maxN
  else
    let some parsed ← parseNaturalIntegralGoal goalType
      | throwError "integral_search: expected an ordinary interval-integral inequality"
    numericalIntegralAttempt parsed startN maxN

syntax (name := integralExactTac) "integral_exact" : tactic

@[tactic integralExactTac]
unsafe def elabIntegralExact : Tactic := fun _ => integralExactCore

end LeanCert.Tactic
