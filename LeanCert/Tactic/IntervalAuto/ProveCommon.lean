/-
Copyright (c) 2024 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import Lean
import LeanCert.Core.Expr
import LeanCert.Core.IntervalRat.Basic
import LeanCert.Meta.ProveSupported
import LeanCert.Tactic.IntervalAuto.Types
import LeanCert.Tactic.IntervalAuto.Extract

/-!
# Common Proving Utilities

Shared utilities for proving bounds across all interval tactics.
-/

open Lean Meta Elab Tactic

namespace LeanCert.Tactic.Auto

open LeanCert.Core
open LeanCert.Meta

/-- Try to close a goal with a sequence of tactics -/
def tryCloseWith (tacs : List (TSyntax `tactic)) : TacticM Bool := do
  for tac in tacs do
    let savedState ← saveState
    try
      evalTactic tac
      if (← getGoals).isEmpty then
        return true
    catch _ =>
      restoreState savedState
  return false

/-- Standard tactics for closing side goals -/
def standardCloseTactics : TacticM (List (TSyntax `tactic)) := do
  return [
    ← `(tactic| rfl),
    ← `(tactic| norm_num),
    ← `(tactic| norm_cast),
    ← `(tactic| (norm_num; simp only [Rat.divInt_eq_div]; push_cast; rfl)),
    ← `(tactic| (simp only [Rat.divInt_eq_div]; push_cast; rfl)),
    ← `(tactic| (congr 1 <;> norm_num)),
    ← `(tactic| simp only [sq, pow_two, pow_succ, pow_zero, pow_one, one_mul, mul_one])
  ]

/-- Try to close the current goal using standard tactics -/
def tryCloseGoal : TacticM Bool := do
  let tacs ← standardCloseTactics
  tryCloseWith tacs

/-- Close all remaining side goals -/
def closeAllSideGoals (tacticName : String) : TacticM Unit := do
  let goals ← getGoals
  for g in goals do
    setGoals [g]
    if ← tryCloseGoal then
      continue
    else
      logWarning m!"{tacticName}: Could not close side goal: {← g.getType}"

/-- Extract rational bound from possible coercion -/
def extractRatBound (bound : Lean.Expr) : TacticM Lean.Expr := do
  let fn := bound.getAppFn
  let args := bound.getAppArgs

  -- Check for Rat.cast (which is what ↑ becomes for ℚ → ℝ)
  if fn.isConstOf ``Rat.cast then
    if args.size > 0 then
      return args.back!
    else
      throwError "Unexpected Rat.cast structure"
  else if fn.isConstOf ``RatCast.ratCast then
    if args.size > 0 then
      return args.back!
    else
      throwError "Unexpected RatCast.ratCast structure"
  else
    let boundTy ← inferType bound
    if boundTy.isConstOf ``Rat then
      return bound
    else
      if let some q ← extractRatFromReal bound then
        return toExpr q
      else
        let boundReduced ← whnf bound
        let fnReduced := boundReduced.getAppFn
        if fnReduced.isConstOf ``Rat.cast || fnReduced.isConstOf ``RatCast.ratCast then
          let argsReduced := boundReduced.getAppArgs
          if argsReduced.size > 0 then
            return argsReduced.back!
        throwError m!"Cannot extract rational from bound: {bound}\n\n\
                      This happens when the bound contains non-computable constants.\n\
                      Suggestions:\n\
                      • Use a rational approximation\n\
                      • Use interval_decide for point inequalities with transcendentals"

/-- Try to extract AST from an Expr.eval application, or reify if it's a raw expression -/
def getAst (func : Lean.Expr) : TacticM Lean.Expr := do
  lambdaTelescope func fun _vars body => do
    let fn := body.getAppFn
    if fn.isConstOf ``LeanCert.Core.Expr.eval then
      let args := body.getAppArgs
      if args.size ≥ 2 then
        return args[1]!
      else
        throwError m!"Unexpected Expr.eval application structure.\n\
                      Expected: Expr.eval env ast\n\
                      Got {args.size} arguments: {args.toList}"
    else
      reify func

/-- Get support proof for an AST, returning (proof, useWithInv) -/
def getSupportProof (ast : Lean.Expr) : TacticM (Lean.Expr × Bool) := do
  -- First try ExprSupportedCore (simpler, works for most cases)
  try
    let proof ← mkSupportedCoreProof ast
    return (proof, false)
  catch _ =>
    -- Fall back to ExprSupportedWithInv (handles log/inv)
    let proof ← mkSupportedWithInvProof ast
    return (proof, true)

/-- Build a Box expression (List IntervalRat) from an array of VarIntervalInfo -/
def mkBoxExpr (infos : Array VarIntervalInfo) : MetaM Lean.Expr := do
  let intervalRatType := Lean.mkConst ``IntervalRat
  let intervals := infos.map (·.intervalRat)
  mkListLit intervalRatType intervals.toList

/-- Check if a certificate check will succeed (without throwing) -/
def certCheckSucceeds (checkFn : Lean.Expr) : TacticM Bool := do
  let certTy ← mkAppM ``Eq #[checkFn, mkConst ``Bool.true]
  let certGoal ← mkFreshExprMVar certTy
  let certGoalId := certGoal.mvarId!
  let savedState ← saveState
  try
    setGoals [certGoalId]
    evalTactic (← `(tactic| native_decide))
    restoreState savedState
    return true
  catch _ =>
    restoreState savedState
    return false

/-- Extract bounds from IntervalInfo for subdivision -/
def getSubdivBounds (intervalInfo : IntervalInfo) :
    TacticM (Option (ℚ × ℚ × Lean.Expr × Lean.Expr × Lean.Expr × Bool)) := do
  match intervalInfo.fromSetIcc with
  | some (lo, hi, loRatExpr, hiRatExpr, leProof, _origLo, _origHi) =>
    return some (lo, hi, loRatExpr, hiRatExpr, leProof, true)
  | none =>
    try
      let intervalVal ← unsafe evalExpr IntervalRat (mkConst ``IntervalRat) intervalInfo.intervalRat
      let lo := intervalVal.lo
      let hi := intervalVal.hi
      let loRatExpr := toExpr lo
      let hiRatExpr := toExpr hi
      let leProofTy ← mkAppM ``LE.le #[loRatExpr, hiRatExpr]
      let leProof ← mkDecideProof leProofTy
      return some (lo, hi, loRatExpr, hiRatExpr, leProof, false)
    catch _ =>
      return none

/-- Extract a rational literal from an expression -/
def getLiteral? (e : Lean.Expr) : TacticM (Option ℚ) := do
  try
    let val ← unsafe evalExpr ℚ (mkConst ``Rat) e
    return some val
  catch _ =>
    return none

end LeanCert.Tactic.Auto
