/-
Copyright (c) 2024 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import Lean
import LeanCert.Tactic.IntervalAuto.Types
import LeanCert.Tactic.IntervalAuto.Parse

/-!
# Diagnostic Utilities for Interval Tactics

Error reporting, shadow diagnostics, and helpful error messages for interval tactics.
-/

open Lean Meta

namespace LeanCert.Tactic.Auto

/-- Extract interval bounds as rationals for diagnostics -/
def extractIntervalBoundsForDiag (intervalInfo : IntervalInfo) : Option (ℚ × ℚ) :=
  match intervalInfo.fromSetIcc with
  | some (lo, hi, _, _, _, _, _) => some (lo, hi)
  | none => none

/-- Format context of the goal for diagnostics -/
def formatGoalContext (goalType : Lean.Expr) : MetaM MessageData := do
  return m!"Goal: {goalType}"

/-- Count foralls in an expression -/
partial def countForallsAux (e : Lean.Expr) (acc : Nat) : MetaM Nat := do
  let e ← whnf e
  if e.isForall then
    let .forallE _ _ body _ := e | return acc
    countForallsAux body (acc + 1)
  else
    return acc

/-- Try to find the comparison in the body -/
partial def findComparisonAux (e : Lean.Expr) : MetaM (Option String) := do
  let e ← whnf e
  if e.isForall then
    let .forallE _ _ body _ := e | return none
    findComparisonAux body
  else
    let fn := e.getAppFn
    if fn.isConstOf ``LE.le then return some "≤"
    if fn.isConstOf ``GE.ge then return some "≥"
    if fn.isConstOf ``LT.lt then return some "<"
    if fn.isConstOf ``GT.gt then return some ">"
    return none

/-- Analyze goal structure for diagnostics -/
def analyzeGoalStructure (goalType : Lean.Expr) : MetaM MessageData := do
  let numForalls ← countForallsAux goalType 0
  let comparison ← findComparisonAux goalType
  let compStr := match comparison with
    | some c => c
    | none => "(not found)"
  return m!"Structure:\n\
            • Quantifiers: {numForalls}\n\
            • Comparison: {compStr}"

/-- Suggest next actions based on analysis -/
def suggestNextActions (tacticName : String) (goalType : Lean.Expr) : MetaM MessageData := do
  let numForalls ← countForallsAux goalType 0
  let suggestions := if numForalls == 0 then
    m!"• Try `interval_decide` for point inequalities\n\
       • Or manually write `have h : ∀ x ∈ Set.Icc a b, ... := by {tacticName}`"
  else if numForalls == 1 then
    m!"• Ensure the goal has form: ∀ x ∈ I, f(x) ≤ c  (or ≥, <, >)\n\
       • Check that bounds are literal rationals\n\
       • Try `simp only [ge_iff_le, gt_iff_lt]` first"
  else
    m!"• For multivariate goals (2+ variables), use `multivariate_bound`\n\
       • Ensure all domains are Set.Icc with rational bounds\n\
       • Check that all bounds are extractable as rationals"
  return suggestions

/-- Generate a diagnostic report for parse errors -/
def mkDiagnosticReport (tacticName : String) (goalType : Lean.Expr) (stage : String)
    (hint : Option MessageData := none) : MetaM MessageData := do
  let context ← formatGoalContext goalType
  let goalStructure ← analyzeGoalStructure goalType
  let suggestions ← suggestNextActions tacticName goalType
  let hintMsg := match hint with
    | some h => m!"\n{h}\n"
    | none => ""
  return m!"━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━\n\
            {tacticName} diagnostic ({stage})\n\
            ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━\n\
            {context}\n\n\
            {goalStructure}\n{hintMsg}\n\
            Suggestions:\n{suggestions}"

end LeanCert.Tactic.Auto
