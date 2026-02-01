/-
Copyright (c) 2024 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Tactic.IntervalAuto.Basic
import LeanCert.Tactic.IntervalAuto.Bound
import LeanCert.Tactic.IntervalAuto.Multivariate
import LeanCert.Tactic.IntervalAuto.OptBound
import LeanCert.Tactic.IntervalAuto.RootBound
import LeanCert.Tactic.IntervalAuto.PointIneq
import LeanCert.Tactic.IntervalAuto.Subdiv
import LeanCert.Tactic.IntervalAuto.Adaptive

/-!
# Automated Interval Arithmetic Tactics

This module re-exports the interval arithmetic tactic suite:

* `interval_bound` - Prove bounds using interval arithmetic
* `interval_decide` - Prove point inequalities
* `interval_auto` - Unified entry point (recommended)
* `multivariate_bound` - Prove bounds on multivariate expressions
* `opt_bound` - Prove bounds using global optimization
* `root_bound` - Prove non-existence of roots
* `interval_bound_subdiv` - Prove bounds with subdivision
* `interval_bound_adaptive` - Prove bounds with adaptive precision

The infrastructure (types, parsing, normalization, extraction, diagnostics,
common proving utilities) lives in `LeanCert.Tactic.IntervalAuto.Basic`.
-/

open Lean Meta Elab Tactic

namespace LeanCert.Tactic.Auto

open LeanCert.Tactic.Auto

/-- Check if goal looks like a point inequality or connective of point inequalities (not quantified) -/
private partial def isPointInequality (goal : Lean.Expr) : MetaM Bool := do
  -- A point inequality is ≤, <, ≥, > without a leading ∀
  if goal.isForall then
    return false
  -- Check if it's a conjunction - recursively check both sides
  if goal.isAppOfArity ``And 2 then
    let args := goal.getAppArgs
    let left ← isPointInequality args[0]!
    let right ← isPointInequality args[1]!
    return left && right
  -- Check if it's a disjunction - recursively check both sides
  if goal.isAppOfArity ``Or 2 then
    let args := goal.getAppArgs
    let left ← isPointInequality args[0]!
    let right ← isPointInequality args[1]!
    return left || right  -- For OR, at least one side needs to be provable
  -- Check if it's a comparison
  let some (_, _, _, _) ← parsePointIneq goal
    | return false
  return true

/-- Unified tactic that handles both point inequalities and quantified bounds.
    - `interval_auto` - uses adaptive precision
    - `interval_auto 20` - uses fixed Taylor depth of 20

    This is the recommended entry point for interval arithmetic proofs.
-/
elab "interval_auto" depth:(num)? : tactic => do
  let goal ← getMainGoal
  let goalType ← goal.getType
  let isPoint ← isPointInequality goalType
  if isPoint then
    trace[interval_decide] "interval_auto: detected point inequality, using interval_decide"
    intervalDecideWithConnectives (depth.map (·.getNat))
  else
    trace[interval_decide] "interval_auto: detected quantified goal, using interval_bound"
    match depth with
    | some n => intervalBoundCore n.getNat
    | none =>
      let depths := [10, 15, 20, 25, 30]
      let goalState ← saveState
      let mut lastError : Option Exception := none
      for d in depths do
        try
          restoreState goalState
          trace[interval_decide] "Trying Taylor depth {d}..."
          intervalBoundCore d
          trace[interval_decide] "Success with Taylor depth {d}"
          return
        catch e =>
          lastError := some e
          continue
      match lastError with
      | some e => throw e
      | none => throwError "interval_auto: All precision levels failed"

end LeanCert.Tactic.Auto
