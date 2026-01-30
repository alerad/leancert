/-
Copyright (c) 2024 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import Lean
import LeanCert.Tactic.IntervalAuto.Types
import LeanCert.Tactic.IntervalAuto.Norm
import LeanCert.Tactic.IntervalAuto.Extract
import LeanCert.Tactic.IntervalAuto.Parse
import LeanCert.Tactic.IntervalAuto.Diagnostic
import LeanCert.Tactic.IntervalAuto.ProveCommon
import LeanCert.Meta.ProveSupported
import LeanCert.Meta.ToExpr
import LeanCert.Validity.Bounds

/-!
# Main Interval Bound Tactic Implementation

This module provides the core `interval_bound` / `certify_bound` tactic implementation
for proving univariate bound goals:
- `∀ x ∈ I, f x ≤ c`
- `∀ x ∈ I, c ≤ f x`
- `∀ x ∈ I, f x < c`
- `∀ x ∈ I, c < f x`

## Main definitions

* `intervalBoundCore` - Core implementation of the interval bound tactic
* `certify_bound` - User-facing tactic with adaptive precision
* `interval_bound` - Backward-compatible alias for `certify_bound`
-/

open Lean Meta Elab Tactic Term

namespace LeanCert.Tactic.Auto

open LeanCert.Meta
open LeanCert.Core
open LeanCert.Engine
open LeanCert.Validity

/-- The main interval_bound tactic implementation -/
def intervalBoundCore (taylorDepth : Nat) : TacticM Unit := do
  intervalNormCore
  -- Pre-process: convert ≥ to ≤ and > to < for uniform handling
  -- First intro variables to get into the body of the forall
  let preprocessed ← do
    try
      evalTactic (← `(tactic| intro _x _hx; simp only [ge_iff_le, gt_iff_lt]; revert _x _hx))
      pure true
    catch e =>
      trace[interval_decide] "Forall preprocessing failed: {e.toMessageData}"
      try
        evalTactic (← `(tactic| simp only [ge_iff_le, gt_iff_lt]))
        pure true
      catch _ => pure false
  if preprocessed then
    trace[interval_decide] "Preprocessing applied ≥/> → ≤/<"

  -- Pre-process: normalize powers (x^2 → x*x, x^3 → x*x*x, etc.)
  try
    evalTactic (← `(tactic| simp only [sq, pow_two, pow_succ, pow_zero, pow_one, one_mul, mul_one] at *))
  catch _ => pure ()

  -- Check if the goal was already solved by simplification (e.g., x^0 ≤ 1 → 1 ≤ 1)
  let goals ← getGoals
  if goals.isEmpty then
    return

  let goal ← getMainGoal
  let goalType ← goal.getType

  -- Parse the goal
  let some boundGoal ← parseBoundGoal goalType
    | do
      -- If parsing fails, try to solve trivially (e.g., after x^0 → 1, goal becomes 1 ≤ 1)
      try
        evalTactic (← `(tactic| intro _ _; norm_num))
        return
      catch _ => pure ()
      -- Debug: show the goal structure
      let goalWhnf ← whnf goalType
      throwError "interval_bound: Could not parse goal as a bound. Expected:\n\
                  • ∀ x ∈ I, f x ≤ c\n\
                  • ∀ x ∈ I, c ≤ f x\n\
                  • ∀ x ∈ I, f x < c\n\
                  • ∀ x ∈ I, c < f x\n\
                  \nGoal type: {goalType}\n\
                  Goal (whnf): {goalWhnf}"

  match boundGoal with
  | .forallLe _name interval func bound =>
    proveForallLe goal interval func bound taylorDepth
  | .forallGe _name interval func bound =>
    proveForallGe goal interval func bound taylorDepth
  | .forallLt _name interval func bound =>
    proveForallLt goal interval func bound taylorDepth
  | .forallGt _name interval func bound =>
    proveForallGt goal interval func bound taylorDepth

where
  /-- Try to extract the rational from a bound expression (possibly coerced to ℝ) -/
  extractRatBound (bound : Lean.Expr) : TacticM Lean.Expr := do
    let fn := bound.getAppFn
    let args := bound.getAppArgs

    -- Check for Rat.cast (which is what ↑ becomes for ℚ → ℝ)
    if fn.isConstOf ``Rat.cast then
      if args.size > 0 then
        return args.back!
      else
        throwError "Unexpected Rat.cast structure"
    else
      -- Check for the RatCast.ratCast form (the actual implementation)
      if fn.isConstOf ``RatCast.ratCast then
        if args.size > 0 then
          return args.back!
        else
          throwError "Unexpected RatCast.ratCast structure"
      else
        -- Check if the type is already ℚ
        let boundTy ← inferType bound
        if boundTy.isConstOf ``Rat then
          return bound
        else
          -- Try to extract a rational value using our helper
          if let some q ← extractRatFromReal bound then
            return toExpr q
          else
            -- Last resort: try to see if this is a reducible form
            let boundReduced ← whnf bound
            let fnReduced := boundReduced.getAppFn
            if fnReduced.isConstOf ``Rat.cast || fnReduced.isConstOf ``RatCast.ratCast then
              let argsReduced := boundReduced.getAppArgs
              if argsReduced.size > 0 then
                return argsReduced.back!
              else
                throwError "Unexpected reduced coercion structure"
            else
              throwError m!"Cannot extract rational from bound: {bound}\n\
                            Type: {boundTy}\n\n\
                            This happens when the bound contains non-computable constants\n\
                            (e.g., Real.pi, Real.sqrt 2, or complex expressions).\n\
                            Suggestions:\n\
                            • Use a rational approximation (e.g., 3.15 instead of Real.pi)\n\
                            • Use interval_decide for point inequalities with transcendentals"

  /-- Try to extract AST from an Expr.eval application, or reify if it's a raw expression -/
  getAst (func : Lean.Expr) : TacticM Lean.Expr := do
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

  /-- Try to generate ExprSupportedCore proof, falling back to ExprSupportedWithInv if needed. -/
  getSupportProof (ast : Lean.Expr) : TacticM (Lean.Expr × Bool) := do
    try
      let proof ← mkSupportedCoreProof ast
      return (proof, false)
    catch _ =>
      let proof ← mkSupportedWithInvProof ast
      return (proof, true)

  /-- Helper: try a tactic and check if goal was closed -/
  tryClose (tac : TacticM Unit) : TacticM Bool := do
    try
      tac
      return (← getGoals).isEmpty
    catch _ => return false

  /-- Close side goals after convert -/
  closeSideGoals : TacticM Unit := do
    let goals ← getGoals
    for g in goals do
      setGoals [g]
      if ← tryClose (evalTactic (← `(tactic| norm_num; simp only [Rat.divInt_eq_div]; push_cast; rfl))) then continue
      if ← tryClose (evalTactic (← `(tactic| norm_num; simp only [Rat.divInt_eq_div]; push_cast; ring))) then continue
      if ← tryClose (evalTactic (← `(tactic| rfl))) then continue
      if ← tryClose (evalTactic (← `(tactic| congr 1 <;> norm_num))) then continue
      if ← tryClose (evalTactic (← `(tactic| norm_cast))) then continue
      if ← tryClose (evalTactic (← `(tactic| norm_num))) then continue
      if ← tryClose (evalTactic (← `(tactic| simp only [sq, pow_two, pow_succ, pow_zero, pow_one, one_mul, mul_one]))) then continue
      if ← tryClose (evalTactic (← `(tactic| simp only [LeanCert.Core.Expr.eval_add, LeanCert.Core.Expr.eval_mul, LeanCert.Core.Expr.eval_neg, LeanCert.Core.Expr.eval_const, LeanCert.Core.Expr.eval_var, LeanCert.Core.Expr.eval_sin, LeanCert.Core.Expr.eval_cos, LeanCert.Core.Expr.eval_exp, LeanCert.Core.Expr.eval_sub]; ring))) then continue
      if ← tryClose (evalTactic (← `(tactic| simp only [LeanCert.Core.Expr.eval_add, LeanCert.Core.Expr.eval_mul, LeanCert.Core.Expr.eval_neg, LeanCert.Core.Expr.eval_const, LeanCert.Core.Expr.eval_var, LeanCert.Core.Expr.eval_sin, LeanCert.Core.Expr.eval_cos, LeanCert.Core.Expr.eval_exp, LeanCert.Core.Expr.eval_sub]; push_cast; ring))) then continue
      if ← tryClose (evalTactic (← `(tactic| simp only [Rat.divInt_eq_div]; push_cast; rfl))) then continue
      if ← tryClose (evalTactic (← `(tactic| simp [Rat.divInt_eq_div]))) then continue
      if ← tryClose (evalTactic (← `(tactic| push_cast; rfl))) then continue
      if ← tryClose (evalTactic (← `(tactic| simp only [Rat.cast_natCast, Rat.cast_intCast, Nat.cast_ofNat, Int.cast_ofNat, NNRat.cast_natCast]))) then continue
      logWarning m!"interval_bound: Could not close side goal: {← g.getType}"

  /-- Prove ∀ x ∈ I, f x ≤ c -/
  proveForallLe (goal : MVarId) (intervalInfo : IntervalInfo) (func bound : Lean.Expr)
      (taylorDepth : Nat) : TacticM Unit := do
    goal.withContext do
      discard <| tryNormalizeGoalToIcc
      let goal ← getMainGoal
      let ast ← getAst func
      let boundRat ← extractRatBound bound
      let (supportProof, useWithInv) ← getSupportProof ast
      let cfgExpr ← mkAppM ``EvalConfig.mk #[toExpr taylorDepth]

      match intervalInfo.fromSetIcc with
        | some (_lo, _hi, loRatExpr, hiRatExpr, leProof, _origLo, _origHi) =>
          let proof ← if useWithInv then
            mkAppM ``verify_upper_bound_Icc_withInv #[ast, supportProof, loRatExpr, hiRatExpr, leProof, boundRat]
          else
            mkAppM ``verify_upper_bound_Icc_core #[ast, supportProof, loRatExpr, hiRatExpr, leProof, boundRat, cfgExpr]

          setGoals [goal]
          try
            let newGoals ← goal.apply proof
            setGoals newGoals
            for g in newGoals do
              setGoals [g]
              if ← tryClose (evalTactic (← `(tactic| rfl))) then continue
              evalTactic (← `(tactic| native_decide))
          catch _ =>
            setGoals [goal]
            let intervalRat ← mkAppM ``IntervalRat.mk #[loRatExpr, hiRatExpr, leProof]
            let checkExpr ← if useWithInv then
              mkAppM ``LeanCert.Validity.checkUpperBoundWithInv #[ast, intervalRat, boundRat]
            else
              mkAppM ``LeanCert.Validity.checkUpperBound #[ast, intervalRat, boundRat, cfgExpr]
            let certTy ← mkAppM ``Eq #[checkExpr, mkConst ``Bool.true]
            let certGoal ← mkFreshExprMVar certTy
            let certGoalId := certGoal.mvarId!
            setGoals [certGoalId]
            evalTactic (← `(tactic| native_decide))
            let certProof := certGoal
            let conclusionProof ← mkAppM' proof #[certProof]
            let conclusionTerm ← Lean.Elab.Term.exprToSyntax conclusionProof
            setGoals [goal]
            evalTactic (← `(tactic| convert ($conclusionTerm) using 3))
            closeSideGoals

        | none =>
          let proof ← if useWithInv then
            mkAppM ``verify_upper_bound_withInv #[ast, supportProof, intervalInfo.intervalRat, boundRat]
          else
            mkAppM ``verify_upper_bound #[ast, supportProof, intervalInfo.intervalRat, boundRat, cfgExpr]
          setGoals [goal]
          try
            let newGoals ← goal.apply proof
            setGoals newGoals
            for g in newGoals do
              setGoals [g]
              evalTactic (← `(tactic| native_decide))
          catch _ =>
            setGoals [goal]
            let checkExpr ← if useWithInv then
              mkAppM ``LeanCert.Validity.checkUpperBoundWithInv #[ast, intervalInfo.intervalRat, boundRat]
            else
              mkAppM ``LeanCert.Validity.checkUpperBound #[ast, intervalInfo.intervalRat, boundRat, cfgExpr]
            let certTy ← mkAppM ``Eq #[checkExpr, mkConst ``Bool.true]
            let certGoal ← mkFreshExprMVar certTy
            let certGoalId := certGoal.mvarId!
            setGoals [certGoalId]
            evalTactic (← `(tactic| native_decide))
            let certProof := certGoal
            let conclusionProof ← mkAppM' proof #[certProof]
            let conclusionTerm ← Lean.Elab.Term.exprToSyntax conclusionProof
            setGoals [goal]
            evalTactic (← `(tactic| convert ($conclusionTerm) using 3))
            closeSideGoals

  /-- Prove ∀ x ∈ I, c ≤ f x -/
  proveForallGe (goal : MVarId) (intervalInfo : IntervalInfo) (func bound : Lean.Expr)
      (taylorDepth : Nat) : TacticM Unit := do
    goal.withContext do
      discard <| tryNormalizeGoalToIcc
      let goal ← getMainGoal
      let ast ← getAst func
      let boundRat ← extractRatBound bound
      let (supportProof, useWithInv) ← getSupportProof ast
      let cfgExpr ← mkAppM ``EvalConfig.mk #[toExpr taylorDepth]

      match intervalInfo.fromSetIcc with
        | some (_lo, _hi, loRatExpr, hiRatExpr, leProof, _origLo, _origHi) =>
          let proof ← if useWithInv then
            mkAppM ``verify_lower_bound_Icc_withInv #[ast, supportProof, loRatExpr, hiRatExpr, leProof, boundRat]
          else
            mkAppM ``verify_lower_bound_Icc_core #[ast, supportProof, loRatExpr, hiRatExpr, leProof, boundRat, cfgExpr]

          setGoals [goal]
          try
            let newGoals ← goal.apply proof
            setGoals newGoals
            for g in newGoals do
              setGoals [g]
              if ← tryClose (evalTactic (← `(tactic| rfl))) then continue
              evalTactic (← `(tactic| native_decide))
          catch _ =>
            setGoals [goal]
            let intervalRat ← mkAppM ``IntervalRat.mk #[loRatExpr, hiRatExpr, leProof]
            let checkExpr ← if useWithInv then
              mkAppM ``LeanCert.Validity.checkLowerBoundWithInv #[ast, intervalRat, boundRat]
            else
              mkAppM ``LeanCert.Validity.checkLowerBound #[ast, intervalRat, boundRat, cfgExpr]
            let certTy ← mkAppM ``Eq #[checkExpr, mkConst ``Bool.true]
            let certGoal ← mkFreshExprMVar certTy
            let certGoalId := certGoal.mvarId!
            setGoals [certGoalId]
            evalTactic (← `(tactic| native_decide))
            let certProof := certGoal
            let conclusionProof ← mkAppM' proof #[certProof]
            let conclusionTerm ← Lean.Elab.Term.exprToSyntax conclusionProof
            setGoals [goal]
            evalTactic (← `(tactic| convert ($conclusionTerm) using 3))
            closeSideGoals

        | none =>
          let proof ← if useWithInv then
            mkAppM ``verify_lower_bound_withInv #[ast, supportProof, intervalInfo.intervalRat, boundRat]
          else
            mkAppM ``verify_lower_bound #[ast, supportProof, intervalInfo.intervalRat, boundRat, cfgExpr]
          setGoals [goal]
          try
            let newGoals ← goal.apply proof
            setGoals newGoals
            for g in newGoals do
              setGoals [g]
              evalTactic (← `(tactic| native_decide))
          catch _ =>
            setGoals [goal]
            let checkExpr ← if useWithInv then
              mkAppM ``LeanCert.Validity.checkLowerBoundWithInv #[ast, intervalInfo.intervalRat, boundRat]
            else
              mkAppM ``LeanCert.Validity.checkLowerBound #[ast, intervalInfo.intervalRat, boundRat, cfgExpr]
            let certTy ← mkAppM ``Eq #[checkExpr, mkConst ``Bool.true]
            let certGoal ← mkFreshExprMVar certTy
            let certGoalId := certGoal.mvarId!
            setGoals [certGoalId]
            evalTactic (← `(tactic| native_decide))
            let certProof := certGoal
            let conclusionProof ← mkAppM' proof #[certProof]
            let conclusionTerm ← Lean.Elab.Term.exprToSyntax conclusionProof
            setGoals [goal]
            evalTactic (← `(tactic| convert ($conclusionTerm) using 3))
            closeSideGoals

  /-- Prove ∀ x ∈ I, f x < c -/
  proveForallLt (goal : MVarId) (intervalInfo : IntervalInfo) (func bound : Lean.Expr)
      (taylorDepth : Nat) : TacticM Unit := do
    goal.withContext do
      discard <| tryNormalizeGoalToIcc
      let goal ← getMainGoal
      let ast ← getAst func
      let boundRat ← extractRatBound bound
      let (supportProof, useWithInv) ← getSupportProof ast
      let cfgExpr ← mkAppM ``EvalConfig.mk #[toExpr taylorDepth]

      match intervalInfo.fromSetIcc with
        | some (_lo, _hi, loRatExpr, hiRatExpr, leProof, _origLo, _origHi) =>
          let proof ← if useWithInv then
            mkAppM ``verify_strict_upper_bound_Icc_withInv #[ast, supportProof, loRatExpr, hiRatExpr, leProof, boundRat]
          else
            mkAppM ``verify_strict_upper_bound_Icc_core #[ast, supportProof, loRatExpr, hiRatExpr, leProof, boundRat, cfgExpr]

          setGoals [goal]
          try
            let newGoals ← goal.apply proof
            setGoals newGoals
            for g in newGoals do
              setGoals [g]
              if ← tryClose (evalTactic (← `(tactic| rfl))) then continue
              evalTactic (← `(tactic| native_decide))
          catch _ =>
            setGoals [goal]
            let intervalRat ← mkAppM ``IntervalRat.mk #[loRatExpr, hiRatExpr, leProof]
            let checkExpr ← if useWithInv then
              mkAppM ``LeanCert.Validity.checkStrictUpperBoundWithInv #[ast, intervalRat, boundRat]
            else
              mkAppM ``LeanCert.Validity.checkStrictUpperBound #[ast, intervalRat, boundRat, cfgExpr]
            let certTy ← mkAppM ``Eq #[checkExpr, mkConst ``Bool.true]
            let certGoal ← mkFreshExprMVar certTy
            let certGoalId := certGoal.mvarId!
            setGoals [certGoalId]
            evalTactic (← `(tactic| native_decide))
            let certProof := certGoal
            let conclusionProof ← mkAppM' proof #[certProof]
            let conclusionTerm ← Lean.Elab.Term.exprToSyntax conclusionProof
            setGoals [goal]
            evalTactic (← `(tactic| convert ($conclusionTerm) using 3))
            closeSideGoals

        | none =>
          let proof ← if useWithInv then
            mkAppM ``verify_strict_upper_bound_withInv #[ast, supportProof, intervalInfo.intervalRat, boundRat]
          else
            mkAppM ``verify_strict_upper_bound #[ast, supportProof, intervalInfo.intervalRat, boundRat, cfgExpr]
          let newGoals ← goal.apply proof
          setGoals newGoals
          for g in newGoals do
            setGoals [g]
            try evalTactic (← `(tactic| native_decide))
            catch _ =>
              try evalTactic (← `(tactic| norm_cast))
              catch _ => evalTactic (← `(tactic| simp only [Rat.cast_zero, Rat.cast_one, Rat.cast_intCast, Rat.cast_natCast]))

  /-- Prove ∀ x ∈ I, c < f x -/
  proveForallGt (goal : MVarId) (intervalInfo : IntervalInfo) (func bound : Lean.Expr)
      (taylorDepth : Nat) : TacticM Unit := do
    goal.withContext do
      discard <| tryNormalizeGoalToIcc
      let goal ← getMainGoal
      let ast ← getAst func
      let boundRat ← extractRatBound bound
      let (supportProof, useWithInv) ← getSupportProof ast
      let cfgExpr ← mkAppM ``EvalConfig.mk #[toExpr taylorDepth]

      match intervalInfo.fromSetIcc with
        | some (_lo, _hi, loRatExpr, hiRatExpr, leProof, _origLo, _origHi) =>
          let proof ← if useWithInv then
            mkAppM ``verify_strict_lower_bound_Icc_withInv #[ast, supportProof, loRatExpr, hiRatExpr, leProof, boundRat]
          else
            mkAppM ``verify_strict_lower_bound_Icc_core #[ast, supportProof, loRatExpr, hiRatExpr, leProof, boundRat, cfgExpr]

          setGoals [goal]
          try
            let newGoals ← goal.apply proof
            setGoals newGoals
            for g in newGoals do
              setGoals [g]
              if ← tryClose (evalTactic (← `(tactic| rfl))) then continue
              evalTactic (← `(tactic| native_decide))
          catch _ =>
            setGoals [goal]
            let intervalRat ← mkAppM ``IntervalRat.mk #[loRatExpr, hiRatExpr, leProof]
            let checkExpr ← if useWithInv then
              mkAppM ``LeanCert.Validity.checkStrictLowerBoundWithInv #[ast, intervalRat, boundRat]
            else
              mkAppM ``LeanCert.Validity.checkStrictLowerBound #[ast, intervalRat, boundRat, cfgExpr]
            let certTy ← mkAppM ``Eq #[checkExpr, mkConst ``Bool.true]
            let certGoal ← mkFreshExprMVar certTy
            let certGoalId := certGoal.mvarId!
            setGoals [certGoalId]
            evalTactic (← `(tactic| native_decide))
            let certProof := certGoal
            let conclusionProof ← mkAppM' proof #[certProof]
            let conclusionTerm ← Lean.Elab.Term.exprToSyntax conclusionProof
            setGoals [goal]
            evalTactic (← `(tactic| convert ($conclusionTerm) using 3))
            closeSideGoals

        | none =>
          let proof ← if useWithInv then
            mkAppM ``verify_strict_lower_bound_withInv #[ast, supportProof, intervalInfo.intervalRat, boundRat]
          else
            mkAppM ``verify_strict_lower_bound #[ast, supportProof, intervalInfo.intervalRat, boundRat, cfgExpr]
          let newGoals ← goal.apply proof
          setGoals newGoals
          for g in newGoals do
            setGoals [g]
            try evalTactic (← `(tactic| native_decide))
            catch _ =>
              try evalTactic (← `(tactic| norm_cast))
              catch _ => evalTactic (← `(tactic| simp only [Rat.cast_zero, Rat.cast_one, Rat.cast_intCast, Rat.cast_natCast]))

/-- The certify_bound tactic.

    Automatically proves bounds on expressions using interval arithmetic.

    Usage:
    - `certify_bound` - uses adaptive precision (tries depths 10, 15, 20, 25, 30)
    - `certify_bound 20` - uses fixed Taylor depth of 20

    Supports goals of the form:
    - `∀ x ∈ I, f x ≤ c`
    - `∀ x ∈ I, c ≤ f x`
    - `∀ x ∈ I, f x < c`
    - `∀ x ∈ I, c < f x`

    Note: `interval_bound` is an alias for backward compatibility.
-/
elab "certify_bound" depth:(num)? : tactic => do
  match depth with
  | some n =>
    intervalBoundCore n.getNat
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
    | some e =>
      restoreState goalState
      -- Diagnostics available in full IntervalAuto.lean
      let goal ← getMainGoal
      let goalType ← goal.getType
      let diagReport ← mkDiagnosticReport "certify_bound" goalType "all depths failed"
      throwError m!"{e.toMessageData}\n\n{diagReport}\n\nTry: certify_bound 50"
    | none => throwError "certify_bound: All precision levels failed"

/-- Backward-compatible alias for certify_bound -/
macro "interval_bound" depth:(num)? : tactic => `(tactic| certify_bound $[$depth]?)

end LeanCert.Tactic.Auto
