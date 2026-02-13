/-
Copyright (c) 2024 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Tactic.IntervalAuto.Basic
import LeanCert.Validity.Bounds
import LeanCert.Engine.Eval.Core
import LeanCert.Engine.Optimization.BoundVerify

/-!
# Main Interval Bound Tactics

Core interval bound proving: `intervalBoundCore`, `certify_bound`, `interval_bound`.
Also includes shadow diagnostics for error reporting.
-/

open Lean Meta Elab Tactic Term

namespace LeanCert.Tactic.Auto

open LeanCert.Meta
open LeanCert.Core
open LeanCert.Engine
open LeanCert.Validity

/-! ## Diagnostic Helpers for Shadow Computation -/

/-- Reify a function expression to actual AST value for diagnostics -/
private def reifyFuncForDiag (func : Lean.Expr) : TacticM LeanCert.Core.Expr := do
  lambdaTelescope func fun _vars body => do
    let fn := body.getAppFn
    if fn.isConstOf ``LeanCert.Core.Expr.eval then
      let args := body.getAppArgs
      if args.size ≥ 2 then
        let astExpr := args[1]!
        let astVal ← unsafe evalExpr LeanCert.Core.Expr (mkConst ``LeanCert.Core.Expr) astExpr
        return astVal
      else
        throwError "Unexpected Expr.eval structure in diagnostic"
    else
      let astExpr ← reify func
      let astVal ← unsafe evalExpr LeanCert.Core.Expr (mkConst ``LeanCert.Core.Expr) astExpr
      return astVal

/-- Run shadow computation to diagnose why a proof failed -/
def runShadowDiagnostic (boundGoal : Option BoundGoal) (_goalType : Lean.Expr) : TacticM MessageData := do
  let some bg := boundGoal | return m!"(Could not parse goal for diagnostics)"

  match bg with
  | .forallLe _ interval func bound
  | .forallGe _ interval func bound
  | .forallLt _ interval func bound
  | .forallGt _ interval func bound =>
    try
      -- Extract interval bounds
      let some (lo, hi) := extractIntervalBoundsForDiag interval
        | return m!"(Could not extract interval bounds for diagnostics)"
      let I : IntervalRat :=
        if hle : lo ≤ hi then ⟨lo, hi, hle⟩
        else ⟨0, 1, by native_decide⟩

      -- Reify function to actual AST value
      let ast ← reifyFuncForDiag func

      -- Evaluate with high precision
      let diagCfg : EvalConfig := { taylorDepth := 30 }
      let result := evalIntervalCore1 ast I diagCfg

      -- Extract bound as rational
      let limitOpt ← extractRatFromReal bound

      -- Format diagnostic based on goal type
      let isUpperBound := match bg with
        | .forallLe .. | .forallLt .. => true
        | .forallGe .. | .forallGt .. => false

      match limitOpt with
      | some limit =>
        if isUpperBound then
          -- For f(x) ≤ c, check if computed lower bound exceeds limit
          if result.lo > limit then
            return m!"❌ Diagnostic Analysis:\n\
                      Goal: f(x) ≤ {limit}\n\
                      Computed Range (depth 30): [{result.lo}, {result.hi}]\n\n\
                      • Mathematical Violation: Lower bound {result.lo} > limit {limit}.\n\
                      • The theorem is likely FALSE."
          else if result.hi > limit then
            return m!"⚠️ Diagnostic Analysis:\n\
                      Goal: f(x) ≤ {limit}\n\
                      Computed Range (depth 30): [{result.lo}, {result.hi}]\n\n\
                      • Precision Issue: Upper bound {result.hi} > limit {limit}.\n\
                      • Try: interval_bound 50 or subdivide the domain."
          else
            return m!"Diagnostic Analysis:\n\
                      Computed Range: [{result.lo}, {result.hi}] ≤ {limit}\n\
                      The proof failed for technical reasons (side goal closure, etc.)."
        else
          -- For c ≤ f(x), check if computed upper bound is below limit
          if result.hi < limit then
            return m!"❌ Diagnostic Analysis:\n\
                      Goal: {limit} ≤ f(x)\n\
                      Computed Range (depth 30): [{result.lo}, {result.hi}]\n\n\
                      • Mathematical Violation: Upper bound {result.hi} < limit {limit}.\n\
                      • The theorem is likely FALSE."
          else if result.lo < limit then
            return m!"⚠️ Diagnostic Analysis:\n\
                      Goal: {limit} ≤ f(x)\n\
                      Computed Range (depth 30): [{result.lo}, {result.hi}]\n\n\
                      • Precision Issue: Lower bound {result.lo} < limit {limit}.\n\
                      • Try: interval_bound 50 or subdivide the domain."
          else
            return m!"Diagnostic Analysis:\n\
                      Computed Range: [{result.lo}, {result.hi}] ≥ {limit}\n\
                      The proof failed for technical reasons (side goal closure, etc.)."
      | none =>
        return m!"Diagnostic Analysis:\n\
                  Computed Range (depth 30): [{result.lo}, {result.hi}]\n\
                  (Could not extract rational from bound for comparison)"
    catch e =>
      return m!"(Diagnostic computation failed: {e.toMessageData})"


/-! ## Main Tactic Implementation -/

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

  -- Pre-process: lightweight power cleanup after intervalNormCore.
  try
    evalTactic (← `(tactic| simp only [pow_zero, pow_one, one_mul, mul_one] at *))
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
  /-- Prove ∀ x ∈ I, f x ≤ c -/
  proveForallLe (goal : MVarId) (intervalInfo : IntervalInfo) (func bound : Lean.Expr)
      (taylorDepth : Nat) : TacticM Unit := do
    goal.withContext do
      discard <| tryNormalizeGoalToIcc
      let goal ← getMainGoal
      -- 1. Get AST (either from Expr.eval or by reifying)
      let ast ← getAst func

      -- 2. Extract rational bound from possible coercion
      let boundRat ← extractRatBound bound

      -- 3. Generate support proof (tries Core first, falls back to WithInv for log/inv)
      let (supportProof, useWithInv) ← getSupportProof ast

      -- 4. Build config expression
      let cfgExpr ← mkAppM ``EvalConfig.mk #[toExpr taylorDepth]

      -- 5. Apply appropriate theorem based on interval source and support type
      match intervalInfo.fromSetIcc with
        | some (_lo, _hi, loRatExpr, hiRatExpr, leProof, _origLo, _origHi) =>
          -- Choose theorem and arguments based on support type
          -- Note: WithInv theorems don't take a cfg parameter
          let proof ← if useWithInv then
            mkAppM ``verify_upper_bound_Icc_withInv #[ast, supportProof, loRatExpr, hiRatExpr, leProof, boundRat]
          else
            mkAppM ``verify_upper_bound_Icc_core #[ast, supportProof, loRatExpr, hiRatExpr, leProof, boundRat, cfgExpr]

          -- Try direct apply first
          setGoals [goal]
          try
            let newGoals ← goal.apply proof
            setGoals newGoals
            for g in newGoals do
              setGoals [g]
              let tryClose (tac : TacticM Unit) : TacticM Bool := do
                let saved ← saveState
                try
                  tac
                  if (← getGoals).isEmpty then
                    return true
                  saved.restore
                  return false
                catch _ =>
                  saved.restore
                  return false
              if ← tryClose (evalTactic (← `(tactic| rfl))) then
                continue
              evalTactic (← `(tactic| native_decide))
          catch _ =>
            -- Apply failed, so we need to use convert
            setGoals [goal]

            -- Build the certificate expression (using appropriate check function)
            -- Note: WithInv check functions don't take a cfg parameter
            let intervalRat ← mkAppM ``IntervalRat.mk #[loRatExpr, hiRatExpr, leProof]
            let checkExpr ← if useWithInv then
              mkAppM ``LeanCert.Validity.checkUpperBoundWithInv #[ast, intervalRat, boundRat]
            else
              mkAppM ``LeanCert.Validity.checkUpperBound #[ast, intervalRat, boundRat, cfgExpr]

            -- Build proof that checkUpperBound ... = true using native_decide via an auxiliary goal
            let certTy ← mkAppM ``Eq #[checkExpr, mkConst ``Bool.true]
            let certGoal ← mkFreshExprMVar certTy
            let certGoalId := certGoal.mvarId!
            setGoals [certGoalId]
            evalTactic (← `(tactic| native_decide))
            let certProof := certGoal

            -- Apply the theorem with the certificate to get the conclusion
            let conclusionProof ← mkAppM' proof #[certProof]
            let conclusionTerm ← Lean.Elab.Term.exprToSyntax conclusionProof

            -- Now use convert on the conclusion (not the full proof)
            setGoals [goal]
            evalTactic (← `(tactic| convert ($conclusionTerm) using 3))

            -- Close side goals (usually equality goals for Set.Icc and bounds)
            let goals ← getGoals
            for g in goals do
              setGoals [g]
              -- Helper: try a tactic and check if goal was actually closed
              let tryClose (tac : TacticM Unit) : TacticM Bool := do
                let saved ← saveState
                try
                  tac
                  if (← getGoals).isEmpty then
                    return true
                  saved.restore
                  return false
                catch _ =>
                  saved.restore
                  return false
              -- Try decimal-specific tactic first for efficiency
              if ← tryClose (evalTactic (← `(tactic| norm_num; simp only [Rat.divInt_eq_div]; push_cast; rfl))) then continue
              if ← tryCloseRpowSideGoal then continue
              -- Handle negative decimals (-(1/2) = ↑(Rat.divInt (-1) 2))
              if ← tryClose (evalTactic (← `(tactic| norm_num; simp only [Rat.divInt_eq_div]; try (push_cast; try ring)))) then continue
              if ← tryClose (evalTactic (← `(tactic| rfl))) then continue
              -- For Set.Icc equality, use congr_arg with norm_num
              if ← tryClose (evalTactic (← `(tactic| congr 1 <;> norm_num))) then continue
              if ← tryClose (evalTactic (← `(tactic| rfl))) then continue
              if ← tryCloseRpowSideGoal then continue
              if ← tryClose (evalTactic (← `(tactic| norm_cast))) then continue
              if ← tryClose (evalTactic (← `(tactic| norm_num))) then continue
              -- Handle power expansion (x^2 = x*x, x^3 = x*x*x, etc.)
              if ← tryClose (evalTactic (← `(tactic| simp only [sq, pow_two, pow_succ, pow_zero, pow_one, one_mul, mul_one]))) then continue
              -- Handle Expr.eval unfolding - unfolds Expr.eval to raw arithmetic, then uses ring to close
              if ← tryClose (evalTactic (← `(tactic| simp only [LeanCert.Core.Expr.eval_add, LeanCert.Core.Expr.eval_mul, LeanCert.Core.Expr.eval_neg, LeanCert.Core.Expr.eval_const, LeanCert.Core.Expr.eval_var, LeanCert.Core.Expr.eval_sin, LeanCert.Core.Expr.eval_cos, LeanCert.Core.Expr.eval_exp, LeanCert.Core.Expr.eval_sqrt, LeanCert.Core.Expr.eval_sub, Real.sqrt_mul_self_eq_abs, LeanCert.Meta.max_eq_half_add_abs_sub, LeanCert.Meta.min_eq_half_sub_abs_sub, div_eq_mul_inv, sub_eq_add_neg]))) then continue
              -- Same but with push_cast for rational coercion issues
              if ← tryClose (evalTactic (← `(tactic| simp only [LeanCert.Core.Expr.eval_add, LeanCert.Core.Expr.eval_mul, LeanCert.Core.Expr.eval_neg, LeanCert.Core.Expr.eval_const, LeanCert.Core.Expr.eval_var, LeanCert.Core.Expr.eval_sin, LeanCert.Core.Expr.eval_cos, LeanCert.Core.Expr.eval_exp, LeanCert.Core.Expr.eval_sqrt, LeanCert.Core.Expr.eval_sub, Real.sqrt_mul_self_eq_abs, LeanCert.Meta.max_eq_half_add_abs_sub, LeanCert.Meta.min_eq_half_sub_abs_sub, div_eq_mul_inv, sub_eq_add_neg]; try (push_cast; try ring)))) then continue
              -- Handle decimal bounds (2.72 = ↑(Rat.divInt 68 25))
              -- norm_num converts 2.72 to 68/25, then simp+push_cast closes the equality
              if ← tryClose (evalTactic (← `(tactic| norm_num; simp only [Rat.divInt_eq_div]; push_cast; rfl))) then continue
              if ← tryClose (evalTactic (← `(tactic| simp only [Rat.divInt_eq_div]; push_cast; rfl))) then continue
              if ← tryClose (evalTactic (← `(tactic| simp [Rat.divInt_eq_div]))) then continue
              if ← tryClose (evalTactic (← `(tactic| push_cast; rfl))) then continue
              if ← tryClose (evalTactic (← `(tactic| simp only [Rat.cast_natCast, Rat.cast_intCast, Nat.cast_ofNat, Int.cast_ofNat, NNRat.cast_natCast]))) then continue
              -- Last resort - leave the goal for the user but warn
              logWarning m!"interval_bound: Could not close side goal: {← g.getType}"

        | none =>
          -- Direct IntervalRat goal - use appropriate verify_upper_bound theorem
          let proof ← if useWithInv then
            mkAppM ``verify_upper_bound_withInv #[ast, supportProof, intervalInfo.intervalRat, boundRat]
          else
            mkAppM ``verify_upper_bound #[ast, supportProof, intervalInfo.intervalRat, boundRat, cfgExpr]
          -- Try direct apply first
          setGoals [goal]
          try
            let newGoals ← goal.apply proof
            setGoals newGoals
            for g in newGoals do
              setGoals [g]
              evalTactic (← `(tactic| native_decide))
          catch _ =>
            -- Apply failed, use convert
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
            let goals ← getGoals
            for g in goals do
              setGoals [g]
              let tryClose (tac : TacticM Unit) : TacticM Bool := do
                let saved ← saveState
                try
                  tac
                  if (← getGoals).isEmpty then
                    return true
                  saved.restore
                  return false
                catch _ =>
                  saved.restore
                  return false
              if ← tryClose (evalTactic (← `(tactic| rfl))) then continue
              if ← tryCloseRpowSideGoal then continue
              if ← tryClose (evalTactic (← `(tactic| norm_cast))) then continue
              if ← tryClose (evalTactic (← `(tactic| norm_num))) then continue
              if ← tryClose (evalTactic (← `(tactic| simp only [LeanCert.Core.Expr.eval_add, LeanCert.Core.Expr.eval_mul, LeanCert.Core.Expr.eval_neg, LeanCert.Core.Expr.eval_const, LeanCert.Core.Expr.eval_var, LeanCert.Core.Expr.eval_sin, LeanCert.Core.Expr.eval_cos, LeanCert.Core.Expr.eval_exp, LeanCert.Core.Expr.eval_sqrt, LeanCert.Core.Expr.eval_sub, Real.sqrt_mul_self_eq_abs, LeanCert.Meta.max_eq_half_add_abs_sub, LeanCert.Meta.min_eq_half_sub_abs_sub, div_eq_mul_inv, sub_eq_add_neg]))) then continue
              if ← tryClose (evalTactic (← `(tactic| simp only [LeanCert.Core.Expr.eval_add, LeanCert.Core.Expr.eval_mul, LeanCert.Core.Expr.eval_neg, LeanCert.Core.Expr.eval_const, LeanCert.Core.Expr.eval_var, LeanCert.Core.Expr.eval_sin, LeanCert.Core.Expr.eval_cos, LeanCert.Core.Expr.eval_exp, LeanCert.Core.Expr.eval_sqrt, LeanCert.Core.Expr.eval_sub, Real.sqrt_mul_self_eq_abs, LeanCert.Meta.max_eq_half_add_abs_sub, LeanCert.Meta.min_eq_half_sub_abs_sub, div_eq_mul_inv, sub_eq_add_neg]; try (push_cast; try ring)))) then continue
              logWarning m!"interval_bound: Could not close side goal: {← g.getType}"

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

      -- Handle based on interval source
      match intervalInfo.fromSetIcc with
        | some (_lo, _hi, loRatExpr, hiRatExpr, leProof, _origLo, _origHi) =>
          -- Choose theorem and arguments based on support type
          -- Note: WithInv theorems don't take a cfg parameter
          let proof ← if useWithInv then
            mkAppM ``verify_lower_bound_Icc_withInv #[ast, supportProof, loRatExpr, hiRatExpr, leProof, boundRat]
          else
            mkAppM ``verify_lower_bound_Icc_core #[ast, supportProof, loRatExpr, hiRatExpr, leProof, boundRat, cfgExpr]

          -- Try direct apply first
          setGoals [goal]
          try
            let newGoals ← goal.apply proof
            setGoals newGoals
            for g in newGoals do
              setGoals [g]
              let tryClose (tac : TacticM Unit) : TacticM Bool := do
                let saved ← saveState
                try
                  tac
                  if (← getGoals).isEmpty then
                    return true
                  saved.restore
                  return false
                catch _ =>
                  saved.restore
                  return false
              if ← tryClose (evalTactic (← `(tactic| rfl))) then
                continue
              evalTactic (← `(tactic| native_decide))
          catch _ =>
            -- Apply failed, use convert
            setGoals [goal]
            let intervalRat ← mkAppM ``IntervalRat.mk #[loRatExpr, hiRatExpr, leProof]
            let checkExpr ← if useWithInv then
              mkAppM ``LeanCert.Validity.checkLowerBoundWithInv #[ast, intervalRat, boundRat]
            else
              mkAppM ``LeanCert.Validity.checkLowerBound #[ast, intervalRat, boundRat, cfgExpr]

            -- Build proof using native_decide via an auxiliary goal
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

            -- Close side goals
            let goals ← getGoals
            for g in goals do
              setGoals [g]
              -- Helper: try a tactic and check if goal was actually closed
              let tryClose (tac : TacticM Unit) : TacticM Bool := do
                let saved ← saveState
                try
                  tac
                  if (← getGoals).isEmpty then
                    return true
                  saved.restore
                  return false
                catch _ =>
                  saved.restore
                  return false
              -- Try decimal-specific tactic first for efficiency
              if ← tryClose (evalTactic (← `(tactic| norm_num; simp only [Rat.divInt_eq_div]; push_cast; rfl))) then continue
              if ← tryCloseRpowSideGoal then continue
              -- Handle negative decimals (-(1/2) = ↑(Rat.divInt (-1) 2))
              if ← tryClose (evalTactic (← `(tactic| norm_num; simp only [Rat.divInt_eq_div]; try (push_cast; try ring)))) then continue
              if ← tryClose (evalTactic (← `(tactic| rfl))) then continue
              if ← tryClose (evalTactic (← `(tactic| congr 1 <;> norm_num))) then continue
              if ← tryClose (evalTactic (← `(tactic| rfl))) then continue
              if ← tryCloseRpowSideGoal then continue
              if ← tryClose (evalTactic (← `(tactic| norm_cast))) then continue
              if ← tryClose (evalTactic (← `(tactic| norm_num))) then continue
              -- Handle power expansion (x^2 = x*x, x^3 = x*x*x, etc.)
              if ← tryClose (evalTactic (← `(tactic| simp only [sq, pow_two, pow_succ, pow_zero, pow_one, one_mul, mul_one]))) then continue
              -- Handle Expr.eval unfolding - unfolds Expr.eval to raw arithmetic, then uses ring to close
              if ← tryClose (evalTactic (← `(tactic| simp only [LeanCert.Core.Expr.eval_add, LeanCert.Core.Expr.eval_mul, LeanCert.Core.Expr.eval_neg, LeanCert.Core.Expr.eval_const, LeanCert.Core.Expr.eval_var, LeanCert.Core.Expr.eval_sin, LeanCert.Core.Expr.eval_cos, LeanCert.Core.Expr.eval_exp, LeanCert.Core.Expr.eval_sqrt, LeanCert.Core.Expr.eval_sub, Real.sqrt_mul_self_eq_abs, LeanCert.Meta.max_eq_half_add_abs_sub, LeanCert.Meta.min_eq_half_sub_abs_sub, div_eq_mul_inv, sub_eq_add_neg]))) then continue
              -- Same but with push_cast for rational coercion issues
              if ← tryClose (evalTactic (← `(tactic| simp only [LeanCert.Core.Expr.eval_add, LeanCert.Core.Expr.eval_mul, LeanCert.Core.Expr.eval_neg, LeanCert.Core.Expr.eval_const, LeanCert.Core.Expr.eval_var, LeanCert.Core.Expr.eval_sin, LeanCert.Core.Expr.eval_cos, LeanCert.Core.Expr.eval_exp, LeanCert.Core.Expr.eval_sqrt, LeanCert.Core.Expr.eval_sub, Real.sqrt_mul_self_eq_abs, LeanCert.Meta.max_eq_half_add_abs_sub, LeanCert.Meta.min_eq_half_sub_abs_sub, div_eq_mul_inv, sub_eq_add_neg]; try (push_cast; try ring)))) then continue
              -- Handle decimal bounds (2.72 = ↑(Rat.divInt 68 25)) - fallback tactics
              if ← tryClose (evalTactic (← `(tactic| simp only [Rat.divInt_eq_div]; push_cast; rfl))) then continue
              if ← tryClose (evalTactic (← `(tactic| simp [Rat.divInt_eq_div]))) then continue
              if ← tryClose (evalTactic (← `(tactic| push_cast; rfl))) then continue
              if ← tryClose (evalTactic (← `(tactic| simp only [Rat.cast_natCast, Rat.cast_intCast, Nat.cast_ofNat, Int.cast_ofNat, NNRat.cast_natCast]))) then continue
              logWarning m!"interval_bound: Could not close side goal: {← g.getType}"

        | none =>
          -- Direct IntervalRat goal - use appropriate verify_lower_bound theorem
          let proof ← if useWithInv then
            mkAppM ``verify_lower_bound_withInv #[ast, supportProof, intervalInfo.intervalRat, boundRat]
          else
            mkAppM ``verify_lower_bound #[ast, supportProof, intervalInfo.intervalRat, boundRat, cfgExpr]
          -- Try direct apply first
          setGoals [goal]
          try
            let newGoals ← goal.apply proof
            setGoals newGoals
            for g in newGoals do
              setGoals [g]
              evalTactic (← `(tactic| native_decide))
          catch _ =>
            -- Apply failed, use convert
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
            let goals ← getGoals
            for g in goals do
              setGoals [g]
              let tryClose (tac : TacticM Unit) : TacticM Bool := do
                let saved ← saveState
                try
                  tac
                  if (← getGoals).isEmpty then
                    return true
                  saved.restore
                  return false
                catch _ =>
                  saved.restore
                  return false
              if ← tryClose (evalTactic (← `(tactic| rfl))) then continue
              if ← tryCloseRpowSideGoal then continue
              if ← tryClose (evalTactic (← `(tactic| norm_cast))) then continue
              if ← tryClose (evalTactic (← `(tactic| norm_num))) then continue
              if ← tryClose (evalTactic (← `(tactic| simp only [LeanCert.Core.Expr.eval_add, LeanCert.Core.Expr.eval_mul, LeanCert.Core.Expr.eval_neg, LeanCert.Core.Expr.eval_const, LeanCert.Core.Expr.eval_var, LeanCert.Core.Expr.eval_sin, LeanCert.Core.Expr.eval_cos, LeanCert.Core.Expr.eval_exp, LeanCert.Core.Expr.eval_sqrt, LeanCert.Core.Expr.eval_sub, Real.sqrt_mul_self_eq_abs, LeanCert.Meta.max_eq_half_add_abs_sub, LeanCert.Meta.min_eq_half_sub_abs_sub, div_eq_mul_inv, sub_eq_add_neg]))) then continue
              if ← tryClose (evalTactic (← `(tactic| simp only [LeanCert.Core.Expr.eval_add, LeanCert.Core.Expr.eval_mul, LeanCert.Core.Expr.eval_neg, LeanCert.Core.Expr.eval_const, LeanCert.Core.Expr.eval_var, LeanCert.Core.Expr.eval_sin, LeanCert.Core.Expr.eval_cos, LeanCert.Core.Expr.eval_exp, LeanCert.Core.Expr.eval_sqrt, LeanCert.Core.Expr.eval_sub, Real.sqrt_mul_self_eq_abs, LeanCert.Meta.max_eq_half_add_abs_sub, LeanCert.Meta.min_eq_half_sub_abs_sub, div_eq_mul_inv, sub_eq_add_neg]; try (push_cast; try ring)))) then continue
              logWarning m!"interval_bound: Could not close side goal: {← g.getType}"

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

      -- Handle based on interval source
      match intervalInfo.fromSetIcc with
        | some (_lo, _hi, loRatExpr, hiRatExpr, leProof, _origLo, _origHi) =>
          -- Choose theorem and arguments based on support type
          -- Note: WithInv theorems don't take a cfg parameter
          let proof ← if useWithInv then
            mkAppM ``verify_strict_upper_bound_Icc_withInv #[ast, supportProof, loRatExpr, hiRatExpr, leProof, boundRat]
          else
            mkAppM ``verify_strict_upper_bound_Icc_core #[ast, supportProof, loRatExpr, hiRatExpr, leProof, boundRat, cfgExpr]

          -- Try direct apply first
          setGoals [goal]
          try
            let newGoals ← goal.apply proof
            setGoals newGoals
            for g in newGoals do
              setGoals [g]
              let tryClose (tac : TacticM Unit) : TacticM Bool := do
                let saved ← saveState
                try
                  tac
                  if (← getGoals).isEmpty then
                    return true
                  saved.restore
                  return false
                catch _ =>
                  saved.restore
                  return false
              if ← tryClose (evalTactic (← `(tactic| rfl))) then
                continue
              evalTactic (← `(tactic| native_decide))
          catch _ =>
            -- Apply failed, use convert
            setGoals [goal]
            let intervalRat ← mkAppM ``IntervalRat.mk #[loRatExpr, hiRatExpr, leProof]
            let checkExpr ← if useWithInv then
              mkAppM ``LeanCert.Validity.checkStrictUpperBoundWithInv #[ast, intervalRat, boundRat]
            else
              mkAppM ``LeanCert.Validity.checkStrictUpperBound #[ast, intervalRat, boundRat, cfgExpr]

            -- Build proof using native_decide via an auxiliary goal
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

            -- Close side goals
            let goals ← getGoals
            for g in goals do
              setGoals [g]
              -- Helper: try a tactic and check if goal was actually closed
              let tryClose (tac : TacticM Unit) : TacticM Bool := do
                let saved ← saveState
                try
                  tac
                  if (← getGoals).isEmpty then
                    return true
                  saved.restore
                  return false
                catch _ =>
                  saved.restore
                  return false
              -- Try decimal-specific tactic first for efficiency
              if ← tryClose (evalTactic (← `(tactic| norm_num; simp only [Rat.divInt_eq_div]; push_cast; rfl))) then continue
              if ← tryCloseRpowSideGoal then continue
              -- Handle negative decimals (-(1/2) = ↑(Rat.divInt (-1) 2))
              if ← tryClose (evalTactic (← `(tactic| norm_num; simp only [Rat.divInt_eq_div]; try (push_cast; try ring)))) then continue
              if ← tryClose (evalTactic (← `(tactic| rfl))) then continue
              if ← tryClose (evalTactic (← `(tactic| congr 1 <;> norm_num))) then continue
              if ← tryClose (evalTactic (← `(tactic| rfl))) then continue
              if ← tryClose (evalTactic (← `(tactic| norm_cast))) then continue
              if ← tryClose (evalTactic (← `(tactic| norm_num))) then continue
              -- Handle power expansion (x^2 = x*x, x^3 = x*x*x, etc.)
              if ← tryClose (evalTactic (← `(tactic| simp only [sq, pow_two, pow_succ, pow_zero, pow_one, one_mul, mul_one]))) then continue
              -- Handle Expr.eval unfolding - unfolds Expr.eval to raw arithmetic, then uses ring to close
              if ← tryClose (evalTactic (← `(tactic| simp only [LeanCert.Core.Expr.eval_add, LeanCert.Core.Expr.eval_mul, LeanCert.Core.Expr.eval_neg, LeanCert.Core.Expr.eval_const, LeanCert.Core.Expr.eval_var, LeanCert.Core.Expr.eval_sin, LeanCert.Core.Expr.eval_cos, LeanCert.Core.Expr.eval_exp, LeanCert.Core.Expr.eval_sqrt, LeanCert.Core.Expr.eval_sub, Real.sqrt_mul_self_eq_abs, LeanCert.Meta.max_eq_half_add_abs_sub, LeanCert.Meta.min_eq_half_sub_abs_sub, div_eq_mul_inv, sub_eq_add_neg]))) then continue
              -- Same but with push_cast for rational coercion issues
              if ← tryClose (evalTactic (← `(tactic| simp only [LeanCert.Core.Expr.eval_add, LeanCert.Core.Expr.eval_mul, LeanCert.Core.Expr.eval_neg, LeanCert.Core.Expr.eval_const, LeanCert.Core.Expr.eval_var, LeanCert.Core.Expr.eval_sin, LeanCert.Core.Expr.eval_cos, LeanCert.Core.Expr.eval_exp, LeanCert.Core.Expr.eval_sqrt, LeanCert.Core.Expr.eval_sub, Real.sqrt_mul_self_eq_abs, LeanCert.Meta.max_eq_half_add_abs_sub, LeanCert.Meta.min_eq_half_sub_abs_sub, div_eq_mul_inv, sub_eq_add_neg]; try (push_cast; try ring)))) then continue
              -- Handle decimal bounds - fallback tactics
              if ← tryClose (evalTactic (← `(tactic| simp only [Rat.divInt_eq_div]; push_cast; rfl))) then continue
              if ← tryClose (evalTactic (← `(tactic| simp [Rat.divInt_eq_div]))) then continue
              if ← tryClose (evalTactic (← `(tactic| push_cast; rfl))) then continue
              if ← tryClose (evalTactic (← `(tactic| simp only [Rat.cast_natCast, Rat.cast_intCast, Nat.cast_ofNat, Int.cast_ofNat, NNRat.cast_natCast]))) then continue
              logWarning m!"interval_bound: Could not close side goal: {← g.getType}"

        | none =>
          -- Direct IntervalRat goal - use appropriate theorem
          let proof ← if useWithInv then
            mkAppM ``verify_strict_upper_bound_withInv #[ast, supportProof, intervalInfo.intervalRat, boundRat]
          else
            mkAppM ``verify_strict_upper_bound #[ast, supportProof, intervalInfo.intervalRat, boundRat, cfgExpr]
          let newGoals ← goal.apply proof
          setGoals newGoals
          for g in newGoals do
            setGoals [g]
            try
              evalTactic (← `(tactic| native_decide))
            catch _ =>
              try
                evalTactic (← `(tactic| norm_cast))
              catch _ =>
                evalTactic (← `(tactic| simp only [Rat.cast_zero, Rat.cast_one, Rat.cast_intCast, Rat.cast_natCast]))

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

      -- Handle based on interval source
      match intervalInfo.fromSetIcc with
        | some (_lo, _hi, loRatExpr, hiRatExpr, leProof, _origLo, _origHi) =>
          -- Choose theorem and arguments based on support type
          -- Note: WithInv theorems don't take a cfg parameter
          let proof ← if useWithInv then
            mkAppM ``verify_strict_lower_bound_Icc_withInv #[ast, supportProof, loRatExpr, hiRatExpr, leProof, boundRat]
          else
            mkAppM ``verify_strict_lower_bound_Icc_core #[ast, supportProof, loRatExpr, hiRatExpr, leProof, boundRat, cfgExpr]

          -- Try direct apply first
          setGoals [goal]
          try
            let newGoals ← goal.apply proof
            setGoals newGoals
            for g in newGoals do
              setGoals [g]
              let tryClose (tac : TacticM Unit) : TacticM Bool := do
                let saved ← saveState
                try
                  tac
                  if (← getGoals).isEmpty then
                    return true
                  saved.restore
                  return false
                catch _ =>
                  saved.restore
                  return false
              if ← tryClose (evalTactic (← `(tactic| rfl))) then
                continue
              evalTactic (← `(tactic| native_decide))
          catch _ =>
            -- Apply failed, use convert
            setGoals [goal]
            let intervalRat ← mkAppM ``IntervalRat.mk #[loRatExpr, hiRatExpr, leProof]
            let checkExpr ← if useWithInv then
              mkAppM ``LeanCert.Validity.checkStrictLowerBoundWithInv #[ast, intervalRat, boundRat]
            else
              mkAppM ``LeanCert.Validity.checkStrictLowerBound #[ast, intervalRat, boundRat, cfgExpr]

            -- Build proof using native_decide via an auxiliary goal
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

            -- Close side goals
            let goals ← getGoals
            for g in goals do
              setGoals [g]
              -- Helper: try a tactic and check if goal was actually closed
              let tryClose (tac : TacticM Unit) : TacticM Bool := do
                let saved ← saveState
                try
                  tac
                  if (← getGoals).isEmpty then
                    return true
                  saved.restore
                  return false
                catch _ =>
                  saved.restore
                  return false
              -- Try decimal-specific tactic first for efficiency
              if ← tryClose (evalTactic (← `(tactic| norm_num; simp only [Rat.divInt_eq_div]; push_cast; rfl))) then continue
              if ← tryCloseRpowSideGoal then continue
              -- Handle negative decimals (-(1/2) = ↑(Rat.divInt (-1) 2))
              if ← tryClose (evalTactic (← `(tactic| norm_num; simp only [Rat.divInt_eq_div]; try (push_cast; try ring)))) then continue
              if ← tryClose (evalTactic (← `(tactic| rfl))) then continue
              if ← tryClose (evalTactic (← `(tactic| congr 1 <;> norm_num))) then continue
              if ← tryClose (evalTactic (← `(tactic| rfl))) then continue
              if ← tryClose (evalTactic (← `(tactic| norm_cast))) then continue
              if ← tryClose (evalTactic (← `(tactic| norm_num))) then continue
              -- Handle power expansion (x^2 = x*x, x^3 = x*x*x, etc.)
              if ← tryClose (evalTactic (← `(tactic| simp only [sq, pow_two, pow_succ, pow_zero, pow_one, one_mul, mul_one]))) then continue
              -- Handle Expr.eval unfolding - unfolds Expr.eval to raw arithmetic, then uses ring to close
              if ← tryClose (evalTactic (← `(tactic| simp only [LeanCert.Core.Expr.eval_add, LeanCert.Core.Expr.eval_mul, LeanCert.Core.Expr.eval_neg, LeanCert.Core.Expr.eval_const, LeanCert.Core.Expr.eval_var, LeanCert.Core.Expr.eval_sin, LeanCert.Core.Expr.eval_cos, LeanCert.Core.Expr.eval_exp, LeanCert.Core.Expr.eval_sqrt, LeanCert.Core.Expr.eval_sub, Real.sqrt_mul_self_eq_abs, LeanCert.Meta.max_eq_half_add_abs_sub, LeanCert.Meta.min_eq_half_sub_abs_sub, div_eq_mul_inv, sub_eq_add_neg]))) then continue
              -- Same but with push_cast for rational coercion issues
              if ← tryClose (evalTactic (← `(tactic| simp only [LeanCert.Core.Expr.eval_add, LeanCert.Core.Expr.eval_mul, LeanCert.Core.Expr.eval_neg, LeanCert.Core.Expr.eval_const, LeanCert.Core.Expr.eval_var, LeanCert.Core.Expr.eval_sin, LeanCert.Core.Expr.eval_cos, LeanCert.Core.Expr.eval_exp, LeanCert.Core.Expr.eval_sqrt, LeanCert.Core.Expr.eval_sub, Real.sqrt_mul_self_eq_abs, LeanCert.Meta.max_eq_half_add_abs_sub, LeanCert.Meta.min_eq_half_sub_abs_sub, div_eq_mul_inv, sub_eq_add_neg]; try (push_cast; try ring)))) then continue
              -- Handle decimal bounds - fallback tactics
              if ← tryClose (evalTactic (← `(tactic| simp only [Rat.divInt_eq_div]; push_cast; rfl))) then continue
              if ← tryClose (evalTactic (← `(tactic| simp [Rat.divInt_eq_div]))) then continue
              if ← tryClose (evalTactic (← `(tactic| push_cast; rfl))) then continue
              if ← tryClose (evalTactic (← `(tactic| simp only [Rat.cast_natCast, Rat.cast_intCast, Nat.cast_ofNat, Int.cast_ofNat, NNRat.cast_natCast]))) then continue
              logWarning m!"interval_bound: Could not close side goal: {← g.getType}"

        | none =>
          -- Direct IntervalRat goal - use appropriate theorem
          let proof ← if useWithInv then
            mkAppM ``verify_strict_lower_bound_withInv #[ast, supportProof, intervalInfo.intervalRat, boundRat]
          else
            mkAppM ``verify_strict_lower_bound #[ast, supportProof, intervalInfo.intervalRat, boundRat, cfgExpr]
          let newGoals ← goal.apply proof
          setGoals newGoals
          for g in newGoals do
            setGoals [g]
            try
              evalTactic (← `(tactic| native_decide))
            catch _ =>
              try
                evalTactic (← `(tactic| norm_cast))
              catch _ =>
                evalTactic (← `(tactic| simp only [Rat.cast_zero, Rat.cast_one, Rat.cast_intCast, Rat.cast_natCast]))


/-! ## Tactic Syntax -/

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
    -- Fixed depth specified by user
    intervalBoundCore n.getNat
  | none =>
    -- Adaptive: try increasing depths until success
    let depths := [10, 15, 20, 25, 30]
    let _goal ← getMainGoal
    let goalState ← saveState
    let mut lastError : Option Exception := none
    for d in depths do
      try
        restoreState goalState
        trace[interval_decide] "Trying Taylor depth {d}..."
        intervalBoundCore d
        trace[interval_decide] "Success with Taylor depth {d}"
        return  -- Success!
      catch e =>
        lastError := some e
        continue
    -- All depths failed - run diagnostics and report enriched error
    match lastError with
    | some e =>
      -- Restore state and try to parse goal for diagnostics
      restoreState goalState
      let diagMsg ← try
        -- Apply same preprocessing as intervalBoundCore for consistent parsing
        try
          evalTactic (← `(tactic| intro _x _hx; simp only [ge_iff_le, gt_iff_lt]; revert _x _hx))
        catch _ =>
          try evalTactic (← `(tactic| simp only [ge_iff_le, gt_iff_lt]))
          catch _ => pure ()
        try
          evalTactic (← `(tactic| simp only [pow_zero, pow_one, one_mul, mul_one] at *))
        catch _ => pure ()

        let goal ← getMainGoal
        let goalType ← goal.getType
        let boundGoalOpt ← parseBoundGoal goalType
        runShadowDiagnostic boundGoalOpt goalType
      catch _ =>
        pure m!"(Could not run diagnostics)"

      throwError m!"{e.toMessageData}\n\n{diagMsg}"
    | none => throwError "certify_bound: All precision levels failed"

/-- Backward-compatible alias for certify_bound -/
macro "interval_bound" depth:(num)? : tactic => `(tactic| certify_bound $[$depth]?)


end LeanCert.Tactic.Auto

