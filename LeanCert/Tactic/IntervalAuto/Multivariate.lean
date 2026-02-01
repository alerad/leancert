/-
Copyright (c) 2024 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Tactic.IntervalAuto.Basic
import LeanCert.Validity.Bounds
import LeanCert.Engine.Optimization.BoundVerify

/-!
# Multivariate Bound Tactic

The `multivariate_bound` tactic proves bounds on multivariate expressions.
-/

open Lean Meta Elab Tactic Term

namespace LeanCert.Tactic.Auto

open LeanCert.Meta
open LeanCert.Core
open LeanCert.Engine
open LeanCert.Validity
open LeanCert.Validity.GlobalOpt
open LeanCert.Engine.Optimization

/-- The main multivariate_bound tactic implementation -/
def multivariateBoundCore (maxIters : Nat) (tolerance : ℚ) (useMonotonicity : Bool) (taylorDepth : Nat) : TacticM Unit := do
  intervalNormCore
  let goal ← getMainGoal
  let goalType ← goal.getType
  trace[LeanCert.discovery] "multivariate_bound goal: {goalType}"

  -- Parse the multivariate goal
  let parsed ← parseMultivariateBoundGoal goalType
  let some boundGoal := parsed
    | let diagReport ← mkDiagnosticReport "multivariate_bound" goalType "parse"
        (some m!"Expected forms:\n\
                 • ∀ x ∈ I, ∀ y ∈ J, ... f(x,y,...) ≤ c\n\
                 • ∀ x ∈ I, ∀ y ∈ J, ... c ≤ f(x,y,...)\n\n\
                 Domain formats accepted:\n\
                 • x ∈ Set.Icc a b\n\
                 • a ≤ x ∧ x ≤ b\n\
                 • a ≤ x → x ≤ b → ...")
      throwError "multivariate_bound: Could not parse goal as multivariate bound.\n\n{diagReport}"

  match boundGoal with
  | .forallLe vars func bound =>
    proveMultivariateLe goal vars func bound maxIters tolerance useMonotonicity taylorDepth
  | .forallGe vars func bound =>
    proveMultivariateGe goal vars func bound maxIters tolerance useMonotonicity taylorDepth

where
  /-- Extract rational bound from possible coercion (reusing logic from intervalBoundCore) -/
  extractRatBound (bound : Lean.Expr) : TacticM Lean.Expr := do
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

  /-- Fetch local variable expressions in the order of VarIntervalInfo. -/
  getVarExprs (vars : Array VarIntervalInfo) : TacticM (Array Lean.Expr) := do
    let lctx ← getLCtx
    let mut out : Array Lean.Expr := #[]
    let mut used : Array Lean.FVarId := #[]
    for info in vars do
      match lctx.findFromUserName? info.varName with
      | some decl =>
          out := out.push (Lean.mkFVar decl.fvarId)
          used := used.push decl.fvarId
      | none =>
          let mut fallback : Option Lean.LocalDecl := none
          for decl in lctx do
            if !(used.any (fun id => id == decl.fvarId)) then
              if (← isDefEq decl.type info.varType) then
                fallback := some decl
                break
          match fallback with
          | some decl =>
              out := out.push (Lean.mkFVar decl.fvarId)
              used := used.push decl.fvarId
          | none =>
              throwError m!"multivariate_bound: missing local {info.varName}"
    return out

  /-- Build an environment function ρ from a list of variables. -/
  mkEnvExpr (varsListExpr : Lean.Expr) : TacticM Lean.Expr := do
    withLocalDeclD `i (Lean.mkConst ``Nat) fun i => do
      let zeroRat := toExpr (0 : ℚ)
      let zeroReal ← mkAppOptM ``Rat.cast #[mkConst ``Real, none, zeroRat]
      let body ← mkAppM ``List.getD #[varsListExpr, i, zeroReal]
      mkLambdaFVars #[i] body

  /-- Prove ∀ x₁ ∈ I₁, ..., ∀ xₙ ∈ Iₙ, f(x) ≤ c using verify_global_upper_bound -/
  proveMultivariateLe (goal : MVarId) (vars : Array VarIntervalInfo) (func bound : Lean.Expr)
      (maxIters : Nat) (tolerance : ℚ) (useMonotonicity : Bool) (taylorDepth : Nat) : TacticM Unit := do
    goal.withContext do
      let boxExpr ← mkBoxExpr vars
      let ast ← reify func
      let boundRat ← extractRatBound bound
      let supportProof ← mkSupportedProof ast
      let cfgExpr ← mkAppM ``GlobalOptConfig.mk #[toExpr maxIters, toExpr tolerance, toExpr useMonotonicity, toExpr taylorDepth]
      let proof ← mkAppM ``verify_global_upper_bound #[ast, supportProof, boxExpr, boundRat, cfgExpr]

      setGoals [goal]
      try
        evalTactic (← `(tactic| repeat intro))
      catch _ => pure ()

      let mainGoalAfterIntro ← getMainGoal

      let (rhoSyntax, varsListSyntax, boxSyntax) ← withMainContext do
        let varExprs ← getVarExprs vars
        let varsListExpr ← mkListLit (Lean.mkConst ``Real) varExprs.toList
        let rhoExpr ← mkEnvExpr varsListExpr
        let rhoSyntax ← Lean.Elab.Term.exprToSyntax rhoExpr
        let varsListSyntax ← Lean.Elab.Term.exprToSyntax varsListExpr
        let boxSyntax ← Lean.Elab.Term.exprToSyntax boxExpr
        return (rhoSyntax, varsListSyntax, boxSyntax)

      let checkExpr ← mkAppM ``checkGlobalUpperBound #[ast, boxExpr, boundRat, cfgExpr]
      let certTy ← mkAppM ``Eq #[checkExpr, Lean.mkConst ``Bool.true]
      let certGoal ← mkFreshExprMVar certTy
      let certGoalId := certGoal.mvarId!
      setGoals [certGoalId]
      try
        evalTactic (← `(tactic| native_decide))
      catch e =>
        throwError "multivariate_bound: Certificate check failed. The bound may be too tight.\n{e.toMessageData}"

      let conclusionProof ← mkAppM' proof #[certGoal]
      let conclusionTerm ← Lean.Elab.Term.exprToSyntax conclusionProof

      setGoals [mainGoalAfterIntro]
      evalTactic (← `(tactic| exact (by
        have hmem : Box.envMem $rhoSyntax $boxSyntax := by
          intro i
          fin_cases i <;>
            simp [Box.envMem, IntervalRat.mem_iff_mem_Icc, Set.mem_Icc] at * <;>
            first | assumption | constructor <;> assumption
        have hzero : ∀ i, i ≥ ($boxSyntax).length → $rhoSyntax i = 0 := by
          intro i hi
          have hnot : ¬ i < ($boxSyntax).length := by exact not_lt.mpr hi
          have hnot' : ¬ i < ($varsListSyntax).length := by
            simpa using hnot
          have hge' : ($varsListSyntax).length ≤ i := by
            exact not_lt.mp hnot'
          simp [List.getD, List.getElem?_eq_none hge', Option.getD]
        exact $conclusionTerm $rhoSyntax hmem hzero
      )))

  /-- Prove ∀ x₁ ∈ I₁, ..., ∀ xₙ ∈ Iₙ, c ≤ f(x) using verify_global_lower_bound -/
  proveMultivariateGe (goal : MVarId) (vars : Array VarIntervalInfo) (func bound : Lean.Expr)
      (maxIters : Nat) (tolerance : ℚ) (useMonotonicity : Bool) (taylorDepth : Nat) : TacticM Unit := do
    goal.withContext do
      let boxExpr ← mkBoxExpr vars
      let ast ← reify func
      let boundRat ← extractRatBound bound
      let supportProof ← mkSupportedProof ast
      let cfgExpr ← mkAppM ``GlobalOptConfig.mk #[toExpr maxIters, toExpr tolerance, toExpr useMonotonicity, toExpr taylorDepth]

      let proof ← mkAppM ``verify_global_lower_bound #[ast, supportProof, boxExpr, boundRat, cfgExpr]

      setGoals [goal]
      try
        evalTactic (← `(tactic| repeat intro))
      catch _ => pure ()

      let mainGoalAfterIntro ← getMainGoal

      let (rhoSyntax, varsListSyntax, boxSyntax) ← withMainContext do
        let varExprs ← getVarExprs vars
        let varsListExpr ← mkListLit (Lean.mkConst ``Real) varExprs.toList
        let rhoExpr ← mkEnvExpr varsListExpr
        let rhoSyntax ← Lean.Elab.Term.exprToSyntax rhoExpr
        let varsListSyntax ← Lean.Elab.Term.exprToSyntax varsListExpr
        let boxSyntax ← Lean.Elab.Term.exprToSyntax boxExpr
        return (rhoSyntax, varsListSyntax, boxSyntax)

      let checkExpr ← mkAppM ``checkGlobalLowerBound #[ast, boxExpr, boundRat, cfgExpr]
      let certTy ← mkAppM ``Eq #[checkExpr, Lean.mkConst ``Bool.true]
      let certGoal ← mkFreshExprMVar certTy
      let certGoalId := certGoal.mvarId!
      setGoals [certGoalId]
      try
        evalTactic (← `(tactic| native_decide))
      catch e =>
        throwError "multivariate_bound: Certificate check failed. The bound may be too tight.\n{e.toMessageData}"

      let conclusionProof ← mkAppM' proof #[certGoal]
      let conclusionTerm ← Lean.Elab.Term.exprToSyntax conclusionProof

      setGoals [mainGoalAfterIntro]
      evalTactic (← `(tactic| exact (by
        have hmem : Box.envMem $rhoSyntax $boxSyntax := by
          intro i
          fin_cases i <;>
            simp [Box.envMem, IntervalRat.mem_iff_mem_Icc, Set.mem_Icc] at * <;>
            first | assumption | constructor <;> assumption
        have hzero : ∀ i, i ≥ ($boxSyntax).length → $rhoSyntax i = 0 := by
          intro i hi
          have hnot : ¬ i < ($boxSyntax).length := by exact not_lt.mpr hi
          have hnot' : ¬ i < ($varsListSyntax).length := by
            simpa using hnot
          have hge' : ($varsListSyntax).length ≤ i := by
            exact not_lt.mp hnot'
          simp [List.getD, List.getElem?_eq_none hge', Option.getD]
        exact $conclusionTerm $rhoSyntax hmem hzero
      )))

/-- The multivariate_bound tactic.

    Automatically proves bounds on multivariate expressions using global optimization.

    Usage:
    - `multivariate_bound` - uses defaults (1000 iterations, tolerance 1/1000, Taylor depth 10)
    - `multivariate_bound 2000` - uses 2000 iterations

    Supports goals of the form:
    - `∀ x ∈ I, ∀ y ∈ J, f(x,y) ≤ c`
    - `∀ x ∈ I, ∀ y ∈ J, c ≤ f(x,y)`
-/
elab "multivariate_bound" iters:(num)? : tactic => do
  let maxIters := match iters with
    | some n => n.getNat
    | none => 1000
  multivariateBoundCore maxIters (1/1000) false 10

end LeanCert.Tactic.Auto
