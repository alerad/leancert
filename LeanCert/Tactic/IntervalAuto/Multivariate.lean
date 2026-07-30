/-
Copyright (c) 2024 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Tactic.IntervalAuto.Basic
import LeanCert.Tactic.Verification
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

/-- Runtime facts from the retained multivariate global-bound certificate. -/
inductive MultivariateBoundDirection where
  | upper
  | lower
  deriving DecidableEq, Repr, Inhabited

structure MultivariateBoundOutcome where
  direction : MultivariateBoundDirection
  checker : Name
  verifier : Name
  verification : LeanCert.Tactic.VerificationUsage
  maxIterations : Nat
  tolerance : ℚ
  useMonotonicity : Bool
  taylorDepth : Nat
  deriving Inhabited

inductive MultivariateBoundFailure where
  | unsupported (expression detail : String)
  | rejected (detail : String)
  | transportFailure (detail : String)
  | internalFailure (detail : String)
  deriving Inhabited, Repr

/-- Typed multivariate-bound implementation. -/
unsafe def multivariateBoundCoreTyped (maxIters : Nat) (tolerance : ℚ)
    (useMonotonicity : Bool) (taylorDepth : Nat) :
    TacticM (Except MultivariateBoundFailure MultivariateBoundOutcome) := do
  let original ← saveState
  try intervalNormCore
  catch e =>
    original.restore
    return .error <| .unsupported "goal normalization" (← e.toMessageData.toString)
  let goal ← getMainGoal
  let goalType ← goal.getType
  trace[LeanCert.discovery] "multivariate_bound goal: {goalType}"

  -- Parse the multivariate goal
  let parsed ← parseMultivariateBoundGoal goalType
  let some boundGoal := parsed
    | original.restore
      return .error <| .unsupported (toString goalType)
        "expected a quantified multivariate upper or lower bound"

  match boundGoal with
  | .forallLe vars func bound =>
    match ← proveMultivariateLe goal vars func bound maxIters tolerance
        useMonotonicity taylorDepth with
    | .error failure =>
      original.restore
      return .error failure
    | .ok event => return .ok {
      direction := .upper
      checker := ``checkGlobalUpperBound
      verifier := ``verify_global_upper_bound
      verification := event.toUsage
      maxIterations := maxIters
      tolerance := tolerance
      useMonotonicity := useMonotonicity
      taylorDepth := taylorDepth
    }
  | .forallGe vars func bound =>
    match ← proveMultivariateGe goal vars func bound maxIters tolerance
        useMonotonicity taylorDepth with
    | .error failure =>
      original.restore
      return .error failure
    | .ok event => return .ok {
      direction := .lower
      checker := ``checkGlobalLowerBound
      verifier := ``verify_global_lower_bound
      verification := event.toUsage
      maxIterations := maxIters
      tolerance := tolerance
      useMonotonicity := useMonotonicity
      taylorDepth := taylorDepth
    }

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
      (maxIters : Nat) (tolerance : ℚ) (useMonotonicity : Bool)
      (taylorDepth : Nat) :
      TacticM (Except MultivariateBoundFailure LeanCert.Tactic.VerificationEvent) := do
    let saved ← saveState
    goal.withContext do
      let prepared ←
        try
          let boxExpr ← mkBoxExpr vars
          let ast := (← reifyWithReport func).expr
          let boundRat ← extractRatBound bound
          let supportProof ← mkSupportedProof ast
          let cfgExpr ← mkAppM ``GlobalOptConfig.mk
            #[toExpr maxIters, toExpr tolerance, toExpr useMonotonicity,
              toExpr taylorDepth]
          let proof ← mkAppM ``verify_global_upper_bound
            #[ast, supportProof, boxExpr, boundRat, cfgExpr]
          pure <| some (boxExpr, ast, boundRat, cfgExpr, proof)
        catch e =>
          saved.restore
          return .error <| .unsupported (toString func)
            (← e.toMessageData.toString)
      let some (boxExpr, ast, boundRat, cfgExpr, proof) := prepared
        | saved.restore
          return .error <| .unsupported (toString func)
            "multivariate preparation produced no expression"

      setGoals [goal]
      try
        evalTactic (← `(tactic| repeat intro))
      catch _ => pure ()

      let mainGoalAfterIntro ← getMainGoal

      let syntaxData ←
        try
          withMainContext do
            let varExprs ← getVarExprs vars
            let varsListExpr ← mkListLit (Lean.mkConst ``Real) varExprs.toList
            let rhoExpr ← mkEnvExpr varsListExpr
            let rhoSyntax ← Lean.Elab.Term.exprToSyntax rhoExpr
            let varsListSyntax ← Lean.Elab.Term.exprToSyntax varsListExpr
            let boxSyntax ← Lean.Elab.Term.exprToSyntax boxExpr
            pure <| some (rhoSyntax, varsListSyntax, boxSyntax)
        catch e =>
          saved.restore
          return .error <| .unsupported (toString func)
            (← e.toMessageData.toString)
      let some (rhoSyntax, varsListSyntax, boxSyntax) := syntaxData
        | saved.restore
          return .error <| .unsupported (toString func)
            "could not construct the multivariate environment"

      let checkExpr ← mkAppM ``checkGlobalUpperBound #[ast, boxExpr, boundRat, cfgExpr]
      let certTy ← mkAppM ``Eq #[checkExpr, Lean.mkConst ``Bool.true]
      let certGoal ← mkFreshExprMVar certTy
      let certGoalId := certGoal.mvarId!
      setGoals [certGoalId]
      let event ←
        match ← LeanCert.Tactic.closeCertificateGoalTyped
            (← LeanCert.Tactic.VerificationConfig.current) (← getMainGoal)
            (tacticName := "multivariate_bound") with
        | .accepted event => pure event
        | .rejected =>
            saved.restore
            return .error <| .rejected
              "the multivariate upper-bound checker evaluated to false"
        | .failed failure =>
            saved.restore
            return .error <| .internalFailure
              (failure.message "multivariate_bound")

      let conclusionProof ← mkAppM' proof #[certGoal]
      let conclusionTerm ← Lean.Elab.Term.exprToSyntax conclusionProof

      setGoals [mainGoalAfterIntro]
      try
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
        have hresult := $conclusionTerm $rhoSyntax hmem hzero
        convert hresult using 1 <;>
          simp [List.getD, LeanCert.Core.Expr.eval, Rat.divInt_eq_div,
            sq, pow_two, sub_eq_add_neg, div_eq_mul_inv] <;>
          ring
        )))
      catch e =>
        saved.restore
        return .error <| .transportFailure (← e.toMessageData.toString)
      return .ok event

  /-- Prove ∀ x₁ ∈ I₁, ..., ∀ xₙ ∈ Iₙ, c ≤ f(x) using verify_global_lower_bound -/
  proveMultivariateGe (goal : MVarId) (vars : Array VarIntervalInfo) (func bound : Lean.Expr)
      (maxIters : Nat) (tolerance : ℚ) (useMonotonicity : Bool)
      (taylorDepth : Nat) :
      TacticM (Except MultivariateBoundFailure LeanCert.Tactic.VerificationEvent) := do
    let saved ← saveState
    goal.withContext do
      let prepared ←
        try
          let boxExpr ← mkBoxExpr vars
          let ast := (← reifyWithReport func).expr
          let boundRat ← extractRatBound bound
          let supportProof ← mkSupportedProof ast
          let cfgExpr ← mkAppM ``GlobalOptConfig.mk
            #[toExpr maxIters, toExpr tolerance, toExpr useMonotonicity,
              toExpr taylorDepth]
          let proof ← mkAppM ``verify_global_lower_bound
            #[ast, supportProof, boxExpr, boundRat, cfgExpr]
          pure <| some (boxExpr, ast, boundRat, cfgExpr, proof)
        catch e =>
          saved.restore
          return .error <| .unsupported (toString func)
            (← e.toMessageData.toString)
      let some (boxExpr, ast, boundRat, cfgExpr, proof) := prepared
        | saved.restore
          return .error <| .unsupported (toString func)
            "multivariate preparation produced no expression"

      setGoals [goal]
      try
        evalTactic (← `(tactic| repeat intro))
      catch _ => pure ()

      let mainGoalAfterIntro ← getMainGoal

      let syntaxData ←
        try
          withMainContext do
            let varExprs ← getVarExprs vars
            let varsListExpr ← mkListLit (Lean.mkConst ``Real) varExprs.toList
            let rhoExpr ← mkEnvExpr varsListExpr
            let rhoSyntax ← Lean.Elab.Term.exprToSyntax rhoExpr
            let varsListSyntax ← Lean.Elab.Term.exprToSyntax varsListExpr
            let boxSyntax ← Lean.Elab.Term.exprToSyntax boxExpr
            pure <| some (rhoSyntax, varsListSyntax, boxSyntax)
        catch e =>
          saved.restore
          return .error <| .unsupported (toString func)
            (← e.toMessageData.toString)
      let some (rhoSyntax, varsListSyntax, boxSyntax) := syntaxData
        | saved.restore
          return .error <| .unsupported (toString func)
            "could not construct the multivariate environment"

      let checkExpr ← mkAppM ``checkGlobalLowerBound #[ast, boxExpr, boundRat, cfgExpr]
      let certTy ← mkAppM ``Eq #[checkExpr, Lean.mkConst ``Bool.true]
      let certGoal ← mkFreshExprMVar certTy
      let certGoalId := certGoal.mvarId!
      setGoals [certGoalId]
      let event ←
        match ← LeanCert.Tactic.closeCertificateGoalTyped
            (← LeanCert.Tactic.VerificationConfig.current) (← getMainGoal)
            (tacticName := "multivariate_bound") with
        | .accepted event => pure event
        | .rejected =>
            saved.restore
            return .error <| .rejected
              "the multivariate lower-bound checker evaluated to false"
        | .failed failure =>
            saved.restore
            return .error <| .internalFailure
              (failure.message "multivariate_bound")

      let conclusionProof ← mkAppM' proof #[certGoal]
      let conclusionTerm ← Lean.Elab.Term.exprToSyntax conclusionProof

      setGoals [mainGoalAfterIntro]
      try
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
        have hresult := $conclusionTerm $rhoSyntax hmem hzero
        convert hresult using 1 <;>
          simp [List.getD, LeanCert.Core.Expr.eval, Rat.divInt_eq_div,
            sq, pow_two, sub_eq_add_neg, div_eq_mul_inv] <;>
          ring
        )))
      catch e =>
        saved.restore
        return .error <| .transportFailure (← e.toMessageData.toString)
      return .ok event

/-- Reporting compatibility wrapper preserving the historical throwing API. -/
unsafe def multivariateBoundCoreReported (maxIters : Nat) (tolerance : ℚ)
    (useMonotonicity : Bool) (taylorDepth : Nat) :
    TacticM MultivariateBoundOutcome := do
  match ← multivariateBoundCoreTyped maxIters tolerance useMonotonicity
      taylorDepth with
  | .ok outcome => return outcome
  | .error (.unsupported expression detail) =>
      throwError "multivariate_bound: unsupported expression {expression}:\n{detail}"
  | .error (.rejected detail) =>
      throwError "multivariate_bound: certificate rejected:\n{detail}"
  | .error (.transportFailure detail) =>
      throwError "multivariate_bound: proof transport failed:\n{detail}"
  | .error (.internalFailure detail) =>
      throwError "multivariate_bound: internal verification failure:\n{detail}"

/-- Compatibility wrapper retaining the historical `TacticM Unit` API. -/
unsafe def multivariateBoundCore (maxIters : Nat) (tolerance : ℚ)
    (useMonotonicity : Bool) (taylorDepth : Nat) : TacticM Unit := do
  discard <| multivariateBoundCoreReported maxIters tolerance useMonotonicity taylorDepth

/-- The multivariate_bound tactic.

    Automatically proves bounds on multivariate expressions using global optimization.

    Usage:
    - `multivariate_bound` - uses defaults (1000 iterations, tolerance 1/1000, Taylor depth 10)
    - `multivariate_bound 2000` - uses 2000 iterations

    Supports goals of the form:
    - `∀ x ∈ I, ∀ y ∈ J, f(x,y) ≤ c`
    - `∀ x ∈ I, ∀ y ∈ J, c ≤ f(x,y)`
-/
syntax (name := multivariateBoundTac) "multivariate_bound" (num)?
  (leancertTrustItem)? : tactic

@[tactic multivariateBoundTac]
unsafe def elabMultivariateBound : Tactic := fun stx => do
  let iters := stx[1].getOptional?
  let t := stx[2].getOptional?.map (⟨·⟩)
  let trust? ← LeanCert.Tactic.elabTrustItem? t
  LeanCert.Tactic.withTrustMode trust? do
    let maxIters := match iters with
      | some n => n.toNat
      | none => 1000
    multivariateBoundCore maxIters (1/1000) false 10

end LeanCert.Tactic.Auto
