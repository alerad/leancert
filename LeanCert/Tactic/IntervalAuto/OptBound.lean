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
# Global Optimization Tactic

The `opt_bound` tactic handles goals using global branch-and-bound optimization.
-/

open Lean Meta Elab Tactic Term

namespace LeanCert.Tactic.Auto

open LeanCert.Meta
open LeanCert.Core
open LeanCert.Engine
open LeanCert.Validity
open LeanCert.Engine.Optimization

/-- Build a GlobalOptConfig expression -/
def mkGlobalOptConfigExpr (maxIters : Nat) (tolerance : ℚ) (useMonotonicity : Bool) (taylorDepth : Nat) : MetaM Lean.Expr := do
  mkAppM ``GlobalOptConfig.mk #[toExpr maxIters, toExpr tolerance, toExpr useMonotonicity, toExpr taylorDepth]

/-- Runtime facts from the retained global-optimization certificate. -/
inductive OptimizationDirection where
  | upper
  | lower
  deriving DecidableEq, Repr, Inhabited

structure OptBoundOutcome where
  direction : OptimizationDirection
  checker : Name
  verifier : Name
  verification : LeanCert.Tactic.VerificationUsage
  maxIterations : Nat
  tolerance : ℚ
  useMonotonicity : Bool
  taylorDepth : Nat
  deriving Inhabited

inductive OptBoundFailure where
  | unsupported (expression detail : String)
  | transportFailure (detail : String)
  | internalFailure (detail : String)
  deriving Inhabited, Repr

/-- Typed `opt_bound` implementation. The upper and lower theorem
interpretations are transactional, and only the retained certificate
contributes verification telemetry. -/
unsafe def optBoundCoreTyped (maxIters : Nat) (useMonotonicity : Bool)
    (taylorDepth : Nat) : TacticM (Except OptBoundFailure OptBoundOutcome) := do
  let tolerance : ℚ := 1 / 1000
  let cfgExpr ← mkGlobalOptConfigExpr maxIters tolerance useMonotonicity taylorDepth
  let cfgSyntax ← Term.exprToSyntax cfgExpr
  let goalType ← (← getMainGoal).getType
  let rec hasBinders (count : Nat) (type : Lean.Expr) : MetaM Bool := do
    if count == 0 then return true
    match ← whnf type with
    | .forallE _ _ body _ => hasBinders (count - 1) body
    | _ => return false
  unless ← hasBinders 3 goalType do
    return .error <| .unsupported (toString goalType)
      "expected three quantified/implication binders before a global bound"
  let rec stripBinders (count : Nat) (type : Lean.Expr) : MetaM (Option Lean.Expr) := do
    if count == 0 then return some type
    match ← whnf type with
    | .forallE _ _ body _ => stripBinders (count - 1) body
    | _ => return none
  let direction ←
    match ← stripBinders 3 goalType with
    | none => pure none
    | some body =>
        let comparison := body
        let args := comparison.getAppArgs
        if comparison.getAppFn.isConstOf ``LE.le && args.size ≥ 4 then
          let lhs := args[2]!
          let rhs := args[3]!
          if isExprEval lhs then pure <| some OptimizationDirection.upper
          else if isExprEval rhs then pure <| some OptimizationDirection.lower
          else pure none
        else pure none
  let some direction := direction
    | return .error <| .unsupported (toString (← (← getMainGoal).getType))
        "expected a checked global upper- or lower-bound theorem shape"
  let tryDirection (direction : OptimizationDirection) (checker verifier : Name) :
      TacticM (Except OptBoundFailure OptBoundOutcome) := do
    let saved ← saveState
    try
      match direction with
      | .upper =>
          evalTactic (← `(tactic|
            apply LeanCert.Validity.GlobalOpt.verify_global_upper_bound
              (cfg := $cfgSyntax)))
      | .lower =>
          evalTactic (← `(tactic|
            apply LeanCert.Validity.GlobalOpt.verify_global_lower_bound
              (cfg := $cfgSyntax)))
    catch e =>
      saved.restore
      return .error <| .transportFailure (← e.toMessageData.toString)
    let newGoals ← getGoals
    let mut verification : LeanCert.Tactic.VerificationUsage := {}
    for subgoal in newGoals do
      setGoals [subgoal]
      let subgoalType ← subgoal.getType
      if subgoalType.getAppFn.isConstOf ``ADSupported then
      try
        proveSupport subgoal
        pruneSolvedGoals
      catch e =>
        saved.restore
        return .error <| .transportFailure (← e.toMessageData.toString)
      else
        let args := subgoalType.getAppArgs
        unless subgoalType.getAppFn.isConstOf ``Eq && args.size == 3 do
          saved.restore
          return .error <| .internalFailure
            s!"expected a Boolean certificate equality, got {subgoalType}"
        let event ←
          try
            LeanCert.Tactic.closeCertificateGoalReported
              (← LeanCert.Tactic.VerificationConfig.current) subgoal
              (tacticName := "opt_bound")
          catch e =>
            saved.restore
            return .error <| .internalFailure (← e.toMessageData.toString)
        verification := verification.combine event.toUsage
    unless (← getGoals).isEmpty do
      saved.restore
      return .error <| .transportFailure
        "verified optimization certificate left unresolved proof obligations"
    return .ok {
      direction
      checker
      verifier
      verification
      maxIterations := maxIters
      tolerance
      useMonotonicity
      taylorDepth
    }
  match direction with
  | .upper =>
      tryDirection direction
        ``LeanCert.Validity.GlobalOpt.checkGlobalUpperBound
        ``LeanCert.Validity.GlobalOpt.verify_global_upper_bound
  | .lower =>
      tryDirection direction
        ``LeanCert.Validity.GlobalOpt.checkGlobalLowerBound
        ``LeanCert.Validity.GlobalOpt.verify_global_lower_bound

where
  /-- Prove ExprSupportedCore goal by generating the proof -/
  proveSupport (goal : MVarId) : TacticM Unit := do
    goal.withContext do
      let gType ← goal.getType
      let args := gType.getAppArgs
      if args.size ≥ 1 then
        let expr ← withTransparency .all <| whnf args[0]!
        let proof ← mkSupportedProof expr
        goal.assign proof

/-- Reporting compatibility wrapper preserving the historical throwing API. -/
unsafe def optBoundCoreReported (maxIters : Nat) (useMonotonicity : Bool)
    (taylorDepth : Nat) : TacticM OptBoundOutcome := do
  match ← optBoundCoreTyped maxIters useMonotonicity taylorDepth with
  | .ok outcome => return outcome
  | .error (.unsupported expression detail) =>
      throwError "opt_bound: unsupported goal {expression}:\n{detail}"
  | .error (.transportFailure detail) =>
      throwError "opt_bound: proof transport failed:\n{detail}"
  | .error (.internalFailure detail) =>
      throwError "opt_bound: internal verification failure:\n{detail}"

/-- Compatibility wrapper retaining the historical `TacticM Unit` API. -/
unsafe def optBoundCore (maxIters : Nat) (useMonotonicity : Bool)
    (taylorDepth : Nat) : TacticM Unit := do
  discard <| optBoundCoreReported maxIters useMonotonicity taylorDepth

/-- The opt_bound tactic.

    Automatically proves global bounds on expressions over boxes using
    branch-and-bound optimization.

    Usage:
    - `opt_bound` - uses defaults (1000 iterations, no monotonicity, Taylor depth 10)
    - `opt_bound 2000` - uses 2000 iterations
    - `opt_bound 1000 mono` - enables monotonicity pruning

    Supports goals of the form:
    - `∀ ρ, Box.envMem ρ B → (∀ i, i ≥ B.length → ρ i = 0) → c ≤ Expr.eval ρ e`
    - `∀ ρ, Box.envMem ρ B → (∀ i, i ≥ B.length → ρ i = 0) → Expr.eval ρ e ≤ c`
-/
syntax (name := optBoundTac) "opt_bound" (num)? ("mono")?
  (leancertTrustItem)? : tactic

@[tactic optBoundTac]
unsafe def elabOptBound : Tactic := fun stx => do
  let iters := stx[1].getOptional?
  let monoOpt := stx[2].getOptional?
  let t := stx[3].getOptional?.map (⟨·⟩)
  let trust? ← LeanCert.Tactic.elabTrustItem? t
  LeanCert.Tactic.withTrustMode trust? do
    let maxIters := match iters with
      | some n => n.toNat
      | none => 1000
    let useMonotonicity := monoOpt.isSome
    optBoundCore maxIters useMonotonicity 10

end LeanCert.Tactic.Auto
