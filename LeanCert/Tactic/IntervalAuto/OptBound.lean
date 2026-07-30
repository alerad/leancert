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
structure OptBoundOutcome where
  checker : Name
  verifier : Name
  verification : LeanCert.Tactic.VerificationUsage
  maxIterations : Nat
  useMonotonicity : Bool
  taylorDepth : Nat
  deriving Inhabited

/-- The reporting-aware `opt_bound` implementation. Candidate search is an
implementation detail; this reports only the checker that closed the proof. -/
def optBoundCoreReported (maxIters : Nat) (useMonotonicity : Bool)
    (taylorDepth : Nat) : TacticM OptBoundOutcome := do
  let cfgExpr ← mkGlobalOptConfigExpr maxIters ((1 : ℚ)/1000) useMonotonicity taylorDepth

  -- First try applying upper bound theorem (for f(ρ) ≤ c goals)
  let goal ← getMainGoal
  let upperState ← saveState
  try
    let proof ← mkAppOptM ``LeanCert.Validity.GlobalOpt.verify_global_upper_bound
      #[none, none, none, none, some cfgExpr]
    let newGoals ← goal.apply proof
    setGoals newGoals
    let goals ← getGoals
    let mut verification : LeanCert.Tactic.VerificationUsage := {}
    for g in goals do
      setGoals [g]
      let gType ← g.getType
      if gType.getAppFn.isConstOf ``ExprSupportedCore then
        proveSupport g
      else
        let event ← LeanCert.Tactic.closeCertificateGoalReported
          (← LeanCert.Tactic.VerificationConfig.current) (← getMainGoal)
          (tacticName := "opt_bound")
        verification := verification.combine event.toUsage
    return {
      checker := ``LeanCert.Validity.GlobalOpt.checkGlobalUpperBound
      verifier := ``LeanCert.Validity.GlobalOpt.verify_global_upper_bound
      verification, maxIterations := maxIters, useMonotonicity, taylorDepth
    }
  catch _ => upperState.restore

  -- Try lower bound theorem (for c ≤ f(ρ) goals)
  let goal ← getMainGoal
  let lowerState ← saveState
  try
    let proof ← mkAppOptM ``LeanCert.Validity.GlobalOpt.verify_global_lower_bound
      #[none, none, none, none, some cfgExpr]
    let newGoals ← goal.apply proof
    setGoals newGoals
    let goals ← getGoals
    let mut verification : LeanCert.Tactic.VerificationUsage := {}
    for g in goals do
      setGoals [g]
      let gType ← g.getType
      if gType.getAppFn.isConstOf ``ExprSupportedCore then
        proveSupport g
      else
        let event ← LeanCert.Tactic.closeCertificateGoalReported
          (← LeanCert.Tactic.VerificationConfig.current) (← getMainGoal)
          (tacticName := "opt_bound")
        verification := verification.combine event.toUsage
    return {
      checker := ``LeanCert.Validity.GlobalOpt.checkGlobalLowerBound
      verifier := ``LeanCert.Validity.GlobalOpt.verify_global_lower_bound
      verification, maxIterations := maxIters, useMonotonicity, taylorDepth
    }
  catch _ => lowerState.restore

  throwError "opt_bound: Could not apply global bound theorem. Check that goal has form:\n\
              • ∀ ρ, Box.envMem ρ B → (∀ i ≥ B.length, ρ i = 0) → c ≤ Expr.eval ρ e\n\
              • ∀ ρ, Box.envMem ρ B → (∀ i ≥ B.length, ρ i = 0) → Expr.eval ρ e ≤ c"

where
  /-- Prove ExprSupportedCore goal by generating the proof -/
  proveSupport (goal : MVarId) : TacticM Unit := do
    goal.withContext do
      let gType ← goal.getType
      let args := gType.getAppArgs
      if args.size ≥ 1 then
        let expr := args[0]!
        let proof ← mkSupportedCoreProof expr
        goal.assign proof

/-- Compatibility wrapper retaining the historical `TacticM Unit` API. -/
def optBoundCore (maxIters : Nat) (useMonotonicity : Bool)
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
elab "opt_bound" iters:(num)? mono:("mono")?
    t:(leancertTrustItem)? : tactic => do
  let trust? ← LeanCert.Tactic.elabTrustItem? t
  LeanCert.Tactic.withTrustMode trust? do
    let maxIters := match iters with
      | some n => n.getNat
      | none => 1000
    let useMonotonicity := mono.isSome
    optBoundCore maxIters useMonotonicity 10

end LeanCert.Tactic.Auto
