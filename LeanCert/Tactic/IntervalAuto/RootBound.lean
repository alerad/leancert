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
# Root Finding Tactic

The `root_bound` tactic proves `∀ x ∈ I, f x ≠ 0` using interval arithmetic.
-/

open Lean Meta Elab Tactic Term

namespace LeanCert.Tactic.Auto

open LeanCert.Meta
open LeanCert.Core
open LeanCert.Engine
open LeanCert.Validity

/-- Runtime facts from a retained no-root certificate. -/
structure RootBoundOutcome where
  checker : Name
  verifier : Name
  verification : LeanCert.Tactic.VerificationUsage
  taylorDepth : Nat
  deriving Inhabited

/-- Reporting-aware root-bound implementation. -/
def rootBoundCoreReported (taylorDepth : Nat) : TacticM RootBoundOutcome := do
  let goal ← getMainGoal
  let goalType ← goal.getType

  -- Parse the goal
  let some rootGoal ← parseRootGoal goalType
    | let diagReport ← mkDiagnosticReport "root_bound" goalType "parse"
        (some m!"Expected form: ∀ x ∈ I, f x ≠ 0\n\n\
                 The function f must be continuous and supported by LeanCert.\n\
                 The interval I must be Set.Icc or equivalent.")
      throwError "root_bound: Could not parse goal as a root goal.\n\n{diagReport}"

  match rootGoal with
  | .forallNeZero _name interval func =>
    let event ← proveForallNeZero goal interval func taylorDepth
    return {
      checker := ``Validity.RootFinding.checkNoRoot
      verifier := ``Validity.RootFinding.verify_no_root
      verification := event.toUsage
      taylorDepth := taylorDepth
    }

where
  /-- Extract an AST and retain definitions unfolded during reification. -/
  getAst (func : Lean.Expr) : TacticM LeanCert.Meta.ReifyReport := do
    lambdaTelescope func fun _vars body => do
      let fn := body.getAppFn
      if fn.isConstOf ``LeanCert.Core.Expr.eval then
        let args := body.getAppArgs
        if args.size ≥ 2 then
          return { expr := args[1]! }
        else
          throwError m!"Unexpected Expr.eval application structure.\n\
                        Expected: Expr.eval env ast\n\
                        Got {args.size} arguments: {args.toList}"
      else
        reifyWithReport func

  /-- Try to convert Set.Icc to IntervalRat for root_bound -/
  tryConvertSetIccForRootBound (interval : Lean.Expr) : MetaM (Option Lean.Expr) := do
    let fn := interval.getAppFn
    let args := interval.getAppArgs
    if fn.isConstOf ``Set.Icc && args.size >= 4 then
      let loExpr := args[2]!
      let hiExpr := args[3]!
      if let some lo ← extractRatFromReal loExpr then
        if let some hi ← extractRatFromReal hiExpr then
          let loRatExpr := toExpr lo
          let hiRatExpr := toExpr hi
          let leProofTy ← mkAppM ``LE.le #[loRatExpr, hiRatExpr]
          let leProof ← mkDecideProof leProofTy
          let intervalRat ← mkAppM ``IntervalRat.mk #[loRatExpr, hiRatExpr, leProof]
          return some intervalRat
    return none

  /-- Prove ∀ x ∈ I, f x ≠ 0 using verify_no_root -/
  proveForallNeZero (goal : MVarId) (interval func : Lean.Expr)
      (taylorDepth : Nat) : TacticM LeanCert.Tactic.VerificationEvent := do
    goal.withContext do
      -- 0. Try to convert Set.Icc to IntervalRat if needed
      let mut fromSetIcc := false
      let intervalExpr ←
        match ← tryConvertSetIccForRootBound interval with
        | some intervalRat =>
            fromSetIcc := true
            pure intervalRat
        | none =>
            let intervalTy ← inferType interval
            if intervalTy.isConstOf ``IntervalRat then
              pure interval
            else
              throwError "root_bound: Only IntervalRat or literal Set.Icc intervals are supported"

      -- 1. Get AST
      let reified ← getAst func
      let ast := reified.expr

      -- Keep the user's goal synchronized with definitions delta-reduced by
      -- reification.  The verifier conclusion can then be bridged with the
      -- fixed arithmetic normalization below.
      unfoldReifiedDefinitions reified.unfolded

      -- 2. Generate ExprSupportedCore proof
      let supportProof ← mkSupportedCoreProof ast

      -- 3. Build config expression
      let cfgExpr ← mkAppM ``EvalConfig.mk #[toExpr taylorDepth]

      -- 4. Apply verify_no_root theorem
      let proof ← mkAppM ``Validity.RootFinding.verify_no_root
        #[ast, supportProof, intervalExpr, cfgExpr]
      let checkExpr ← mkAppM ``Validity.RootFinding.checkNoRoot
        #[ast, intervalExpr, cfgExpr]
      let certTy ← mkAppM ``Eq #[checkExpr, mkConst ``Bool.true]
      let certGoal ← mkFreshExprMVar certTy
      let event ← LeanCert.Tactic.closeCertificateGoalReported
        (← LeanCert.Tactic.VerificationConfig.current) certGoal.mvarId!
        (tacticName := "root_bound")
      let conclusionProof ← mkAppM' proof #[certGoal]

      if fromSetIcc then
        -- Use simpa to bridge Set.Icc to IntervalRat
        let proofSyntax ← Term.exprToSyntax conclusionProof
        evalTactic (← `(tactic| exact (by
          have h := $proofSyntax
          simpa [IntervalRat.mem_iff_mem_Icc, sub_eq_add_neg, sq, pow_two] using h)))
      else
        goal.assign conclusionProof
        replaceMainGoal []
      return event

/-- Compatibility wrapper retaining the historical `TacticM Unit` API. -/
def rootBoundCore (taylorDepth : Nat) : TacticM Unit := do
  discard <| rootBoundCoreReported taylorDepth

/-- The root_bound tactic.

    Automatically proves root-related properties using interval arithmetic.

    Usage:
    - `root_bound` - uses default Taylor depth of 10
    - `root_bound 20` - uses Taylor depth of 20

    Supports goals of the form:
    - `∀ x ∈ I, f x ≠ 0` (proves no root exists in interval)
-/
elab "root_bound" depth:(num)? t:(leancertTrustItem)? : tactic => do
  withTrustMode (← elabTrustItem? t) do
    let taylorDepth := match depth with
      | some n => n.getNat
      | none => 10
    rootBoundCore taylorDepth

end LeanCert.Tactic.Auto
