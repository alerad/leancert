/-
Copyright (c) 2024 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Tactic.IntervalAuto.Basic
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

/-- The main root_bound tactic implementation -/
def rootBoundCore (taylorDepth : Nat) : TacticM Unit := do
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
    proveForallNeZero goal interval func taylorDepth

where
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
      (taylorDepth : Nat) : TacticM Unit := do
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
      let ast ← getAst func

      -- 2. Generate ExprSupportedCore proof
      let supportProof ← mkSupportedCoreProof ast

      -- 3. Build config expression
      let cfgExpr ← mkAppM ``EvalConfig.mk #[toExpr taylorDepth]

      -- 4. Apply verify_no_root theorem
      let proof ← mkAppM ``Validity.RootFinding.verify_no_root
        #[ast, supportProof, intervalExpr, cfgExpr]

      if fromSetIcc then
        -- Use simpa to bridge Set.Icc to IntervalRat
        let proofSyntax ← Term.exprToSyntax proof
        evalTactic (← `(tactic| refine (by
          have h := $proofSyntax (by native_decide)
          simpa [IntervalRat.mem_iff_mem_Icc] using h)))
      else
        -- 5. Apply the proof - this leaves the certificate check as a goal
        let newGoals ← goal.apply proof

        setGoals newGoals

        -- 6. Solve remaining goals with native_decide
        for g in newGoals do
          setGoals [g]
          evalTactic (← `(tactic| native_decide))

/-- The root_bound tactic.

    Automatically proves root-related properties using interval arithmetic.

    Usage:
    - `root_bound` - uses default Taylor depth of 10
    - `root_bound 20` - uses Taylor depth of 20

    Supports goals of the form:
    - `∀ x ∈ I, f x ≠ 0` (proves no root exists in interval)
-/
elab "root_bound" depth:(num)? : tactic => do
  let taylorDepth := match depth with
    | some n => n.getNat
    | none => 10
  rootBoundCore taylorDepth

end LeanCert.Tactic.Auto
