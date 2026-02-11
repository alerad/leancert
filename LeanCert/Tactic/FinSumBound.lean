/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import Lean
import LeanCert.Engine.FinSumDyadic
import LeanCert.Meta.ToExpr
import LeanCert.Meta.ProveSupported
import LeanCert.Tactic.IntervalAuto
import LeanCert.Tactic.FinSumWitness

/-!
# `finsum_bound`: O(1) Proof-Size Tactic for Finite Sum Bounds

Proves bounds of the form `∑ k ∈ Finset.Icc a b, f k ≤ target` (or `≥`)
using `native_decide` with O(1) proof size, regardless of the number of terms.

## Motivation

`finsum_expand` expands sums symbolically, creating O(N) proof terms that blow up
for N > ~100. `finsum_bound` uses an accumulator-based evaluator over `Core.Expr`
with `native_decide`, keeping proof size constant.

## Usage

```lean
-- Upper bound on harmonic-like sum
example : ∑ k ∈ Finset.Icc 1 100, (1 : ℝ) / (k * k) ≤ 2 := by
  finsum_bound

-- Lower bound
example : (4 : ℝ) ≤ ∑ k ∈ Finset.Icc 1 100, 1 / k := by
  finsum_bound

-- Higher precision
example : ∑ k ∈ Finset.Icc 1 500, (1 : ℝ) / (k * k) ≤ 2 := by
  finsum_bound 100
```

## Architecture

```
Parse goal → reify body (ℕ → ℝ) to Core.Expr
  → build ExprSupportedCore or ExprSupportedWithInv proof
  → build DyadicConfig
  → checkFinSumUpperBoundFull/LowerBoundFull : Bool (domain + bound)
  → native_decide
  → verify_finsum_upper_full/lower_full (bridge theorem)
```
-/

open Lean Meta Elab Tactic Term

namespace LeanCert.Tactic

open LeanCert.Meta
open LeanCert.Core
open LeanCert.Engine

initialize registerTraceClass `finsum_bound

/-! ## Goal Parsing -/

/-- Result of parsing a finite sum bound goal. -/
structure FinSumGoal where
  /-- Lower range bound (ℕ expression) -/
  aExpr : Lean.Expr
  /-- Upper range bound (ℕ expression) -/
  bExpr : Lean.Expr
  /-- Sum body as lambda (ℕ → ℝ) -/
  bodyLambda : Lean.Expr
  /-- Bound target (ℝ expression) -/
  targetExpr : Lean.Expr
  /-- true for `sum ≤ target`, false for `target ≤ sum` -/
  isUpper : Bool

/-- Extract `(a, b, f)` from `Finset.sum (Finset.Icc a b) f`. -/
private def extractFinsetIccSum (e : Lean.Expr) : Option (Lean.Expr × Lean.Expr × Lean.Expr) :=
  let fn := e.getAppFn
  let args := e.getAppArgs
  -- Finset.sum : {β} → {α} → [AddCommMonoid β] → Finset α → (α → β) → β
  -- args = [β, α, inst, s, f]
  if fn.isConstOf ``Finset.sum && args.size ≥ 5 then
    let s := args[3]!
    let f := args[4]!
    let sfn := s.getAppFn
    let sargs := s.getAppArgs
    -- Finset.Icc : {α} → [Preorder α] → [LocallyFiniteOrder α] → α → α → Finset α
    if sfn.isConstOf ``Finset.Icc && sargs.size ≥ 5 then
      some (sargs[3]!, sargs[4]!, f)
    else
      none
  else
    none

/-- Parse a goal of the form `∑ k ∈ Finset.Icc a b, f k ≤ target`
    or `target ≤ ∑ k ∈ Finset.Icc a b, f k`. -/
private def parseFinSumGoal (goalType : Lean.Expr) : Option FinSumGoal := do
  -- Match LE.le _ _ lhs rhs
  let_expr LE.le _ _ lhs rhs := goalType | none
  -- Check if lhs is a Finset.Icc sum
  if let some (a, b, f) := extractFinsetIccSum lhs then
    return { aExpr := a, bExpr := b, bodyLambda := f, targetExpr := rhs, isUpper := true }
  -- Check if rhs is a Finset.Icc sum
  if let some (a, b, f) := extractFinsetIccSum rhs then
    return { aExpr := a, bExpr := b, bodyLambda := f, targetExpr := lhs, isUpper := false }
  none

/-! ## Body Reification -/

/-- Replace occurrences of `Nat.cast k` (where `k` is the given fvar) with
    a replacement expression. Checks both `Nat.cast` and `NatCast.natCast` forms. -/
private def replaceNatCast (body : Lean.Expr) (kFVarId : FVarId)
    (replacement : Lean.Expr) : Lean.Expr :=
  body.replace fun e =>
    let fn := e.getAppFn
    let args := e.getAppArgs
    if args.size ≥ 1 then
      let lastArg := args.back!
      if lastArg.isFVar && lastArg.fvarId! == kFVarId then
        if fn.isConstOf ``Nat.cast || fn.isConstOf ``NatCast.natCast then
          some replacement
        else none
      else none
    else none

/-- Reify a sum body lambda `(ℕ → ℝ)` to a `Core.Expr` AST.
    Replaces `Nat.cast k` with a real variable, then reifies. -/
private def reifyFinSumBody (bodyLambda : Lean.Expr) : MetaM Lean.Expr := do
  lambdaTelescope bodyLambda fun vars body => do
    if vars.size < 1 then
      throwError "finsum_bound: expected a lambda for the sum body"
    let k := vars[0]!
    let realTy := Lean.mkConst ``Real
    withLocalDeclD `_x realTy fun x => do
      -- Replace Nat.cast k with x
      let body' := replaceNatCast body k.fvarId! x
      -- Also try: if k appears bare (e.g. in Nat operations), this won't be caught.
      -- For now, we just reify what we can.
      let realLambda ← mkLambdaFVars #[x] body'
      reify realLambda

/-! ## Tactic Kernel -/

/-- Result of support level detection. -/
private inductive SupportLevel
  | core (proof : Lean.Expr)     -- ExprSupportedCore
  | withInv (proof : Lean.Expr)  -- ExprSupportedWithInv

/-- Try to build a support proof. Tries ExprSupportedCore first,
    then falls back to ExprSupportedWithInv for bodies with inv/atan/arsinh/atanh. -/
private def detectSupportLevel (ast : Lean.Expr) : MetaM SupportLevel := do
  try
    let proof ← mkSupportedCoreProof ast
    return .core proof
  catch _ =>
    try
      let proof ← mkSupportedWithInvProof ast
      return .withInv proof
    catch _ =>
      throwError "finsum_bound: could not prove ExprSupportedCore or ExprSupportedWithInv \
        for the reified body. The body may contain unsupported operations."

/-- Core implementation of `finsum_bound`. -/
private def finSumBoundCore (prec : Int) (taylorDepth : Nat) : TacticM Unit := do
  let goal ← getMainGoal
  let goalType ← goal.getType

  let some fsGoal := parseFinSumGoal goalType
    | throwError "finsum_bound: goal is not of the form \
        `∑ k ∈ Finset.Icc a b, f k ≤ target` or `target ≤ ∑ k ∈ Finset.Icc a b, f k`"

  goal.withContext do
    -- Extract target as rational
    let some target ← Auto.extractRatFromReal fsGoal.targetExpr
      | throwError "finsum_bound: could not extract rational from bound `{← ppExpr fsGoal.targetExpr}`"
    let targetExpr := toExpr target

    -- Reify the sum body
    let ast ← reifyFinSumBody fsGoal.bodyLambda
    trace[finsum_bound] "Reified AST: {ast}"

    -- Build support proof (try Core, fallback WithInv)
    let support ← detectSupportLevel ast

    -- Build configuration
    let precExpr := toExpr prec
    let depthExpr := toExpr taylorDepth
    let cfgExpr ← mkAppM ``DyadicConfig.mk #[precExpr, depthExpr, toExpr (0 : Nat)]

    -- Precision proof: prec ≤ 0
    let precLeZeroTy ← mkAppM ``LE.le #[precExpr, toExpr (0 : Int)]
    let precLeZeroProof ← mkDecideProof precLeZeroTy

    -- Build the combined certificate check expression (domain + bound in one check)
    let checkExpr ← if fsGoal.isUpper then
      mkAppM ``checkFinSumUpperBoundFull #[ast, fsGoal.aExpr, fsGoal.bExpr, targetExpr, cfgExpr]
    else
      mkAppM ``checkFinSumLowerBoundFull #[ast, fsGoal.aExpr, fsGoal.bExpr, targetExpr, cfgExpr]

    let checkEqTrue ← mkAppM ``Eq #[checkExpr, Lean.mkConst ``Bool.true]
    let checkMVar ← mkFreshExprMVar (some checkEqTrue) (kind := .syntheticOpaque)

    -- Select bridge theorem based on support level and direction
    let (bridgeThm, supportProof) := match support, fsGoal.isUpper with
      | .core p,    true  => (``verify_finsum_upper_full, p)
      | .core p,    false => (``verify_finsum_lower_full, p)
      | .withInv p, true  => (``verify_finsum_upper_full_withInv, p)
      | .withInv p, false => (``verify_finsum_lower_full_withInv, p)

    -- Build bridge theorem proof (no domain proof needed — it's in the checker)
    let proof ← mkAppM bridgeThm
      #[ast, supportProof, fsGoal.aExpr, fsGoal.bExpr, targetExpr, cfgExpr,
        precLeZeroProof, checkMVar]

    -- Try direct assignment (works if Expr.eval defEq to user's body AND target cast matches)
    let proofTy ← inferType proof
    if ← isDefEq proofTy goalType then
      goal.assign proof
      replaceMainGoal [checkMVar.mvarId!]
      evalTactic (← `(tactic| native_decide))
    else
      -- DefEq failed. Use suffices: prove the Expr.eval form, then convert to user's form.
      trace[finsum_bound] "Direct defEq failed, using suffices + simp fallback"

      -- Strategy: goal.assign (converter suffMVar) where converter : proofTy → goalType
      let suffMVar ← mkFreshExprMVar (some proofTy) (kind := .syntheticOpaque)
      let converterMVar ← mkFreshExprMVar
        (some (← mkArrow proofTy goalType)) (kind := .syntheticOpaque)
      goal.assign (mkApp converterMVar suffMVar)

      -- 1. Solve suffMVar: assign the bridge theorem proof
      suffMVar.mvarId!.assign proof

      -- 2. Solve checkMVar with native_decide
      setGoals [checkMVar.mvarId!]
      try
        evalTactic (← `(tactic| native_decide))
      catch e =>
        throwError "finsum_bound: native_decide failed on certificate check. \
          The bound may be too tight for precision ({prec}).\n\
          Try: `finsum_bound 100`.\n{e.toMessageData}"

      -- 3. Solve converterMVar: proofTy → goalType
      setGoals [converterMVar.mvarId!]
      try
        evalTactic (← `(tactic|
          intro h; simp only [Core.Expr.eval, Engine.sumBodyRealEnv] at h ⊢;
          norm_num at h ⊢; exact h))
      catch _ =>
        try
          evalTactic (← `(tactic|
            intro h; simp only [Core.Expr.eval, Engine.sumBodyRealEnv] at h ⊢;
            push_cast at h ⊢; linarith))
        catch _ =>
          throwError "finsum_bound: could not convert Expr.eval form to the user's goal.\n\
            Proof type: {← ppExpr proofTy}\n\
            Goal type: {← ppExpr goalType}"

/-! ## Main Tactic -/

/-- Prove bounds on finite sums with O(1) proof size.

    Handles goals:
    - `∑ k ∈ Finset.Icc a b, f k ≤ target`
    - `target ≤ ∑ k ∈ Finset.Icc a b, f k`

    Usage:
    - `finsum_bound` — auto-reify, default 53-bit precision
    - `finsum_bound 80` — auto-reify, 80-bit precision
    - `finsum_bound using myEval (fun k _ _ => myProof k _)` — witness mode
    - `finsum_bound using myEval myProof 100` — witness mode, 100-bit precision -/
syntax (name := finSumBound) "finsum_bound" ("using" term:max term:max)? (num)? : tactic

elab_rules : tactic
  | `(tactic| finsum_bound using $evalTerm:term $hmem:term $[$prec:num]?) => do
    let precision : Int := match prec with
      | some n => -(n.getNat : Int)
      | none => -53
    finSumWitnessCore evalTerm hmem precision
  | `(tactic| finsum_bound $[$prec:num]?) => do
    let precision : Int := match prec with
      | some n => -(n.getNat : Int)
      | none => -53
    finSumBoundCore precision 10

end LeanCert.Tactic
