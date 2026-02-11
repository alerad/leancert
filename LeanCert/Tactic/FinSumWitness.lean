/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import Lean
import LeanCert.Engine.WitnessSum
import LeanCert.Tactic.IntervalAuto

/-!
# `finsum_witness`: Tactic for Witness-Based Finite Sum Bounds

Proves bounds of the form `∑ k ∈ Finset.Icc a b, f k ≤ target` (or `≥`)
using a user-provided per-term evaluator + correctness proof,
via `native_decide` with O(1) proof size.

## Motivation

`finsum_bound` auto-reifies sum bodies to `Core.Expr`, which covers +, *, inv, exp, sin,
log, etc. Functions outside `Core.Expr` (like `rpow` in BKLNW's `x^(1/k - 1/3)`) need
a custom evaluator. `finsum_witness` lets the user provide:
1. A computable evaluator `Nat → DyadicConfig → IntervalDyadic`
2. A correctness proof that each term is contained in the evaluator's output

## Usage

```lean
-- User defines evaluator + correctness proof:
def myEval (k : Nat) (cfg : DyadicConfig) : IntervalDyadic := ...
theorem myEval_correct (k : Nat) (cfg : DyadicConfig) : myF k ∈ myEval k cfg := ...

-- Prove bound:
example : ∑ k ∈ Finset.Icc 1 100, myF k ≤ target := by
  finsum_witness myEval (fun k _ _ => myEval_correct k _)
```

## Architecture

```
Parse goal → extract a, b, body, target
  → elaborate user's evalTerm and hmem
  → build DyadicConfig
  → checkWitnessSumUpperBound/LowerBound : Bool
  → native_decide
  → verify_witness_sum_upper/lower (bridge theorem)
```
-/

open Lean Meta Elab Tactic Term

namespace LeanCert.Tactic

open LeanCert.Core
open LeanCert.Engine

initialize registerTraceClass `finsum_witness

/-! ## Goal Parsing -/

/-- Result of parsing a finite sum bound goal. -/
private structure WitnessGoal where
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
private def extractFinsetIccSum' (e : Lean.Expr) : Option (Lean.Expr × Lean.Expr × Lean.Expr) :=
  let fn := e.getAppFn
  let args := e.getAppArgs
  -- Finset.sum : {β} → {α} → [AddCommMonoid β] → Finset α → (α → β) → β
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
private def parseWitnessGoal (goalType : Lean.Expr) : Option WitnessGoal := do
  let_expr LE.le _ _ lhs rhs := goalType | none
  if let some (a, b, f) := extractFinsetIccSum' lhs then
    return { aExpr := a, bExpr := b, bodyLambda := f, targetExpr := rhs, isUpper := true }
  if let some (a, b, f) := extractFinsetIccSum' rhs then
    return { aExpr := a, bExpr := b, bodyLambda := f, targetExpr := lhs, isUpper := false }
  none

/-! ## Generalized Finset Parsing -/

/-- Result of parsing a witness goal over an arbitrary Finset. -/
private structure WitnessGoalList where
  /-- The Finset expression from the goal -/
  finsetExpr : Lean.Expr
  /-- The List Nat literal of elements -/
  indicesExpr : Lean.Expr
  /-- Sum body as lambda (ℕ → ℝ) -/
  bodyLambda : Lean.Expr
  /-- Bound target (ℝ expression) -/
  targetExpr : Lean.Expr
  /-- true for `sum ≤ target`, false for `target ≤ sum` -/
  isUpper : Bool

/-- Extract `(Finset, body)` from `Finset.sum S f`. -/
private def extractFinsetSum' (e : Lean.Expr) : Option (Lean.Expr × Lean.Expr) :=
  let fn := e.getAppFn
  let args := e.getAppArgs
  if fn.isConstOf ``Finset.sum && args.size ≥ 5 then
    some (args[3]!, args[4]!)
  else
    none

/-- Try to extract a Nat literal from a Lean expression. -/
private def extractNatLit' (e : Lean.Expr) : MetaM (Option Nat) := do
  if let some n := e.rawNatLit? then return some n
  let e' ← whnf e
  if let some n := e'.rawNatLit? then return some n
  return none

/-- Recursively extract elements from nested insert/singleton/empty Finset expressions. -/
private partial def tryExtractExplicitFinset' (e : Lean.Expr) : MetaM (Option (List Nat)) := do
  let fn := e.getAppFn
  let args := e.getAppArgs
  if fn.isConstOf ``Insert.insert && args.size ≥ 5 then
    if let some n := ← extractNatLit' args[3]! then
      if let some rest := ← tryExtractExplicitFinset' args[4]! then
        return some (n :: rest)
    return none
  if fn.isConstOf ``Finset.cons && args.size ≥ 4 then
    if let some n := ← extractNatLit' args[1]! then
      if let some rest := ← tryExtractExplicitFinset' args[2]! then
        return some (n :: rest)
    return none
  if fn.isConstOf ``Singleton.singleton && args.size ≥ 4 then
    if let some n := ← extractNatLit' args[3]! then
      return some [n]
    return none
  if fn.isConstOf ``EmptyCollection.emptyCollection then
    return some []
  let e' ← whnf e
  if e' != e then
    return ← tryExtractExplicitFinset' e'
  return none

/-- Extract Nat elements from a Finset expression. -/
private def extractFinsetElements' (finsetExpr : Lean.Expr) : MetaM (Option (List Nat)) := do
  let sfn := finsetExpr.getAppFn
  let sargs := finsetExpr.getAppArgs
  if sfn.isConstOf ``Finset.Icc && sargs.size ≥ 5 then
    if let (some a, some b) := (← extractNatLit' sargs[3]!, ← extractNatLit' sargs[4]!) then
      return some (List.range' a (b + 1 - a))
    return none
  if sfn.isConstOf ``Finset.Ico && sargs.size ≥ 5 then
    if let (some a, some b) := (← extractNatLit' sargs[3]!, ← extractNatLit' sargs[4]!) then
      return some (List.range' a (b - a))
    return none
  if sfn.isConstOf ``Finset.Ioc && sargs.size ≥ 5 then
    if let (some a, some b) := (← extractNatLit' sargs[3]!, ← extractNatLit' sargs[4]!) then
      return some (List.range' (a + 1) (b - a))
    return none
  if sfn.isConstOf ``Finset.Ioo && sargs.size ≥ 5 then
    if let (some a, some b) := (← extractNatLit' sargs[3]!, ← extractNatLit' sargs[4]!) then
      if b > a + 1 then
        return some (List.range' (a + 1) (b - a - 1))
      else
        return some []
    return none
  if sfn.isConstOf ``Finset.range && sargs.size ≥ 1 then
    if let some n := ← extractNatLit' sargs[0]! then
      return some (List.range n)
    return none
  tryExtractExplicitFinset' finsetExpr

/-- Parse a witness goal for the list path. -/
private def parseWitnessGoalList (goalType : Lean.Expr) : MetaM (Option WitnessGoalList) := do
  let_expr LE.le _ _ lhs rhs := goalType | return none
  let tryExtract (sumSide otherSide : Lean.Expr) (isUpper : Bool) :
      MetaM (Option WitnessGoalList) := do
    if let some (finsetExpr, bodyLambda) := extractFinsetSum' sumSide then
      if let some indices := ← extractFinsetElements' finsetExpr then
        let indicesExpr := toExpr indices
        return some { finsetExpr, indicesExpr, bodyLambda, targetExpr := otherSide, isUpper }
    return none
  if let some g := ← tryExtract lhs rhs true then return some g
  if let some g := ← tryExtract rhs lhs false then return some g
  return none

/-! ## Tactic Implementation -/

/-- Core implementation of `finsum_witness` for Icc goals. -/
private def finSumWitnessIccCore (wGoal : WitnessGoal) (evalTermSyn hmemSyn : Syntax)
    (prec : Int) : TacticM Unit := do
  let goal ← getMainGoal
  let goalType ← goal.getType

  goal.withContext do
    -- Extract target as rational
    let some target ← Auto.extractRatFromReal wGoal.targetExpr
      | throwError "finsum_witness: could not extract rational from bound \
          `{← ppExpr wGoal.targetExpr}`"
    let targetExpr := toExpr target

    -- Build configuration
    let precExpr := toExpr prec
    let depthExpr := toExpr (10 : Nat)
    let cfgExpr ← mkAppM ``DyadicConfig.mk #[precExpr, depthExpr, toExpr (0 : Nat)]

    -- Elaborate user's evalTerm
    let evalTermTy ← mkArrow (Lean.mkConst ``Nat)
      (← mkArrow (Lean.mkConst ``DyadicConfig) (Lean.mkConst ``IntervalDyadic))
    let evalTermExpr ← Tactic.elabTermEnsuringType evalTermSyn (some evalTermTy)

    -- Build the expected type for hmem:
    --   ∀ k, a ≤ k → k ≤ b → f k ∈ evalTerm k cfg
    let natTy := Lean.mkConst ``Nat
    let hmemTy ← withLocalDeclD `k natTy fun k => do
      let akTy ← mkAppM ``LE.le #[wGoal.aExpr, k]
      let kbTy ← mkAppM ``LE.le #[k, wGoal.bExpr]
      let fk := (Lean.mkApp wGoal.bodyLambda k).headBeta
      let evalk := Lean.mkApp (Lean.mkApp evalTermExpr k) cfgExpr
      let memTy ← mkAppM ``Membership.mem #[evalk, fk]
      let body ← mkArrow akTy (← mkArrow kbTy memTy)
      mkForallFVars #[k] body

    trace[finsum_witness] "Expected hmem type: {hmemTy}"

    let hmemExpr ← Tactic.elabTermEnsuringType hmemSyn (some hmemTy)

    let checkExpr ← if wGoal.isUpper then
      mkAppM ``checkWitnessSumUpperBound
        #[evalTermExpr, wGoal.aExpr, wGoal.bExpr, targetExpr, cfgExpr]
    else
      mkAppM ``checkWitnessSumLowerBound
        #[evalTermExpr, wGoal.aExpr, wGoal.bExpr, targetExpr, cfgExpr]

    let checkEqTrue ← mkAppM ``Eq #[checkExpr, Lean.mkConst ``Bool.true]
    let checkMVar ← mkFreshExprMVar (some checkEqTrue) (kind := .syntheticOpaque)

    let bridgeThm := if wGoal.isUpper then
      ``verify_witness_sum_upper
    else
      ``verify_witness_sum_lower
    let proof ← mkAppM bridgeThm
      #[wGoal.bodyLambda, evalTermExpr, wGoal.aExpr, wGoal.bExpr,
        targetExpr, cfgExpr, hmemExpr, checkMVar]

    let proofTy ← inferType proof
    if ← isDefEq proofTy goalType then
      goal.assign proof
      replaceMainGoal [checkMVar.mvarId!]
      evalTactic (← `(tactic| native_decide))
    else
      trace[finsum_witness] "Direct defEq failed, using suffices fallback"

      let suffMVar ← mkFreshExprMVar (some proofTy) (kind := .syntheticOpaque)
      let converterMVar ← mkFreshExprMVar
        (some (← mkArrow proofTy goalType)) (kind := .syntheticOpaque)
      goal.assign (mkApp converterMVar suffMVar)

      suffMVar.mvarId!.assign proof

      setGoals [checkMVar.mvarId!]
      try
        evalTactic (← `(tactic| native_decide))
      catch e =>
        throwError "finsum_witness: native_decide failed on certificate check. \
          The bound may be too tight for precision ({prec}).\n\
          Try: `finsum_witness ... 100`.\n{e.toMessageData}"

      setGoals [converterMVar.mvarId!]
      try
        evalTactic (← `(tactic| intro h; exact h))
      catch _ =>
        try
          evalTactic (← `(tactic| intro h; push_cast at h ⊢; linarith))
        catch _ =>
          throwError "finsum_witness: could not convert proof type to goal type.\n\
            Proof type: {← ppExpr proofTy}\n\
            Goal type: {← ppExpr goalType}"

/-- Core implementation of `finsum_witness` for arbitrary Finsets (list path). -/
private def finSumWitnessListCore (wGoal : WitnessGoalList) (evalTermSyn hmemSyn : Syntax)
    (prec : Int) : TacticM Unit := do
  let goal ← getMainGoal
  let goalType ← goal.getType

  goal.withContext do
    let some target ← Auto.extractRatFromReal wGoal.targetExpr
      | throwError "finsum_witness: could not extract rational from bound \
          `{← ppExpr wGoal.targetExpr}`"
    let targetExpr := toExpr target

    let precExpr := toExpr prec
    let depthExpr := toExpr (10 : Nat)
    let cfgExpr ← mkAppM ``DyadicConfig.mk #[precExpr, depthExpr, toExpr (0 : Nat)]

    let evalTermTy ← mkArrow (Lean.mkConst ``Nat)
      (← mkArrow (Lean.mkConst ``DyadicConfig) (Lean.mkConst ``IntervalDyadic))
    let evalTermExpr ← Tactic.elabTermEnsuringType evalTermSyn (some evalTermTy)

    -- Build hmem type: ∀ k, k ∈ S → f k ∈ evalTerm k cfg
    let natTy := Lean.mkConst ``Nat
    let hmemTy ← withLocalDeclD `k natTy fun k => do
      let memSTy ← mkAppM ``Membership.mem #[wGoal.finsetExpr, k]
      let fk := (Lean.mkApp wGoal.bodyLambda k).headBeta
      let evalk := Lean.mkApp (Lean.mkApp evalTermExpr k) cfgExpr
      let memEvalTy ← mkAppM ``Membership.mem #[evalk, fk]
      let body ← mkArrow memSTy memEvalTy
      mkForallFVars #[k] body

    trace[finsum_witness] "Expected hmem type (list path): {hmemTy}"

    let hmemExpr ← Tactic.elabTermEnsuringType hmemSyn (some hmemTy)

    -- Build combined check (S = indices.toFinset ∧ Nodup ∧ bound)
    let checkExpr ← if wGoal.isUpper then
      mkAppM ``checkWitnessSumUpperBoundListFull
        #[evalTermExpr, wGoal.finsetExpr, wGoal.indicesExpr, targetExpr, cfgExpr]
    else
      mkAppM ``checkWitnessSumLowerBoundListFull
        #[evalTermExpr, wGoal.finsetExpr, wGoal.indicesExpr, targetExpr, cfgExpr]

    let checkEqTrue ← mkAppM ``Eq #[checkExpr, Lean.mkConst ``Bool.true]
    let checkMVar ← mkFreshExprMVar (some checkEqTrue) (kind := .syntheticOpaque)

    let bridgeThm := if wGoal.isUpper then
      ``verify_witness_sum_upper_list_full
    else
      ``verify_witness_sum_lower_list_full
    let proof ← mkAppM bridgeThm
      #[wGoal.bodyLambda, evalTermExpr, wGoal.finsetExpr, wGoal.indicesExpr,
        targetExpr, cfgExpr, hmemExpr, checkMVar]

    let proofTy ← inferType proof
    if ← isDefEq proofTy goalType then
      goal.assign proof
      replaceMainGoal [checkMVar.mvarId!]
      evalTactic (← `(tactic| native_decide))
    else
      trace[finsum_witness] "Direct defEq failed (list path), using suffices fallback"

      let suffMVar ← mkFreshExprMVar (some proofTy) (kind := .syntheticOpaque)
      let converterMVar ← mkFreshExprMVar
        (some (← mkArrow proofTy goalType)) (kind := .syntheticOpaque)
      goal.assign (mkApp converterMVar suffMVar)

      suffMVar.mvarId!.assign proof

      setGoals [checkMVar.mvarId!]
      try
        evalTactic (← `(tactic| native_decide))
      catch e =>
        throwError "finsum_witness: native_decide failed on certificate check. \
          The bound may be too tight for precision ({prec}).\n\
          Try: `finsum_witness ... 100`.\n{e.toMessageData}"

      setGoals [converterMVar.mvarId!]
      try
        evalTactic (← `(tactic| intro h; exact h))
      catch _ =>
        try
          evalTactic (← `(tactic| intro h; push_cast at h ⊢; linarith))
        catch _ =>
          throwError "finsum_witness: could not convert proof type to goal type.\n\
            Proof type: {← ppExpr proofTy}\n\
            Goal type: {← ppExpr goalType}"

/-- Main dispatch: try Icc path first, then list path. -/
def finSumWitnessCore (evalTermSyn hmemSyn : Syntax) (prec : Int) : TacticM Unit := do
  let goal ← getMainGoal
  let goalType ← goal.getType

  -- Try Icc path first
  if let some wGoal := parseWitnessGoal goalType then
    finSumWitnessIccCore wGoal evalTermSyn hmemSyn prec
    return

  -- Fall back to general list path
  if let some wGoalList := ← parseWitnessGoalList goalType then
    finSumWitnessListCore wGoalList evalTermSyn hmemSyn prec
    return

  throwError "finsum_witness: goal is not of the form \
    `∑ k ∈ S, f k ≤ target` or `target ≤ ∑ k ∈ S, f k` \
    where S is a recognized Finset (Icc, Ico, Ioc, Ioo, range, or explicit)"

/-! ## Main Tactic -/

/-- Prove bounds on finite sums using a witness evaluator.

    The user provides:
    - `evalTerm` : `Nat → DyadicConfig → IntervalDyadic` — computable per-term evaluator
    - `hmem` : proof that `∀ k, a ≤ k → k ≤ b → f k ∈ evalTerm k cfg`

    Usage:
    - `finsum_witness myEval using (fun k _ _ => myCorrectness k _)`
    - `finsum_witness myEval using myProof 100` — with 100-bit precision -/
elab "finsum_witness" evalTerm:term "using" hmem:term prec:(num)? : tactic => do
  let precision : Int := match prec with
    | some n => -(n.getNat : Int)
    | none => -53
  finSumWitnessCore evalTerm hmem precision

end LeanCert.Tactic
