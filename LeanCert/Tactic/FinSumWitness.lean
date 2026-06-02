/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import Lean
import LeanCert.Engine.WitnessSum
import LeanCert.Tactic.IntervalAuto
import LeanCert.Tactic.BridgeNative
import LeanCert.Tactic.FinsetParse

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

/-- Parse a goal of the form `∑ k ∈ Finset.Icc a b, f k ≤ target`
    or `target ≤ ∑ k ∈ Finset.Icc a b, f k`. -/
private def parseWitnessGoal (goalType : Lean.Expr) : Option WitnessGoal := do
  let_expr LE.le _ _ lhs rhs := goalType | none
  if let some (a, b, f) := extractFinsetIccSum lhs then
    return { aExpr := a, bExpr := b, bodyLambda := f, targetExpr := rhs, isUpper := true }
  if let some (a, b, f) := extractFinsetIccSum rhs then
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

/-- Parse a witness goal for the list path. -/
private def parseWitnessGoalList (goalType : Lean.Expr) : MetaM (Option WitnessGoalList) := do
  let_expr LE.le _ _ lhs rhs := goalType | return none
  let tryExtract (sumSide otherSide : Lean.Expr) (isUpper : Bool) :
      MetaM (Option WitnessGoalList) := do
    if let some (finsetExpr, bodyLambda) := extractFinsetSum sumSide then
      if let some indices := ← extractFinsetElements finsetExpr then
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

    -- Apply bridge + native_decide (with converter fallback)
    closeBridgeWithNativeDecide goal goalType proof checkMVar "finsum_witness" #[
      do evalTactic (← `(tactic| intro h; exact h)),
      do evalTactic (← `(tactic| intro h; push_cast at h ⊢; linarith))
    ]

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

    -- Apply bridge + native_decide (with converter fallback)
    closeBridgeWithNativeDecide goal goalType proof checkMVar "finsum_witness" #[
      do evalTactic (← `(tactic| intro h; exact h)),
      do evalTactic (← `(tactic| intro h; push_cast at h ⊢; linarith))
    ]

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

/-- Try to auto-prove an hmem metavar using several strategies.
    Works best when the evaluator returns singletons or tight intervals
    where membership reduces to decidable ℚ comparisons. -/
private def tryAutoProveHmem (hmemMVar : MVarId) : TacticM Unit := do
  -- Strategy 1: simp [mem_def] + split into ≤ components + cast to ℚ + native_decide
  -- Works for constant evaluators (no free variables in the comparison)
  setGoals [hmemMVar]
  try
    evalTactic (← `(tactic|
      intros;
      simp only [IntervalDyadic.mem_def, IntervalDyadic.singleton];
      refine ⟨?_, ?_⟩ <;> exact_mod_cast (by native_decide)))
    return
  catch _ => pure ()
  -- Strategy 2: interval_cases to enumerate k, then per-case native_decide
  -- Works for k-dependent evaluators on Icc (bounds are concrete literals)
  setGoals [hmemMVar]
  try
    evalTactic (← `(tactic|
      intro k hlo hhi;
      interval_cases k <;> {
        simp only [IntervalDyadic.mem_def, IntervalDyadic.singleton];
        refine ⟨?_, ?_⟩ <;> exact_mod_cast (by native_decide)
      }))
    return
  catch _ => pure ()
  -- Strategy 3: fin_cases for list path (1 premise: k ∈ S)
  setGoals [hmemMVar]
  try
    evalTactic (← `(tactic|
      intro k hk;
      fin_cases hk <;> {
        simp only [IntervalDyadic.mem_def, IntervalDyadic.singleton];
        refine ⟨?_, ?_⟩ <;> exact_mod_cast (by native_decide)
      }))
    return
  catch _ => pure ()
  -- All strategies failed
  let hmemTy ← hmemMVar.getType
  throwError "finsum_bound auto: could not auto-prove membership.\n\
    Expected type: {← ppExpr hmemTy}\n\
    Provide hmem explicitly: `finsum_bound using evalTerm hmemProof`"

/-- Core implementation of `finsum_bound auto` for Icc goals. -/
private def finSumWitnessAutoIccCore (wGoal : WitnessGoal) (evalTermSyn : Syntax)
    (prec : Int) : TacticM Unit := do
  let goal ← getMainGoal
  let goalType ← goal.getType

  goal.withContext do
    let some target ← Auto.extractRatFromReal wGoal.targetExpr
      | throwError "finsum_bound auto: could not extract rational from bound \
          `{← ppExpr wGoal.targetExpr}`"
    let targetExpr := toExpr target

    let precExpr := toExpr prec
    let depthExpr := toExpr (10 : Nat)
    let cfgExpr ← mkAppM ``DyadicConfig.mk #[precExpr, depthExpr, toExpr (0 : Nat)]

    let evalTermTy ← mkArrow (Lean.mkConst ``Nat)
      (← mkArrow (Lean.mkConst ``DyadicConfig) (Lean.mkConst ``IntervalDyadic))
    let evalTermExpr ← Tactic.elabTermEnsuringType evalTermSyn (some evalTermTy)

    -- Build hmem type: ∀ k, a ≤ k → k ≤ b → f k ∈ evalTerm k cfg
    let natTy := Lean.mkConst ``Nat
    let hmemTy ← withLocalDeclD `k natTy fun k => do
      let akTy ← mkAppM ``LE.le #[wGoal.aExpr, k]
      let kbTy ← mkAppM ``LE.le #[k, wGoal.bExpr]
      let fk := (Lean.mkApp wGoal.bodyLambda k).headBeta
      let evalk := Lean.mkApp (Lean.mkApp evalTermExpr k) cfgExpr
      let memTy ← mkAppM ``Membership.mem #[evalk, fk]
      let body ← mkArrow akTy (← mkArrow kbTy memTy)
      mkForallFVars #[k] body

    -- Auto-prove hmem
    let hmemMVar ← mkFreshExprMVar (some hmemTy) (kind := .syntheticOpaque)
    let savedGoals ← getGoals
    tryAutoProveHmem hmemMVar.mvarId!
    setGoals savedGoals

    let hmemExpr := hmemMVar

    -- Rest is identical to finSumWitnessIccCore
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

    -- Apply bridge + native_decide (with converter fallback)
    closeBridgeWithNativeDecide goal goalType proof checkMVar "finsum_bound auto" #[
      do evalTactic (← `(tactic| intro h; exact h)),
      do evalTactic (← `(tactic| intro h; push_cast at h ⊢; linarith))
    ]

/-- Core implementation of `finsum_bound auto` for arbitrary Finsets (list path). -/
private def finSumWitnessAutoListCore (wGoal : WitnessGoalList) (evalTermSyn : Syntax)
    (prec : Int) : TacticM Unit := do
  let goal ← getMainGoal
  let goalType ← goal.getType

  goal.withContext do
    let some target ← Auto.extractRatFromReal wGoal.targetExpr
      | throwError "finsum_bound auto: could not extract rational from bound \
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

    -- Auto-prove hmem
    let hmemMVar ← mkFreshExprMVar (some hmemTy) (kind := .syntheticOpaque)
    let savedGoals ← getGoals
    tryAutoProveHmem hmemMVar.mvarId!
    setGoals savedGoals

    let hmemExpr := hmemMVar

    -- Rest is identical to finSumWitnessListCore
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

    -- Apply bridge + native_decide (with converter fallback)
    closeBridgeWithNativeDecide goal goalType proof checkMVar "finsum_bound auto" #[
      do evalTactic (← `(tactic| intro h; exact h)),
      do evalTactic (← `(tactic| intro h; push_cast at h ⊢; linarith))
    ]

/-- Main dispatch for auto-hmem mode: try Icc path first, then list path. -/
def finSumWitnessAutoCore (evalTermSyn : Syntax) (prec : Int) : TacticM Unit := do
  let goal ← getMainGoal
  let goalType ← goal.getType

  if let some wGoal := parseWitnessGoal goalType then
    finSumWitnessAutoIccCore wGoal evalTermSyn prec
    return

  if let some wGoalList := ← parseWitnessGoalList goalType then
    finSumWitnessAutoListCore wGoalList evalTermSyn prec
    return

  throwError "finsum_bound auto: goal is not of the form \
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
