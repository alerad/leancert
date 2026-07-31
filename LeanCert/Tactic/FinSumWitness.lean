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

/-- Computational route used for a finite-sum certificate. -/
inductive FinSumPath where
  | reifiedRange
  | reifiedExplicit
  | witnessRange
  | witnessExplicit
  deriving Repr, Inhabited, BEq

/-- Runtime facts retained from a successful finite-sum proof. -/
structure FinSumOutcome where
  path : FinSumPath
  isUpper : Bool
  rewrittenFin : Bool := false
  termCount : Nat
  precision : Int
  taylorDepth : Nat
  enclosure : IntervalRat
  checker : Name
  verifier : Name
  verification : VerificationUsage
  deriving Inhabited

/-- Typed finite-sum failures shared by reified and witness routes. -/
inductive FinSumFailure where
  | unsupported (detail : String)
  | domainObstruction (index : Option Nat) (detail : String)
  | rejected (checker : Name) (enclosure : Option IntervalRat)
  | verificationFailure (detail : String)
  | transportFailure (detail : String)
  | internalFailure (detail : String)
  deriving Inhabited, Repr

private def bridgeFailureToFinSum : BridgeFailure → FinSumFailure
  | .rejected => .rejected Name.anonymous none
  | .verificationFailure detail => .verificationFailure detail
  | .transportFailure detail => .transportFailure detail

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
    (prec : Int) : TacticM (Except FinSumFailure FinSumOutcome) := do
  let goal ← getMainGoal
  let goalType ← goal.getType

  goal.withContext do
    -- Extract target as rational
    let some target ← Auto.extractRatFromReal wGoal.targetExpr
      | return .error <| .unsupported
          s!"bound is not rational: {← ppExpr wGoal.targetExpr}"
    let targetExpr := toExpr target

    -- Build configuration
    let precExpr := toExpr prec
    let depthExpr := toExpr (10 : Nat)
    let cfgExpr ← mkAppM ``DyadicConfig.mk #[precExpr, depthExpr]

    -- Elaborate user's evalTerm
    let evalTermTy ← mkArrow (Lean.mkConst ``Nat)
      (← mkArrow (Lean.mkConst ``DyadicConfig) (Lean.mkConst ``IntervalDyadic))
    let evalTermExpr ←
      try Tactic.elabTermEnsuringType evalTermSyn (some evalTermTy)
      catch e =>
        return .error <| .unsupported
          s!"malformed witness evaluator: {← e.toMessageData.toString}"

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

    let hmemExpr ←
      try Tactic.elabTermEnsuringType hmemSyn (some hmemTy)
      catch e =>
        return .error <| .unsupported
          s!"malformed witness proof: {← e.toMessageData.toString}"

    let some a ← extractNatLit wGoal.aExpr
      | return .error <| .unsupported "range lower endpoint is not a natural literal"
    let some b ← extractNatLit wGoal.bExpr
      | return .error <| .unsupported "range upper endpoint is not a natural literal"
    let checkerName := if wGoal.isUpper then
      ``checkWitnessSumUpperBound else ``checkWitnessSumLowerBound
    let verifierName := if wGoal.isUpper then
      ``verify_witness_sum_upper else ``verify_witness_sum_lower
    let enclosureExpr ← mkAppM ``witnessSumDyadic
      #[evalTermExpr, wGoal.aExpr, wGoal.bExpr, cfgExpr]
    let enclosure ← unsafe evalExpr IntervalDyadic (mkConst ``IntervalDyadic) enclosureExpr
    let enclosureRat := enclosure.toIntervalRat
    unless (if wGoal.isUpper then enclosureRat.hi ≤ target else target ≤ enclosureRat.lo) do
      return .error <| .rejected checkerName (some enclosureRat)
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
    let result ← closeBridgeWithVerificationTyped goal goalType proof checkMVar "finsum_witness" #[
      do evalTactic (← `(tactic| intro h; exact h)),
      do evalTactic (← `(tactic| intro h; push_cast at h ⊢; linarith))
    ]
    match result with
    | .error .rejected => return .error <| .rejected checkerName (some enclosureRat)
    | .error failure => return .error (bridgeFailureToFinSum failure)
    | .ok event =>
      return .ok {
        path := .witnessRange
        isUpper := wGoal.isUpper
        termCount := if b < a then 0 else b + 1 - a
        precision := prec
        taylorDepth := 10
        enclosure := enclosureRat
        checker := checkerName
        verifier := verifierName
        verification := event.toUsage
      }

/-- Core implementation of `finsum_witness` for arbitrary Finsets (list path). -/
private def finSumWitnessListCore (wGoal : WitnessGoalList) (evalTermSyn hmemSyn : Syntax)
    (prec : Int) : TacticM (Except FinSumFailure FinSumOutcome) := do
  let goal ← getMainGoal
  let goalType ← goal.getType

  goal.withContext do
    let some target ← Auto.extractRatFromReal wGoal.targetExpr
      | return .error <| .unsupported
          s!"bound is not rational: {← ppExpr wGoal.targetExpr}"
    let targetExpr := toExpr target

    let precExpr := toExpr prec
    let depthExpr := toExpr (10 : Nat)
    let cfgExpr ← mkAppM ``DyadicConfig.mk #[precExpr, depthExpr]

    let evalTermTy ← mkArrow (Lean.mkConst ``Nat)
      (← mkArrow (Lean.mkConst ``DyadicConfig) (Lean.mkConst ``IntervalDyadic))
    let evalTermExpr ←
      try Tactic.elabTermEnsuringType evalTermSyn (some evalTermTy)
      catch e =>
        return .error <| .unsupported
          s!"malformed witness evaluator: {← e.toMessageData.toString}"

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

    let hmemExpr ←
      try Tactic.elabTermEnsuringType hmemSyn (some hmemTy)
      catch e =>
        return .error <| .unsupported
          s!"malformed witness proof: {← e.toMessageData.toString}"

    let indices ← unsafe evalExpr (List Nat)
      (mkApp (mkConst ``List [0]) (mkConst ``Nat)) wGoal.indicesExpr
    -- Build combined check (S = indices.toFinset ∧ Nodup ∧ bound)
    let checkerName := if wGoal.isUpper then
      ``checkWitnessSumUpperBoundListFull else ``checkWitnessSumLowerBoundListFull
    let verifierName := if wGoal.isUpper then
      ``verify_witness_sum_upper_list_full else ``verify_witness_sum_lower_list_full
    let enclosureExpr ← mkAppM ``witnessSumDyadicList
      #[evalTermExpr, wGoal.indicesExpr, cfgExpr]
    let enclosure ← unsafe evalExpr IntervalDyadic (mkConst ``IntervalDyadic) enclosureExpr
    let enclosureRat := enclosure.toIntervalRat
    unless (if wGoal.isUpper then enclosureRat.hi ≤ target else target ≤ enclosureRat.lo) do
      return .error <| .rejected checkerName (some enclosureRat)
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
    let result ← closeBridgeWithVerificationTyped goal goalType proof checkMVar "finsum_witness" #[
      do evalTactic (← `(tactic| intro h; exact h)),
      do evalTactic (← `(tactic| intro h; push_cast at h ⊢; linarith))
    ]
    match result with
    | .error .rejected => return .error <| .rejected checkerName (some enclosureRat)
    | .error failure => return .error (bridgeFailureToFinSum failure)
    | .ok event =>
      return .ok {
        path := .witnessExplicit
        isUpper := wGoal.isUpper
        termCount := indices.length
        precision := prec
        taylorDepth := 10
        enclosure := enclosureRat
        checker := checkerName
        verifier := verifierName
        verification := event.toUsage
      }

/-- Main dispatch: try Icc path first, then list path. -/
def finSumWitnessCoreTyped (evalTermSyn hmemSyn : Syntax) (prec : Int) :
    TacticM (Except FinSumFailure FinSumOutcome) := do
  let original ← saveState
  try
    let goal ← getMainGoal
    let goalType ← goal.getType

    if let some wGoal := parseWitnessGoal goalType then
      match ← finSumWitnessIccCore wGoal evalTermSyn hmemSyn prec with
      | .ok outcome => return .ok outcome
      | .error failure =>
          original.restore
          return .error failure

    if let some wGoalList := ← parseWitnessGoalList goalType then
      match ← finSumWitnessListCore wGoalList evalTermSyn hmemSyn prec with
      | .ok outcome => return .ok outcome
      | .error failure =>
          original.restore
          return .error failure

    original.restore
    return .error <| .unsupported "goal is not a recognized finite-sum bound"
  catch e =>
    original.restore
    return .error <| .internalFailure (← e.toMessageData.toString)

/-- Run one structural membership-synthesis strategy, then close every closed
decidable obligation through the typed verification boundary.

The caller selects a strategy that matches the already parsed range or explicit
Finset shape. Structural exceptions therefore remain unexpected and escape to
the outer transactional core as internal failures. Once certificate
obligations exist, rejection and verification failures are retained as typed
failures and never reinterpreted as unsupported syntax. -/
private def tryAutoHmemStrategy (hmemMVar : MVarId) (strategy : Syntax) :
    TacticM (Except FinSumFailure (Option VerificationUsage)) := do
  let strategyState ← saveState
  let surroundingGoals ← getGoals
  setGoals [hmemMVar]
  evalTactic strategy

  let cfg ← VerificationConfig.current
  let mut usage : VerificationUsage := {}
  while !(← getGoals).isEmpty do
    let certGoal ← getMainGoal
    let certType ← instantiateMVars (← certGoal.getType)
    -- A strategy that leaves the quantified index in its obligation has not
    -- reached a certificate boundary yet; allow the enumerating strategies
    -- below to try instead.
    if certType.hasFVar || certType.hasMVar then
      strategyState.restore
      return .ok none
    match ← closeCertificateGoalTyped cfg certGoal
        (tacticName := "finsum_bound auto membership") with
    | .accepted event =>
        usage := usage.combine event.toUsage
    | .rejected =>
        strategyState.restore
        return .error <| .rejected
          `LeanCert.Tactic.finsum_bound_auto_membership none
    | .failed failure =>
        strategyState.restore
        let detail := failure.message "finsum_bound auto membership"
        match failure with
        | .malformedCertificateGoal _ | .internalError _ =>
            return .error <| .internalFailure detail
        | .kernelFailure _ | .nativeFailure _ =>
            return .error <| .verificationFailure detail

  unless ← hmemMVar.isAssigned do
    strategyState.restore
    return .error <| .internalFailure
      "membership synthesis discharged its subgoals without assigning the membership proof"
  setGoals surroundingGoals
  return .ok (some usage)

/-- Parsed shape of an automatically synthesized membership theorem. -/
private inductive AutoHmemShape where
  | range
  | explicit

/-- Try to auto-prove an hmem metavar using shape-specific structural strategies.
Works best when the evaluator returns singletons or tight intervals whose
membership reduces to closed decidable comparisons. -/
private def tryAutoProveHmemTyped (shape : AutoHmemShape) (hmemMVar : MVarId) :
    TacticM (Except FinSumFailure VerificationUsage) := do
  let constantStrategy ← `(tactic|
      intros;
      simp only [IntervalDyadic.mem_def, IntervalDyadic.singleton];
      constructor <;> norm_cast)
  let rangeStrategy ← `(tactic|
      intro k hlo hhi;
      interval_cases k <;>
      simp only [IntervalDyadic.mem_def, IntervalDyadic.singleton] <;>
      constructor <;> norm_cast)
  let explicitStrategy ← `(tactic|
      intro k hk;
      fin_cases hk <;>
      simp only [IntervalDyadic.mem_def, IntervalDyadic.singleton] <;>
      constructor <;> norm_cast)
  let strategies : Array Syntax := match shape with
    | .range => #[constantStrategy, rangeStrategy]
    | .explicit => #[constantStrategy, explicitStrategy]
  for strategy in strategies do
    match ← tryAutoHmemStrategy hmemMVar strategy with
    | .ok (some usage) => return .ok usage
    | .ok none => pure ()
    | .error failure => return .error failure
  let hmemTy ← hmemMVar.getType
  return .error <| .unsupported
    s!"could not auto-prove membership.\nExpected type: {← ppExpr hmemTy}\n\
      Provide hmem explicitly: `finsum_bound using evalTerm hmemProof`"

/-- Core implementation of `finsum_bound auto` for Icc goals. -/
private def finSumWitnessAutoIccCore (wGoal : WitnessGoal) (evalTermSyn : Syntax)
    (prec : Int) : TacticM (Except FinSumFailure FinSumOutcome) := do
  let goal ← getMainGoal
  let goalType ← goal.getType

  goal.withContext do
    let some target ← Auto.extractRatFromReal wGoal.targetExpr
      | return .error <| .unsupported
          s!"bound is not rational: {← ppExpr wGoal.targetExpr}"
    let targetExpr := toExpr target

    let precExpr := toExpr prec
    let depthExpr := toExpr (10 : Nat)
    let cfgExpr ← mkAppM ``DyadicConfig.mk #[precExpr, depthExpr]

    let evalTermTy ← mkArrow (Lean.mkConst ``Nat)
      (← mkArrow (Lean.mkConst ``DyadicConfig) (Lean.mkConst ``IntervalDyadic))
    let evalTermExpr ←
      try Tactic.elabTermEnsuringType evalTermSyn (some evalTermTy)
      catch e =>
        return .error <| .unsupported
          s!"malformed witness evaluator: {← e.toMessageData.toString}"

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
    let membershipUsage ←
      match ← tryAutoProveHmemTyped .range hmemMVar.mvarId! with
      | .ok usage => pure usage
      | .error failure => return .error failure

    let hmemExpr := hmemMVar

    -- Rest is identical to finSumWitnessIccCore
    let checkerName := if wGoal.isUpper then
      ``checkWitnessSumUpperBound else ``checkWitnessSumLowerBound
    let verifierName := if wGoal.isUpper then
      ``verify_witness_sum_upper else ``verify_witness_sum_lower
    let enclosureExpr ← mkAppM ``witnessSumDyadic
      #[evalTermExpr, wGoal.aExpr, wGoal.bExpr, cfgExpr]
    let enclosure ← unsafe evalExpr IntervalDyadic (mkConst ``IntervalDyadic) enclosureExpr
    let enclosureRat := enclosure.toIntervalRat
    unless (if wGoal.isUpper then enclosureRat.hi ≤ target else target ≤ enclosureRat.lo) do
      return .error <| .rejected checkerName (some enclosureRat)

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
    let result ← closeBridgeWithVerificationTyped goal goalType proof checkMVar "finsum_bound auto" #[
      do evalTactic (← `(tactic| intro h; exact h)),
      do evalTactic (← `(tactic| intro h; push_cast at h ⊢; linarith))
    ]
    match result with
    | .error .rejected => return .error <| .rejected checkerName (some enclosureRat)
    | .error (.verificationFailure detail) =>
        return .error <| .verificationFailure detail
    | .error (.transportFailure detail) =>
        return .error <| .transportFailure detail
    | .ok event =>
      let some a ← extractNatLit wGoal.aExpr
        | return .error <| .unsupported "range lower endpoint is not a natural literal"
      let some b ← extractNatLit wGoal.bExpr
        | return .error <| .unsupported "range upper endpoint is not a natural literal"
      return .ok {
        path := .witnessRange
        isUpper := wGoal.isUpper
        termCount := if b < a then 0 else b + 1 - a
        precision := prec
        taylorDepth := 10
        enclosure := enclosureRat
        checker := checkerName
        verifier := verifierName
        verification := membershipUsage.combine event.toUsage
      }

/-- Core implementation of `finsum_bound auto` for arbitrary Finsets (list path). -/
private def finSumWitnessAutoListCore (wGoal : WitnessGoalList) (evalTermSyn : Syntax)
    (prec : Int) : TacticM (Except FinSumFailure FinSumOutcome) := do
  let goal ← getMainGoal
  let goalType ← goal.getType

  goal.withContext do
    let some target ← Auto.extractRatFromReal wGoal.targetExpr
      | return .error <| .unsupported
          s!"bound is not rational: {← ppExpr wGoal.targetExpr}"
    let targetExpr := toExpr target

    let precExpr := toExpr prec
    let depthExpr := toExpr (10 : Nat)
    let cfgExpr ← mkAppM ``DyadicConfig.mk #[precExpr, depthExpr]

    let evalTermTy ← mkArrow (Lean.mkConst ``Nat)
      (← mkArrow (Lean.mkConst ``DyadicConfig) (Lean.mkConst ``IntervalDyadic))
    let evalTermExpr ←
      try Tactic.elabTermEnsuringType evalTermSyn (some evalTermTy)
      catch e =>
        return .error <| .unsupported
          s!"malformed witness evaluator: {← e.toMessageData.toString}"

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
    let membershipUsage ←
      match ← tryAutoProveHmemTyped .explicit hmemMVar.mvarId! with
      | .ok usage => pure usage
      | .error failure => return .error failure

    let hmemExpr := hmemMVar

    -- Rest is identical to finSumWitnessListCore
    let checkerName := if wGoal.isUpper then
      ``checkWitnessSumUpperBoundListFull else ``checkWitnessSumLowerBoundListFull
    let verifierName := if wGoal.isUpper then
      ``verify_witness_sum_upper_list_full else ``verify_witness_sum_lower_list_full
    let enclosureExpr ← mkAppM ``witnessSumDyadicList
      #[evalTermExpr, wGoal.indicesExpr, cfgExpr]
    let enclosure ← unsafe evalExpr IntervalDyadic (mkConst ``IntervalDyadic) enclosureExpr
    let enclosureRat := enclosure.toIntervalRat
    unless (if wGoal.isUpper then enclosureRat.hi ≤ target else target ≤ enclosureRat.lo) do
      return .error <| .rejected checkerName (some enclosureRat)

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
    let result ← closeBridgeWithVerificationTyped goal goalType proof checkMVar "finsum_bound auto" #[
      do evalTactic (← `(tactic| intro h; exact h)),
      do evalTactic (← `(tactic| intro h; push_cast at h ⊢; linarith))
    ]
    match result with
    | .error .rejected => return .error <| .rejected checkerName (some enclosureRat)
    | .error (.verificationFailure detail) =>
        return .error <| .verificationFailure detail
    | .error (.transportFailure detail) =>
        return .error <| .transportFailure detail
    | .ok event =>
      let indices ← unsafe evalExpr (List Nat)
        (mkApp (mkConst ``List [0]) (mkConst ``Nat)) wGoal.indicesExpr
      return .ok {
        path := .witnessExplicit
        isUpper := wGoal.isUpper
        termCount := indices.length
        precision := prec
        taylorDepth := 10
        enclosure := enclosureRat
        checker := checkerName
        verifier := verifierName
        verification := membershipUsage.combine event.toUsage
      }

/-- Main dispatch for auto-hmem mode: try Icc path first, then list path. -/
def finSumWitnessAutoCoreTyped (evalTermSyn : Syntax) (prec : Int) :
    TacticM (Except FinSumFailure FinSumOutcome) := do
  let original ← saveState
  try
    let goal ← getMainGoal
    let goalType ← goal.getType
    let result ←
      if let some wGoal := parseWitnessGoal goalType then
        finSumWitnessAutoIccCore wGoal evalTermSyn prec
      else if let some wGoalList := ← parseWitnessGoalList goalType then
        finSumWitnessAutoListCore wGoalList evalTermSyn prec
      else
        pure <| .error <| .unsupported "goal is not a recognized finite-sum bound"
    match result with
    | .ok outcome => return .ok outcome
    | .error failure =>
        original.restore
        return .error failure
  catch e =>
    original.restore
    return .error <| .internalFailure (← e.toMessageData.toString)

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
  match ← finSumWitnessCoreTyped evalTerm hmem precision with
  | .ok _ => pure ()
  | .error failure => throwError "finsum_witness: {repr failure}"

end LeanCert.Tactic
