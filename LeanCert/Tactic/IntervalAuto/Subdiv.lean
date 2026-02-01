/-
Copyright (c) 2024 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Tactic.IntervalAuto.Basic
import LeanCert.Tactic.IntervalAuto.Bound
import LeanCert.Validity.Bounds
import LeanCert.Engine.Optimization.BoundVerify

/-!
# Subdivision-aware Bound Proving

The `interval_bound_subdiv` tactic uses interval subdivision when the direct approach fails.
-/

open Lean Meta Elab Tactic Term

namespace LeanCert.Tactic.Auto

open LeanCert.Meta
open LeanCert.Core
open LeanCert.Engine
open LeanCert.Validity

/-- Try to prove upper bound with subdivision. -/
private partial def proveUpperBoundWithSubdiv
    (ast supportProof loRatExpr hiRatExpr leProof boundRat cfgExpr : Lean.Expr)
    (taylorDepth maxSubdiv : Nat) : TacticM (Option Lean.Expr) := do
  let intervalRat ← mkAppM ``IntervalRat.mk #[loRatExpr, hiRatExpr, leProof]
  let checkExpr ← mkAppM ``LeanCert.Validity.checkUpperBound
    #[ast, intervalRat, boundRat, cfgExpr]

  if ← certCheckSucceeds checkExpr then
    trace[interval_decide] "Direct check succeeded"
    let certTy ← mkAppM ``Eq #[checkExpr, mkConst ``Bool.true]
    let certGoal ← mkFreshExprMVar certTy
    let certGoalId := certGoal.mvarId!
    setGoals [certGoalId]
    evalTactic (← `(tactic| native_decide))
    let certProof := certGoal
    let proof ← mkAppM ``Validity.verify_upper_bound_Icc_core
      #[ast, supportProof, loRatExpr, hiRatExpr, leProof, boundRat, cfgExpr, certProof]
    return some proof

  if maxSubdiv == 0 then
    trace[interval_decide] "Subdivision exhausted - giving up"
    return none

  trace[interval_decide] "Direct check failed, trying subdivision (depth {maxSubdiv})"

  let some lo ← getLiteral? loRatExpr
    | trace[interval_decide] "Could not extract lo literal"; return none
  let some hi ← getLiteral? hiRatExpr
    | trace[interval_decide] "Could not extract hi literal"; return none

  let mid : ℚ := (lo + hi) / 2
  let midExpr := toExpr mid
  let loLeMidExpr ← mkDecideProof (← mkAppM ``LE.le #[loRatExpr, midExpr])
  let midLeHiExpr ← mkDecideProof (← mkAppM ``LE.le #[midExpr, hiRatExpr])

  let leftProof ← proveUpperBoundWithSubdiv ast supportProof loRatExpr midExpr loLeMidExpr
    boundRat cfgExpr taylorDepth (maxSubdiv - 1)
  let some _ := leftProof
    | trace[interval_decide] "Left half failed"; return none

  let rightProof ← proveUpperBoundWithSubdiv ast supportProof midExpr hiRatExpr midLeHiExpr
    boundRat cfgExpr taylorDepth (maxSubdiv - 1)
  let some _ := rightProof
    | trace[interval_decide] "Right half failed"; return none

  let leftInterval ← mkAppM ``IntervalRat.mk #[loRatExpr, midExpr, loLeMidExpr]
  let rightInterval ← mkAppM ``IntervalRat.mk #[midExpr, hiRatExpr, midLeHiExpr]

  let leftCheckExpr ← mkAppM ``LeanCert.Validity.checkUpperBound
    #[ast, leftInterval, boundRat, cfgExpr]
  let rightCheckExpr ← mkAppM ``LeanCert.Validity.checkUpperBound
    #[ast, rightInterval, boundRat, cfgExpr]

  let leftCertTy ← mkAppM ``Eq #[leftCheckExpr, mkConst ``Bool.true]
  let leftCertGoal ← mkFreshExprMVar leftCertTy
  setGoals [leftCertGoal.mvarId!]
  evalTactic (← `(tactic| native_decide))
  let leftCertProof := leftCertGoal

  let rightCertTy ← mkAppM ``Eq #[rightCheckExpr, mkConst ``Bool.true]
  let rightCertGoal ← mkFreshExprMVar rightCertTy
  setGoals [rightCertGoal.mvarId!]
  evalTactic (← `(tactic| native_decide))
  let rightCertProof := rightCertGoal

  trace[interval_decide] "Subdivision succeeded on both halves - combining proofs"

  let proof ← mkAppM ``Validity.verify_upper_bound_general_split
    #[ast, supportProof, loRatExpr, midExpr, hiRatExpr,
      loLeMidExpr, midLeHiExpr, leProof, boundRat, cfgExpr,
      leftCertProof, rightCertProof]

  return some proof

/-- Try to prove lower bound with subdivision. -/
private partial def proveLowerBoundWithSubdiv
    (ast supportProof loRatExpr hiRatExpr leProof boundRat cfgExpr : Lean.Expr)
    (taylorDepth maxSubdiv : Nat) : TacticM (Option Lean.Expr) := do
  let intervalRat ← mkAppM ``IntervalRat.mk #[loRatExpr, hiRatExpr, leProof]
  let checkExpr ← mkAppM ``LeanCert.Validity.checkLowerBound
    #[ast, intervalRat, boundRat, cfgExpr]

  if ← certCheckSucceeds checkExpr then
    trace[interval_decide] "Direct lower bound check succeeded"
    let certTy ← mkAppM ``Eq #[checkExpr, mkConst ``Bool.true]
    let certGoal ← mkFreshExprMVar certTy
    let certGoalId := certGoal.mvarId!
    setGoals [certGoalId]
    evalTactic (← `(tactic| native_decide))
    let certProof := certGoal
    let proof ← mkAppM ``Validity.verify_lower_bound_Icc_core
      #[ast, supportProof, loRatExpr, hiRatExpr, leProof, boundRat, cfgExpr, certProof]
    return some proof

  if maxSubdiv == 0 then
    trace[interval_decide] "Subdivision exhausted - giving up"
    return none

  trace[interval_decide] "Direct lower bound check failed, trying subdivision (depth {maxSubdiv})"

  let some lo ← getLiteral? loRatExpr
    | trace[interval_decide] "Could not extract lo literal"; return none
  let some hi ← getLiteral? hiRatExpr
    | trace[interval_decide] "Could not extract hi literal"; return none

  let mid : ℚ := (lo + hi) / 2
  let midExpr := toExpr mid
  let loLeMidExpr ← mkDecideProof (← mkAppM ``LE.le #[loRatExpr, midExpr])
  let midLeHiExpr ← mkDecideProof (← mkAppM ``LE.le #[midExpr, hiRatExpr])

  let leftProof ← proveLowerBoundWithSubdiv ast supportProof loRatExpr midExpr loLeMidExpr
    boundRat cfgExpr taylorDepth (maxSubdiv - 1)
  let some _ := leftProof
    | trace[interval_decide] "Left half failed"; return none

  let rightProof ← proveLowerBoundWithSubdiv ast supportProof midExpr hiRatExpr midLeHiExpr
    boundRat cfgExpr taylorDepth (maxSubdiv - 1)
  let some _ := rightProof
    | trace[interval_decide] "Right half failed"; return none

  let leftInterval ← mkAppM ``IntervalRat.mk #[loRatExpr, midExpr, loLeMidExpr]
  let rightInterval ← mkAppM ``IntervalRat.mk #[midExpr, hiRatExpr, midLeHiExpr]

  let leftCheckExpr ← mkAppM ``LeanCert.Validity.checkLowerBound
    #[ast, leftInterval, boundRat, cfgExpr]
  let rightCheckExpr ← mkAppM ``LeanCert.Validity.checkLowerBound
    #[ast, rightInterval, boundRat, cfgExpr]

  let leftCertTy ← mkAppM ``Eq #[leftCheckExpr, mkConst ``Bool.true]
  let leftCertGoal ← mkFreshExprMVar leftCertTy
  setGoals [leftCertGoal.mvarId!]
  evalTactic (← `(tactic| native_decide))
  let leftCertProof := leftCertGoal

  let rightCertTy ← mkAppM ``Eq #[rightCheckExpr, mkConst ``Bool.true]
  let rightCertGoal ← mkFreshExprMVar rightCertTy
  setGoals [rightCertGoal.mvarId!]
  evalTactic (← `(tactic| native_decide))
  let rightCertProof := rightCertGoal

  trace[interval_decide] "Subdivision succeeded on both halves - combining lower bound proofs"

  let proof ← mkAppM ``Validity.verify_lower_bound_general_split
    #[ast, supportProof, loRatExpr, midExpr, hiRatExpr,
      loLeMidExpr, midLeHiExpr, leProof, boundRat, cfgExpr,
      leftCertProof, rightCertProof]

  return some proof

/-- Try to prove strict upper bound with subdivision. -/
private partial def proveStrictUpperBoundWithSubdiv
    (ast supportProof loRatExpr hiRatExpr leProof boundRat cfgExpr : Lean.Expr)
    (taylorDepth maxSubdiv : Nat) : TacticM (Option Lean.Expr) := do
  let intervalRat ← mkAppM ``IntervalRat.mk #[loRatExpr, hiRatExpr, leProof]
  let checkExpr ← mkAppM ``LeanCert.Validity.checkStrictUpperBound
    #[ast, intervalRat, boundRat, cfgExpr]

  if ← certCheckSucceeds checkExpr then
    trace[interval_decide] "Direct strict upper bound check succeeded"
    let certTy ← mkAppM ``Eq #[checkExpr, mkConst ``Bool.true]
    let certGoal ← mkFreshExprMVar certTy
    let certGoalId := certGoal.mvarId!
    setGoals [certGoalId]
    evalTactic (← `(tactic| native_decide))
    let certProof := certGoal
    let proof ← mkAppM ``Validity.verify_strict_upper_bound_Icc_core
      #[ast, supportProof, loRatExpr, hiRatExpr, leProof, boundRat, cfgExpr, certProof]
    return some proof

  if maxSubdiv == 0 then
    trace[interval_decide] "Subdivision exhausted - giving up"
    return none

  trace[interval_decide] "Direct strict upper bound check failed, trying subdivision (depth {maxSubdiv})"

  let some lo ← getLiteral? loRatExpr
    | trace[interval_decide] "Could not extract lo literal"; return none
  let some hi ← getLiteral? hiRatExpr
    | trace[interval_decide] "Could not extract hi literal"; return none

  let mid : ℚ := (lo + hi) / 2
  let midExpr := toExpr mid
  let loLeMidExpr ← mkDecideProof (← mkAppM ``LE.le #[loRatExpr, midExpr])
  let midLeHiExpr ← mkDecideProof (← mkAppM ``LE.le #[midExpr, hiRatExpr])

  let leftProof ← proveStrictUpperBoundWithSubdiv ast supportProof loRatExpr midExpr loLeMidExpr
    boundRat cfgExpr taylorDepth (maxSubdiv - 1)
  let some _ := leftProof
    | trace[interval_decide] "Left half failed"; return none

  let rightProof ← proveStrictUpperBoundWithSubdiv ast supportProof midExpr hiRatExpr midLeHiExpr
    boundRat cfgExpr taylorDepth (maxSubdiv - 1)
  let some _ := rightProof
    | trace[interval_decide] "Right half failed"; return none

  let leftInterval ← mkAppM ``IntervalRat.mk #[loRatExpr, midExpr, loLeMidExpr]
  let rightInterval ← mkAppM ``IntervalRat.mk #[midExpr, hiRatExpr, midLeHiExpr]

  let leftCheckExpr ← mkAppM ``LeanCert.Validity.checkStrictUpperBound
    #[ast, leftInterval, boundRat, cfgExpr]
  let rightCheckExpr ← mkAppM ``LeanCert.Validity.checkStrictUpperBound
    #[ast, rightInterval, boundRat, cfgExpr]

  let leftCertTy ← mkAppM ``Eq #[leftCheckExpr, mkConst ``Bool.true]
  let leftCertGoal ← mkFreshExprMVar leftCertTy
  setGoals [leftCertGoal.mvarId!]
  evalTactic (← `(tactic| native_decide))
  let leftCertProof := leftCertGoal

  let rightCertTy ← mkAppM ``Eq #[rightCheckExpr, mkConst ``Bool.true]
  let rightCertGoal ← mkFreshExprMVar rightCertTy
  setGoals [rightCertGoal.mvarId!]
  evalTactic (← `(tactic| native_decide))
  let rightCertProof := rightCertGoal

  trace[interval_decide] "Subdivision succeeded on both halves - combining strict upper bound proofs"

  let proof ← mkAppM ``Validity.verify_strict_upper_bound_general_split
    #[ast, supportProof, loRatExpr, midExpr, hiRatExpr,
      loLeMidExpr, midLeHiExpr, leProof, boundRat, cfgExpr,
      leftCertProof, rightCertProof]

  return some proof

/-- Try to prove strict lower bound with subdivision. -/
private partial def proveStrictLowerBoundWithSubdiv
    (ast supportProof loRatExpr hiRatExpr leProof boundRat cfgExpr : Lean.Expr)
    (taylorDepth maxSubdiv : Nat) : TacticM (Option Lean.Expr) := do
  let intervalRat ← mkAppM ``IntervalRat.mk #[loRatExpr, hiRatExpr, leProof]
  let checkExpr ← mkAppM ``LeanCert.Validity.checkStrictLowerBound
    #[ast, intervalRat, boundRat, cfgExpr]

  if ← certCheckSucceeds checkExpr then
    trace[interval_decide] "Direct strict lower bound check succeeded"
    let certTy ← mkAppM ``Eq #[checkExpr, mkConst ``Bool.true]
    let certGoal ← mkFreshExprMVar certTy
    let certGoalId := certGoal.mvarId!
    setGoals [certGoalId]
    evalTactic (← `(tactic| native_decide))
    let certProof := certGoal
    let proof ← mkAppM ``Validity.verify_strict_lower_bound_Icc_core
      #[ast, supportProof, loRatExpr, hiRatExpr, leProof, boundRat, cfgExpr, certProof]
    return some proof

  if maxSubdiv == 0 then
    trace[interval_decide] "Subdivision exhausted - giving up"
    return none

  trace[interval_decide] "Direct strict lower bound check failed, trying subdivision (depth {maxSubdiv})"

  let some lo ← getLiteral? loRatExpr
    | trace[interval_decide] "Could not extract lo literal"; return none
  let some hi ← getLiteral? hiRatExpr
    | trace[interval_decide] "Could not extract hi literal"; return none

  let mid : ℚ := (lo + hi) / 2
  let midExpr := toExpr mid
  let loLeMidExpr ← mkDecideProof (← mkAppM ``LE.le #[loRatExpr, midExpr])
  let midLeHiExpr ← mkDecideProof (← mkAppM ``LE.le #[midExpr, hiRatExpr])

  let leftProof ← proveStrictLowerBoundWithSubdiv ast supportProof loRatExpr midExpr loLeMidExpr
    boundRat cfgExpr taylorDepth (maxSubdiv - 1)
  let some _ := leftProof
    | trace[interval_decide] "Left half failed"; return none

  let rightProof ← proveStrictLowerBoundWithSubdiv ast supportProof midExpr hiRatExpr midLeHiExpr
    boundRat cfgExpr taylorDepth (maxSubdiv - 1)
  let some _ := rightProof
    | trace[interval_decide] "Right half failed"; return none

  let leftInterval ← mkAppM ``IntervalRat.mk #[loRatExpr, midExpr, loLeMidExpr]
  let rightInterval ← mkAppM ``IntervalRat.mk #[midExpr, hiRatExpr, midLeHiExpr]

  let leftCheckExpr ← mkAppM ``LeanCert.Validity.checkStrictLowerBound
    #[ast, leftInterval, boundRat, cfgExpr]
  let rightCheckExpr ← mkAppM ``LeanCert.Validity.checkStrictLowerBound
    #[ast, rightInterval, boundRat, cfgExpr]

  let leftCertTy ← mkAppM ``Eq #[leftCheckExpr, mkConst ``Bool.true]
  let leftCertGoal ← mkFreshExprMVar leftCertTy
  setGoals [leftCertGoal.mvarId!]
  evalTactic (← `(tactic| native_decide))
  let leftCertProof := leftCertGoal

  let rightCertTy ← mkAppM ``Eq #[rightCheckExpr, mkConst ``Bool.true]
  let rightCertGoal ← mkFreshExprMVar rightCertTy
  setGoals [rightCertGoal.mvarId!]
  evalTactic (← `(tactic| native_decide))
  let rightCertProof := rightCertGoal

  trace[interval_decide] "Subdivision succeeded on both halves - combining strict lower bound proofs"

  let proof ← mkAppM ``Validity.verify_strict_lower_bound_general_split
    #[ast, supportProof, loRatExpr, midExpr, hiRatExpr,
      loLeMidExpr, midLeHiExpr, leProof, boundRat, cfgExpr,
      leftCertProof, rightCertProof]

  return some proof

/-- Prove ∀ x ∈ I, f x ≤ c using subdivision as fallback -/
private def proveForallLeSubdiv (goal : MVarId) (intervalInfo : IntervalInfo)
    (func bound : Lean.Expr) (taylorDepth maxSubdiv : Nat) : TacticM Unit := do
  goal.withContext do
    let ast ← getAst func
    let boundRat ← extractRatBound bound
    let (supportProof, _useWithInv) ← getSupportProof ast
    let cfgExpr ← mkAppM ``EvalConfig.mk #[toExpr taylorDepth]

    let some bounds ← getSubdivBounds intervalInfo
      | throwError "interval_bound_subdiv: Only literal Set.Icc or IntervalRat intervals supported for subdivision"
    let (_lo, _hi, loRatExpr, hiRatExpr, leProof, fromSetIcc) := bounds

    let savedGoals ← getGoals

    let some proof ← proveUpperBoundWithSubdiv ast supportProof loRatExpr hiRatExpr
        leProof boundRat cfgExpr taylorDepth maxSubdiv
      | throwError "interval_bound_subdiv: Failed even with subdivision"

    setGoals savedGoals
    let conclusionTerm ← Lean.Elab.Term.exprToSyntax proof
    if fromSetIcc then
      evalTactic (← `(tactic| convert ($conclusionTerm) using 3))
    else
      evalTactic (← `(tactic| simpa [IntervalRat.mem_iff_mem_Icc] using $conclusionTerm))

    let goals ← getGoals
    for g in goals do
      setGoals [g]
      let tryClose (tac : TacticM Unit) : TacticM Bool := do
        try
          tac
          let goalsEmpty := (← getGoals).isEmpty
          return goalsEmpty
        catch _ => return false
      if ← tryClose (evalTactic (← `(tactic| rfl))) then continue
      if ← tryClose (evalTactic (← `(tactic| norm_num))) then continue
      if ← tryClose (evalTactic (← `(tactic| norm_cast))) then continue
      if ← tryClose (evalTactic (← `(tactic| norm_num; simp only [Rat.divInt_eq_div]; push_cast; rfl))) then continue
      if ← tryClose (evalTactic (← `(tactic| simp only [Rat.divInt_eq_div]; push_cast; rfl))) then continue
      if ← tryClose (evalTactic (← `(tactic| congr 1 <;> norm_num))) then continue
      if ← tryClose (evalTactic (← `(tactic| simp only [sq, pow_two, pow_succ, pow_zero, pow_one, one_mul, mul_one]))) then continue
      logWarning m!"interval_bound_subdiv: Could not close side goal: {← g.getType}"

/-- Prove ∀ x ∈ I, c ≤ f x using subdivision as fallback -/
private def proveForallGeSubdiv (goal : MVarId) (intervalInfo : IntervalInfo)
    (func bound : Lean.Expr) (taylorDepth maxSubdiv : Nat) : TacticM Unit := do
  goal.withContext do
    let ast ← getAst func
    let boundRat ← extractRatBound bound
    let (supportProof, _useWithInv) ← getSupportProof ast
    let cfgExpr ← mkAppM ``EvalConfig.mk #[toExpr taylorDepth]

    let some bounds ← getSubdivBounds intervalInfo
      | throwError "interval_bound_subdiv: Only literal Set.Icc or IntervalRat intervals supported for subdivision"
    let (_lo, _hi, loRatExpr, hiRatExpr, leProof, fromSetIcc) := bounds

    let savedGoals ← getGoals

    let some proof ← proveLowerBoundWithSubdiv ast supportProof loRatExpr hiRatExpr
        leProof boundRat cfgExpr taylorDepth maxSubdiv
      | throwError "interval_bound_subdiv: Failed even with subdivision (lower bound)"

    setGoals savedGoals
    let conclusionTerm ← Lean.Elab.Term.exprToSyntax proof
    if fromSetIcc then
      evalTactic (← `(tactic| convert ($conclusionTerm) using 3))
    else
      evalTactic (← `(tactic| simpa [IntervalRat.mem_iff_mem_Icc] using $conclusionTerm))

    let goals ← getGoals
    for g in goals do
      setGoals [g]
      let tryClose (tac : TacticM Unit) : TacticM Bool := do
        try
          tac
          let goalsEmpty := (← getGoals).isEmpty
          return goalsEmpty
        catch _ => return false
      if ← tryClose (evalTactic (← `(tactic| rfl))) then continue
      if ← tryClose (evalTactic (← `(tactic| norm_num))) then continue
      if ← tryClose (evalTactic (← `(tactic| norm_cast))) then continue
      if ← tryClose (evalTactic (← `(tactic| norm_num; simp only [Rat.divInt_eq_div]; push_cast; rfl))) then continue
      if ← tryClose (evalTactic (← `(tactic| simp only [Rat.divInt_eq_div]; push_cast; rfl))) then continue
      if ← tryClose (evalTactic (← `(tactic| congr 1 <;> norm_num))) then continue
      if ← tryClose (evalTactic (← `(tactic| simp only [sq, pow_two, pow_succ, pow_zero, pow_one, one_mul, mul_one]))) then continue
      logWarning m!"interval_bound_subdiv: Could not close side goal: {← g.getType}"

/-- Prove ∀ x ∈ I, f x < c using subdivision as fallback -/
private def proveForallLtSubdiv (goal : MVarId) (intervalInfo : IntervalInfo)
    (func bound : Lean.Expr) (taylorDepth maxSubdiv : Nat) : TacticM Unit := do
  goal.withContext do
    let ast ← getAst func
    let boundRat ← extractRatBound bound
    let (supportProof, _useWithInv) ← getSupportProof ast
    let cfgExpr ← mkAppM ``EvalConfig.mk #[toExpr taylorDepth]

    let some bounds ← getSubdivBounds intervalInfo
      | throwError "interval_bound_subdiv: Only literal Set.Icc or IntervalRat intervals supported for subdivision"
    let (_lo, _hi, loRatExpr, hiRatExpr, leProof, fromSetIcc) := bounds

    let savedGoals ← getGoals

    let some proof ← proveStrictUpperBoundWithSubdiv ast supportProof loRatExpr hiRatExpr
        leProof boundRat cfgExpr taylorDepth maxSubdiv
      | throwError "interval_bound_subdiv: Failed even with subdivision (strict upper bound)"

    setGoals savedGoals
    let conclusionTerm ← Lean.Elab.Term.exprToSyntax proof
    if fromSetIcc then
      evalTactic (← `(tactic| convert ($conclusionTerm) using 3))
    else
      evalTactic (← `(tactic| simpa [IntervalRat.mem_iff_mem_Icc] using $conclusionTerm))

    let goals ← getGoals
    for g in goals do
      setGoals [g]
      let tryClose (tac : TacticM Unit) : TacticM Bool := do
        try
          tac
          let goalsEmpty := (← getGoals).isEmpty
          return goalsEmpty
        catch _ => return false
      if ← tryClose (evalTactic (← `(tactic| rfl))) then continue
      if ← tryClose (evalTactic (← `(tactic| norm_num))) then continue
      if ← tryClose (evalTactic (← `(tactic| norm_cast))) then continue
      if ← tryClose (evalTactic (← `(tactic| norm_num; simp only [Rat.divInt_eq_div]; push_cast; rfl))) then continue
      if ← tryClose (evalTactic (← `(tactic| simp only [Rat.divInt_eq_div]; push_cast; rfl))) then continue
      if ← tryClose (evalTactic (← `(tactic| simp only [Rat.divInt_eq_div]; push_cast; ring))) then continue
      if ← tryClose (evalTactic (← `(tactic| congr 1 <;> norm_num))) then continue
      if ← tryClose (evalTactic (← `(tactic| simp only [sq, pow_two, pow_succ, pow_zero, pow_one, one_mul, mul_one]))) then continue
      if ← tryClose (evalTactic (← `(tactic| field_simp; ring))) then continue
      logWarning m!"interval_bound_subdiv: Could not close side goal: {← g.getType}"

/-- Prove ∀ x ∈ I, c < f x using subdivision as fallback -/
private def proveForallGtSubdiv (goal : MVarId) (intervalInfo : IntervalInfo)
    (func bound : Lean.Expr) (taylorDepth maxSubdiv : Nat) : TacticM Unit := do
  goal.withContext do
    let ast ← getAst func
    let boundRat ← extractRatBound bound
    let (supportProof, _useWithInv) ← getSupportProof ast
    let cfgExpr ← mkAppM ``EvalConfig.mk #[toExpr taylorDepth]

    let some bounds ← getSubdivBounds intervalInfo
      | throwError "interval_bound_subdiv: Only literal Set.Icc or IntervalRat intervals supported for subdivision"
    let (_lo, _hi, loRatExpr, hiRatExpr, leProof, fromSetIcc) := bounds

    let savedGoals ← getGoals

    let some proof ← proveStrictLowerBoundWithSubdiv ast supportProof loRatExpr hiRatExpr
        leProof boundRat cfgExpr taylorDepth maxSubdiv
      | throwError "interval_bound_subdiv: Failed even with subdivision (strict lower bound)"

    setGoals savedGoals
    let conclusionTerm ← Lean.Elab.Term.exprToSyntax proof
    if fromSetIcc then
      evalTactic (← `(tactic| convert ($conclusionTerm) using 3))
    else
      evalTactic (← `(tactic| simpa [IntervalRat.mem_iff_mem_Icc] using $conclusionTerm))

    let goals ← getGoals
    for g in goals do
      setGoals [g]
      let tryClose (tac : TacticM Unit) : TacticM Bool := do
        try
          tac
          let goalsEmpty := (← getGoals).isEmpty
          return goalsEmpty
        catch _ => return false
      if ← tryClose (evalTactic (← `(tactic| rfl))) then continue
      if ← tryClose (evalTactic (← `(tactic| norm_num))) then continue
      if ← tryClose (evalTactic (← `(tactic| norm_cast))) then continue
      if ← tryClose (evalTactic (← `(tactic| norm_num; simp only [Rat.divInt_eq_div]; push_cast; rfl))) then continue
      if ← tryClose (evalTactic (← `(tactic| simp only [Rat.divInt_eq_div]; push_cast; rfl))) then continue
      if ← tryClose (evalTactic (← `(tactic| congr 1 <;> norm_num))) then continue
      if ← tryClose (evalTactic (← `(tactic| simp only [sq, pow_two, pow_succ, pow_zero, pow_one, one_mul, mul_one]))) then continue
      logWarning m!"interval_bound_subdiv: Could not close side goal: {← g.getType}"

/-- The interval_bound_subdiv tactic. -/
elab "interval_bound_subdiv" depth:(num)? subdivDepth:(num)? : tactic => do
  intervalNormCore
  let maxSubdiv := match subdivDepth with
    | some n => n.getNat
    | none => 3
  let depths : List Nat := match depth with
    | some n => [n.getNat]
    | none => [10, 15, 20, 25]

  try
    evalTactic (← `(tactic| intro _x _hx; simp only [ge_iff_le, gt_iff_lt]; revert _x _hx))
  catch _ =>
    try evalTactic (← `(tactic| simp only [ge_iff_le, gt_iff_lt]))
    catch _ => pure ()

  try
    evalTactic (← `(tactic| simp only [sq, pow_two, pow_succ, pow_zero, pow_one, one_mul, mul_one] at *))
  catch _ => pure ()

  let savedState ← saveState
  let mut lastErr : Option MessageData := none
  for taylorDepth in depths do
    restoreState savedState
    let goal ← getMainGoal
    let goalType ← goal.getType
    let some boundGoal ← parseBoundGoal goalType
      | throwError "interval_bound_subdiv: Could not parse goal"
    try
      match boundGoal with
      | .forallLe _name interval func bound =>
        proveForallLeSubdiv goal interval func bound taylorDepth maxSubdiv
      | .forallGe _name interval func bound =>
        proveForallGeSubdiv goal interval func bound taylorDepth maxSubdiv
      | .forallLt _name interval func bound =>
        proveForallLtSubdiv goal interval func bound taylorDepth maxSubdiv
      | .forallGt _name interval func bound =>
        proveForallGtSubdiv goal interval func bound taylorDepth maxSubdiv
      return
    catch e =>
      lastErr := some e.toMessageData
  throwError m!"interval_bound_subdiv: All precision levels failed\n{lastErr.getD ""}"

end LeanCert.Tactic.Auto
