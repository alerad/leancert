/-
Copyright (c) 2024 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Tactic.IntervalAuto.Basic
import LeanCert.Tactic.Verification
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

/-- Runtime facts retained by one successful subdivision proof tree. -/
structure SubdivisionExecution where
  verification : LeanCert.Tactic.VerificationUsage := {}
  deepestDepthUsed : Nat := 0
  leafChecks : Nat := 0
  deriving Inhabited

/-- A proof together with the execution facts that produced it. -/
structure SubdivisionProof where
  proof : Lean.Expr
  execution : SubdivisionExecution

/-- Reported result of the public subdivision strategy. The numerical backend
is Rational for every leaf checker in this module. -/
structure SubdivisionOutcome where
  taylorDepth : Nat
  maxDepth : Nat
  execution : SubdivisionExecution
  checker : Name
  verifier : Name

private def SubdivisionExecution.combine
    (left right : SubdivisionExecution) : SubdivisionExecution := {
  verification := left.verification.combine right.verification
  deepestDepthUsed := max left.deepestDepthUsed right.deepestDepthUsed
  leafChecks := left.leafChecks + right.leafChecks
}

/-- Try to prove upper bound with subdivision. -/
private partial def proveUpperBoundWithSubdiv
    (ast supportProof loRatExpr hiRatExpr leProof boundRat cfgExpr : Lean.Expr)
    (taylorDepth maxSubdiv depthUsed : Nat) : TacticM (Option SubdivisionProof) := do
  let intervalRat ← mkAppM ``IntervalRat.mk #[loRatExpr, hiRatExpr, leProof]
  let checkExpr ← mkAppM ``LeanCert.Validity.checkUpperBound
    #[ast, intervalRat, boundRat, cfgExpr]

  if ← certCheckSucceeds checkExpr then
    trace[interval_decide] "Direct check succeeded"
    let certTy ← mkAppM ``Eq #[checkExpr, mkConst ``Bool.true]
    let certGoal ← mkFreshExprMVar certTy
    let certGoalId := certGoal.mvarId!
    setGoals [certGoalId]
    let event ← LeanCert.Tactic.closeCertificateGoalReported
      (← LeanCert.Tactic.VerificationConfig.current) (← getMainGoal)
      (tacticName := "interval_bound_subdiv")
    let certProof := certGoal
    let proof ← mkAppM ``Validity.verify_upper_bound_Icc_core
      #[ast, supportProof, loRatExpr, hiRatExpr, leProof, boundRat, cfgExpr, certProof]
    return some {
      proof
      execution := {
        verification := event.toUsage
        deepestDepthUsed := depthUsed
        leafChecks := 1
      }
    }

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
    boundRat cfgExpr taylorDepth (maxSubdiv - 1) (depthUsed + 1)
  let some leftProof := leftProof
    | trace[interval_decide] "Left half failed"; return none

  let rightProof ← proveUpperBoundWithSubdiv ast supportProof midExpr hiRatExpr midLeHiExpr
    boundRat cfgExpr taylorDepth (maxSubdiv - 1) (depthUsed + 1)
  let some rightProof := rightProof
    | trace[interval_decide] "Right half failed"; return none

  trace[interval_decide] "Subdivision succeeded on both halves - combining proofs"

  let proof ← mkAppM ``Validity.combine_upper_bound_general_split
    #[ast, loRatExpr, midExpr, hiRatExpr, boundRat,
      loLeMidExpr, midLeHiExpr, leftProof.proof, rightProof.proof]

  return some {
    proof
    execution := leftProof.execution.combine rightProof.execution
  }

/-- Try to prove lower bound with subdivision. -/
private partial def proveLowerBoundWithSubdiv
    (ast supportProof loRatExpr hiRatExpr leProof boundRat cfgExpr : Lean.Expr)
    (taylorDepth maxSubdiv depthUsed : Nat) : TacticM (Option SubdivisionProof) := do
  let intervalRat ← mkAppM ``IntervalRat.mk #[loRatExpr, hiRatExpr, leProof]
  let checkExpr ← mkAppM ``LeanCert.Validity.checkLowerBound
    #[ast, intervalRat, boundRat, cfgExpr]

  if ← certCheckSucceeds checkExpr then
    trace[interval_decide] "Direct lower bound check succeeded"
    let certTy ← mkAppM ``Eq #[checkExpr, mkConst ``Bool.true]
    let certGoal ← mkFreshExprMVar certTy
    let certGoalId := certGoal.mvarId!
    setGoals [certGoalId]
    let event ← LeanCert.Tactic.closeCertificateGoalReported
      (← LeanCert.Tactic.VerificationConfig.current) (← getMainGoal)
      (tacticName := "interval_bound_subdiv")
    let certProof := certGoal
    let proof ← mkAppM ``Validity.verify_lower_bound_Icc_core
      #[ast, supportProof, loRatExpr, hiRatExpr, leProof, boundRat, cfgExpr, certProof]
    return some {
      proof
      execution := {
        verification := event.toUsage
        deepestDepthUsed := depthUsed
        leafChecks := 1
      }
    }

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
    boundRat cfgExpr taylorDepth (maxSubdiv - 1) (depthUsed + 1)
  let some leftProof := leftProof
    | trace[interval_decide] "Left half failed"; return none

  let rightProof ← proveLowerBoundWithSubdiv ast supportProof midExpr hiRatExpr midLeHiExpr
    boundRat cfgExpr taylorDepth (maxSubdiv - 1) (depthUsed + 1)
  let some rightProof := rightProof
    | trace[interval_decide] "Right half failed"; return none

  trace[interval_decide] "Subdivision succeeded on both halves - combining lower bound proofs"

  let proof ← mkAppM ``Validity.combine_lower_bound_general_split
    #[ast, loRatExpr, midExpr, hiRatExpr, boundRat,
      loLeMidExpr, midLeHiExpr, leftProof.proof, rightProof.proof]

  return some {
    proof
    execution := leftProof.execution.combine rightProof.execution
  }

/-- Try to prove strict upper bound with subdivision. -/
private partial def proveStrictUpperBoundWithSubdiv
    (ast supportProof loRatExpr hiRatExpr leProof boundRat cfgExpr : Lean.Expr)
    (taylorDepth maxSubdiv depthUsed : Nat) : TacticM (Option SubdivisionProof) := do
  let intervalRat ← mkAppM ``IntervalRat.mk #[loRatExpr, hiRatExpr, leProof]
  let checkExpr ← mkAppM ``LeanCert.Validity.checkStrictUpperBound
    #[ast, intervalRat, boundRat, cfgExpr]

  if ← certCheckSucceeds checkExpr then
    trace[interval_decide] "Direct strict upper bound check succeeded"
    let certTy ← mkAppM ``Eq #[checkExpr, mkConst ``Bool.true]
    let certGoal ← mkFreshExprMVar certTy
    let certGoalId := certGoal.mvarId!
    setGoals [certGoalId]
    let event ← LeanCert.Tactic.closeCertificateGoalReported
      (← LeanCert.Tactic.VerificationConfig.current) (← getMainGoal)
      (tacticName := "interval_bound_subdiv")
    let certProof := certGoal
    let proof ← mkAppM ``Validity.verify_strict_upper_bound_Icc_core
      #[ast, supportProof, loRatExpr, hiRatExpr, leProof, boundRat, cfgExpr, certProof]
    return some {
      proof
      execution := {
        verification := event.toUsage
        deepestDepthUsed := depthUsed
        leafChecks := 1
      }
    }

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
    boundRat cfgExpr taylorDepth (maxSubdiv - 1) (depthUsed + 1)
  let some leftProof := leftProof
    | trace[interval_decide] "Left half failed"; return none

  let rightProof ← proveStrictUpperBoundWithSubdiv ast supportProof midExpr hiRatExpr midLeHiExpr
    boundRat cfgExpr taylorDepth (maxSubdiv - 1) (depthUsed + 1)
  let some rightProof := rightProof
    | trace[interval_decide] "Right half failed"; return none

  trace[interval_decide] "Subdivision succeeded on both halves - combining strict upper bound proofs"

  let proof ← mkAppM ``Validity.combine_strict_upper_bound_general_split
    #[ast, loRatExpr, midExpr, hiRatExpr, boundRat,
      loLeMidExpr, midLeHiExpr, leftProof.proof, rightProof.proof]

  return some {
    proof
    execution := leftProof.execution.combine rightProof.execution
  }

/-- Try to prove strict lower bound with subdivision. -/
private partial def proveStrictLowerBoundWithSubdiv
    (ast supportProof loRatExpr hiRatExpr leProof boundRat cfgExpr : Lean.Expr)
    (taylorDepth maxSubdiv depthUsed : Nat) : TacticM (Option SubdivisionProof) := do
  let intervalRat ← mkAppM ``IntervalRat.mk #[loRatExpr, hiRatExpr, leProof]
  let checkExpr ← mkAppM ``LeanCert.Validity.checkStrictLowerBound
    #[ast, intervalRat, boundRat, cfgExpr]

  if ← certCheckSucceeds checkExpr then
    trace[interval_decide] "Direct strict lower bound check succeeded"
    let certTy ← mkAppM ``Eq #[checkExpr, mkConst ``Bool.true]
    let certGoal ← mkFreshExprMVar certTy
    let certGoalId := certGoal.mvarId!
    setGoals [certGoalId]
    let event ← LeanCert.Tactic.closeCertificateGoalReported
      (← LeanCert.Tactic.VerificationConfig.current) (← getMainGoal)
      (tacticName := "interval_bound_subdiv")
    let certProof := certGoal
    let proof ← mkAppM ``Validity.verify_strict_lower_bound_Icc_core
      #[ast, supportProof, loRatExpr, hiRatExpr, leProof, boundRat, cfgExpr, certProof]
    return some {
      proof
      execution := {
        verification := event.toUsage
        deepestDepthUsed := depthUsed
        leafChecks := 1
      }
    }

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
    boundRat cfgExpr taylorDepth (maxSubdiv - 1) (depthUsed + 1)
  let some leftProof := leftProof
    | trace[interval_decide] "Left half failed"; return none

  let rightProof ← proveStrictLowerBoundWithSubdiv ast supportProof midExpr hiRatExpr midLeHiExpr
    boundRat cfgExpr taylorDepth (maxSubdiv - 1) (depthUsed + 1)
  let some rightProof := rightProof
    | trace[interval_decide] "Right half failed"; return none

  trace[interval_decide] "Subdivision succeeded on both halves - combining strict lower bound proofs"

  let proof ← mkAppM ``Validity.combine_strict_lower_bound_general_split
    #[ast, loRatExpr, midExpr, hiRatExpr, boundRat,
      loLeMidExpr, midLeHiExpr, leftProof.proof, rightProof.proof]

  return some {
    proof
    execution := leftProof.execution.combine rightProof.execution
  }

/-- Prove ∀ x ∈ I, f x ≤ c using subdivision as fallback -/
private def proveForallLeSubdivReported (goal : MVarId) (intervalInfo : IntervalInfo)
    (func bound : Lean.Expr) (taylorDepth maxSubdiv : Nat) :
    TacticM SubdivisionExecution := do
  goal.withContext do
    let ast := (← getAstWithReport func).expr
    let boundRat ← extractRatBound bound
    let (supportProof, _useChecked) ← getSupportProof ast
    let cfgExpr ← mkAppM ``EvalConfig.mk #[toExpr taylorDepth]

    let some bounds ← getSubdivBounds intervalInfo
      | throwError "interval_bound_subdiv: Only literal Set.Icc or IntervalRat intervals supported for subdivision"
    let (_lo, _hi, loRatExpr, hiRatExpr, leProof, fromSetIcc) := bounds

    let savedGoals ← getGoals

    let some proof ← proveUpperBoundWithSubdiv ast supportProof loRatExpr hiRatExpr
        leProof boundRat cfgExpr taylorDepth maxSubdiv 0
      | throwError "interval_bound_subdiv: Failed even with subdivision"

    setGoals savedGoals
    let conclusionTerm ← Lean.Elab.Term.exprToSyntax proof.proof
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
    return proof.execution

/-- Prove ∀ x ∈ I, c ≤ f x using subdivision as fallback -/
private def proveForallGeSubdivReported (goal : MVarId) (intervalInfo : IntervalInfo)
    (func bound : Lean.Expr) (taylorDepth maxSubdiv : Nat) :
    TacticM SubdivisionExecution := do
  goal.withContext do
    let ast := (← getAstWithReport func).expr
    let boundRat ← extractRatBound bound
    let (supportProof, _useChecked) ← getSupportProof ast
    let cfgExpr ← mkAppM ``EvalConfig.mk #[toExpr taylorDepth]

    let some bounds ← getSubdivBounds intervalInfo
      | throwError "interval_bound_subdiv: Only literal Set.Icc or IntervalRat intervals supported for subdivision"
    let (_lo, _hi, loRatExpr, hiRatExpr, leProof, fromSetIcc) := bounds

    let savedGoals ← getGoals

    let some proof ← proveLowerBoundWithSubdiv ast supportProof loRatExpr hiRatExpr
        leProof boundRat cfgExpr taylorDepth maxSubdiv 0
      | throwError "interval_bound_subdiv: Failed even with subdivision (lower bound)"

    setGoals savedGoals
    let conclusionTerm ← Lean.Elab.Term.exprToSyntax proof.proof
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
    return proof.execution

/-- Prove ∀ x ∈ I, f x < c using subdivision as fallback -/
private def proveForallLtSubdivReported (goal : MVarId) (intervalInfo : IntervalInfo)
    (func bound : Lean.Expr) (taylorDepth maxSubdiv : Nat) :
    TacticM SubdivisionExecution := do
  goal.withContext do
    let ast := (← getAstWithReport func).expr
    let boundRat ← extractRatBound bound
    let (supportProof, _useChecked) ← getSupportProof ast
    let cfgExpr ← mkAppM ``EvalConfig.mk #[toExpr taylorDepth]

    let some bounds ← getSubdivBounds intervalInfo
      | throwError "interval_bound_subdiv: Only literal Set.Icc or IntervalRat intervals supported for subdivision"
    let (_lo, _hi, loRatExpr, hiRatExpr, leProof, fromSetIcc) := bounds

    let savedGoals ← getGoals

    let some proof ← proveStrictUpperBoundWithSubdiv ast supportProof loRatExpr hiRatExpr
        leProof boundRat cfgExpr taylorDepth maxSubdiv 0
      | throwError "interval_bound_subdiv: Failed even with subdivision (strict upper bound)"

    setGoals savedGoals
    let conclusionTerm ← Lean.Elab.Term.exprToSyntax proof.proof
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
    return proof.execution

/-- Prove ∀ x ∈ I, c < f x using subdivision as fallback -/
private def proveForallGtSubdivReported (goal : MVarId) (intervalInfo : IntervalInfo)
    (func bound : Lean.Expr) (taylorDepth maxSubdiv : Nat) :
    TacticM SubdivisionExecution := do
  goal.withContext do
    let ast := (← getAstWithReport func).expr
    let boundRat ← extractRatBound bound
    let (supportProof, _useChecked) ← getSupportProof ast
    let cfgExpr ← mkAppM ``EvalConfig.mk #[toExpr taylorDepth]

    let some bounds ← getSubdivBounds intervalInfo
      | throwError "interval_bound_subdiv: Only literal Set.Icc or IntervalRat intervals supported for subdivision"
    let (_lo, _hi, loRatExpr, hiRatExpr, leProof, fromSetIcc) := bounds

    let savedGoals ← getGoals

    let some proof ← proveStrictLowerBoundWithSubdiv ast supportProof loRatExpr hiRatExpr
        leProof boundRat cfgExpr taylorDepth maxSubdiv 0
      | throwError "interval_bound_subdiv: Failed even with subdivision (strict lower bound)"

    setGoals savedGoals
    let conclusionTerm ← Lean.Elab.Term.exprToSyntax proof.proof
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
    return proof.execution

/-- Run subdivision and return the facts retained by its successful proof. -/
def intervalBoundSubdivWithDepthReported
    (depth : Option Nat) (maxSubdiv : Nat) : TacticM SubdivisionOutcome := do
  intervalNormCore
  let depths : List Nat := match depth with
    | some n => [n]
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
      let (execution, checker, verifier) ← match boundGoal with
      | .forallLe _name interval func bound =>
        pure (← proveForallLeSubdivReported goal interval func bound taylorDepth maxSubdiv,
          ``LeanCert.Validity.checkUpperBound, ``Validity.verify_upper_bound_Icc_core)
      | .forallGe _name interval func bound =>
        pure (← proveForallGeSubdivReported goal interval func bound taylorDepth maxSubdiv,
          ``LeanCert.Validity.checkLowerBound, ``Validity.verify_lower_bound_Icc_core)
      | .forallLt _name interval func bound =>
        pure (← proveForallLtSubdivReported goal interval func bound taylorDepth maxSubdiv,
          ``LeanCert.Validity.checkStrictUpperBound,
          ``Validity.verify_strict_upper_bound_Icc_core)
      | .forallGt _name interval func bound =>
        pure (← proveForallGtSubdivReported goal interval func bound taylorDepth maxSubdiv,
          ``LeanCert.Validity.checkStrictLowerBound,
          ``Validity.verify_strict_lower_bound_Icc_core)
      return { taylorDepth, maxDepth := maxSubdiv, execution, checker, verifier }
    catch e =>
      lastErr := some e.toMessageData
  throwError m!"interval_bound_subdiv: All precision levels failed\n{lastErr.getD ""}"

/-- Compatibility core retaining the historical `TacticM Unit` shape. -/
def intervalBoundSubdivWithDepth (depth : Option Nat) (maxSubdiv : Nat) :
    TacticM Unit := do
  discard <| intervalBoundSubdivWithDepthReported depth maxSubdiv

/-- The interval_bound_subdiv tactic. -/
elab "interval_bound_subdiv" depth:(num)? subdivDepth:(num)?
    t:(leancertTrustItem)? : tactic => do
  let trust? ← LeanCert.Tactic.elabTrustItem? t
  LeanCert.Tactic.withTrustMode trust? do
    let maxSubdiv := match subdivDepth with
      | some n => n.getNat
      | none => 3
    let depth := depth.map (·.getNat)
    intervalBoundSubdivWithDepth depth maxSubdiv

end LeanCert.Tactic.Auto
