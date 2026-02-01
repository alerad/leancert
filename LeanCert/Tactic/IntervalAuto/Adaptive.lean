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
# Adaptive Branch-and-Bound Tactic

The `interval_bound_adaptive` tactic uses branch-and-bound global optimization.
-/

open Lean Meta Elab Tactic Term

namespace LeanCert.Tactic.Auto

open LeanCert.Meta
open LeanCert.Core
open LeanCert.Engine
open LeanCert.Validity
open LeanCert.Engine.Optimization
open LeanCert.Validity.GlobalOpt

/-- Prove upper bound using adaptive branch-and-bound optimization -/
private def proveForallLeAdaptive (goal : MVarId) (intervalInfo : IntervalInfo)
    (func bound : Lean.Expr) (maxIters : Nat) : TacticM Unit := do
  goal.withContext do
    let ast ← getAst func
    let boundRat ← extractRatBound bound
    let supportProof ← LeanCert.Meta.mkSupportedProof ast

    let some bounds ← getSubdivBounds intervalInfo
      | throwError "interval_bound_adaptive: Only literal Set.Icc or IntervalRat intervals supported"
    let (_lo, _hi, loRatExpr, hiRatExpr, leProof, fromSetIcc) := bounds

    let globalOptCfgExpr ← mkAppM ``GlobalOptConfig.mk
      #[toExpr maxIters, toExpr (1/10000 : ℚ), toExpr false, toExpr (15 : Nat)]

    let intervalRatExpr ← mkAppM ``IntervalRat.mk #[loRatExpr, hiRatExpr, leProof]
    let box ← mkListLit (mkConst ``IntervalRat) [intervalRatExpr]

    let checkExpr ← mkAppM ``checkGlobalUpperBound #[ast, box, boundRat, globalOptCfgExpr]
    let checkTy ← mkAppM ``Eq #[checkExpr, mkConst ``Bool.true]

    let savedGoals ← getGoals
    let checkGoal ← mkFreshExprMVar checkTy
    setGoals [checkGoal.mvarId!]
    try
      evalTactic (← `(tactic| native_decide))
    catch _ =>
      throwError "interval_bound_adaptive: Adaptive verification failed - bound not tight enough"
    let checkProof := checkGoal

    setGoals savedGoals

    let proof ← mkAppM ``verify_global_upper_bound
      #[ast, supportProof, box, boundRat, globalOptCfgExpr, checkProof]

    let conclusionTerm ← Lean.Elab.Term.exprToSyntax proof
    let intervalRatSyntax ← Lean.Elab.Term.exprToSyntax intervalRatExpr
    if fromSetIcc then
      evalTactic (← `(tactic| intro _x _hx))
      evalTactic (← `(tactic|
        have hρ : Box.envMem (fun i => List.getD [_x] i 0) [$intervalRatSyntax] := by
          intro ⟨i, hi⟩
          simp only [List.length_singleton] at hi
          have hi' : i = 0 := Nat.lt_one_iff.mp hi
          subst hi'
          simp only [List.getD_cons_zero, List.getElem_cons_zero, IntervalRat.mem_def]
          constructor <;> (push_cast; linarith [_hx.1, _hx.2])))
      evalTactic (← `(tactic|
        have hzero : ∀ i, i ≥ ([$intervalRatSyntax] : Box).length → (fun j => List.getD [_x] j 0) i = 0 := by
          intro i hi
          simp only [List.length_singleton, ge_iff_le] at hi
          have hnot : ¬ i < [_x].length := Nat.not_lt.mpr hi
          simp [List.getD, List.getElem?_eq_none (Nat.not_lt.mp hnot)]))
      evalTactic (← `(tactic| have heval := $conclusionTerm (fun i => List.getD [_x] i 0) hρ hzero))
      evalTactic (← `(tactic| simp only [List.getD_cons_zero] at heval))
      evalTactic (← `(tactic| convert heval using 1))
      let goals ← getGoals
      for g in goals do
        setGoals [g]
        try evalTactic (← `(tactic| rfl))
        catch _ =>
          try evalTactic (← `(tactic| simp only [Rat.divInt_eq_div]; push_cast; ring))
          catch _ => pure ()
    else
      evalTactic (← `(tactic| intro _x _hx))
      evalTactic (← `(tactic|
        have hρ : Box.envMem (fun i => List.getD [_x] i 0) [$intervalRatSyntax] := by
          intro ⟨i, hi⟩
          simp only [List.length_singleton] at hi
          have hi' : i = 0 := Nat.lt_one_iff.mp hi
          subst hi'
          simp only [List.getD_cons_zero, List.getElem_cons_zero]
          exact _hx))
      evalTactic (← `(tactic|
        have hzero : ∀ i, i ≥ ([$intervalRatSyntax] : Box).length → (fun j => List.getD [_x] j 0) i = 0 := by
          intro i hi
          simp only [List.length_singleton, ge_iff_le] at hi
          have hnot : ¬ i < [_x].length := Nat.not_lt.mpr hi
          simp [List.getD, List.getElem?_eq_none (Nat.not_lt.mp hnot)]))
      evalTactic (← `(tactic| have heval := $conclusionTerm (fun i => List.getD [_x] i 0) hρ hzero))
      evalTactic (← `(tactic| simp only [List.getD_cons_zero] at heval))
      evalTactic (← `(tactic| convert heval using 1))
      let goals ← getGoals
      for g in goals do
        setGoals [g]
        try evalTactic (← `(tactic| rfl))
        catch _ => pure ()

/-- Prove lower bound using adaptive branch-and-bound optimization -/
private def proveForallGeAdaptive (goal : MVarId) (intervalInfo : IntervalInfo)
    (func bound : Lean.Expr) (maxIters : Nat) : TacticM Unit := do
  goal.withContext do
    let ast ← getAst func
    let boundRat ← extractRatBound bound
    let supportProof ← LeanCert.Meta.mkSupportedProof ast

    let some bounds ← getSubdivBounds intervalInfo
      | throwError "interval_bound_adaptive: Only literal Set.Icc or IntervalRat intervals supported"
    let (_lo, _hi, loRatExpr, hiRatExpr, leProof, fromSetIcc) := bounds

    let globalOptCfgExpr ← mkAppM ``GlobalOptConfig.mk
      #[toExpr maxIters, toExpr (1/10000 : ℚ), toExpr false, toExpr (15 : Nat)]

    let intervalRatExpr ← mkAppM ``IntervalRat.mk #[loRatExpr, hiRatExpr, leProof]
    let box ← mkListLit (mkConst ``IntervalRat) [intervalRatExpr]

    let checkExpr ← mkAppM ``checkGlobalLowerBound #[ast, box, boundRat, globalOptCfgExpr]
    let checkTy ← mkAppM ``Eq #[checkExpr, mkConst ``Bool.true]

    let savedGoals ← getGoals
    let checkGoal ← mkFreshExprMVar checkTy
    setGoals [checkGoal.mvarId!]
    try
      evalTactic (← `(tactic| native_decide))
    catch _ =>
      throwError "interval_bound_adaptive: Adaptive verification failed - bound not tight enough"
    let checkProof := checkGoal

    setGoals savedGoals

    let proof ← mkAppM ``verify_global_lower_bound
      #[ast, supportProof, box, boundRat, globalOptCfgExpr, checkProof]

    let conclusionTerm ← Lean.Elab.Term.exprToSyntax proof
    let intervalRatSyntax ← Lean.Elab.Term.exprToSyntax intervalRatExpr
    if fromSetIcc then
      evalTactic (← `(tactic| intro _x _hx))
      evalTactic (← `(tactic|
        have hρ : Box.envMem (fun i => List.getD [_x] i 0) [$intervalRatSyntax] := by
          intro ⟨i, hi⟩
          simp only [List.length_singleton] at hi
          have hi' : i = 0 := Nat.lt_one_iff.mp hi
          subst hi'
          simp only [List.getD_cons_zero, List.getElem_cons_zero, IntervalRat.mem_def]
          constructor <;> (push_cast; linarith [_hx.1, _hx.2])))
      evalTactic (← `(tactic|
        have hzero : ∀ i, i ≥ ([$intervalRatSyntax] : Box).length → (fun j => List.getD [_x] j 0) i = 0 := by
          intro i hi
          simp only [List.length_singleton, ge_iff_le] at hi
          have hnot : ¬ i < [_x].length := Nat.not_lt.mpr hi
          simp [List.getD, List.getElem?_eq_none (Nat.not_lt.mp hnot)]))
      evalTactic (← `(tactic| have heval := $conclusionTerm (fun i => List.getD [_x] i 0) hρ hzero))
      evalTactic (← `(tactic| simp only [List.getD_cons_zero] at heval))
      evalTactic (← `(tactic| convert heval using 1))
      let goals ← getGoals
      for g in goals do
        setGoals [g]
        try evalTactic (← `(tactic| rfl))
        catch _ =>
          try evalTactic (← `(tactic| simp only [Rat.divInt_eq_div]; push_cast; ring))
          catch _ => pure ()
    else
      evalTactic (← `(tactic| intro _x _hx))
      evalTactic (← `(tactic|
        have hρ : Box.envMem (fun i => List.getD [_x] i 0) [$intervalRatSyntax] := by
          intro ⟨i, hi⟩
          simp only [List.length_singleton] at hi
          have hi' : i = 0 := Nat.lt_one_iff.mp hi
          subst hi'
          simp only [List.getD_cons_zero, List.getElem_cons_zero]
          exact _hx))
      evalTactic (← `(tactic|
        have hzero : ∀ i, i ≥ ([$intervalRatSyntax] : Box).length → (fun j => List.getD [_x] j 0) i = 0 := by
          intro i hi
          simp only [List.length_singleton, ge_iff_le] at hi
          have hnot : ¬ i < [_x].length := Nat.not_lt.mpr hi
          simp [List.getD, List.getElem?_eq_none (Nat.not_lt.mp hnot)]))
      evalTactic (← `(tactic| have heval := $conclusionTerm (fun i => List.getD [_x] i 0) hρ hzero))
      evalTactic (← `(tactic| simp only [List.getD_cons_zero] at heval))
      evalTactic (← `(tactic| convert heval using 1))
      let goals ← getGoals
      for g in goals do
        setGoals [g]
        try evalTactic (← `(tactic| rfl))
        catch _ => pure ()

/-- The interval_bound_adaptive tactic. -/
elab "interval_bound_adaptive" iters:(num)? : tactic => do
  let maxIters := match iters with
    | some n => n.getNat
    | none => 200

  try
    evalTactic (← `(tactic| intro _x _hx; simp only [ge_iff_le, gt_iff_lt]; revert _x _hx))
  catch _ =>
    try evalTactic (← `(tactic| simp only [ge_iff_le, gt_iff_lt]))
    catch _ => pure ()
  try
    evalTactic (← `(tactic| simp only [sq, pow_two, pow_succ, pow_zero, pow_one, one_mul, mul_one] at *))
  catch _ => pure ()

  let goal ← getMainGoal
  let goalType ← goal.getType

  let some boundGoal := (← parseBoundGoal goalType)
    | throwError "interval_bound_adaptive: Could not parse goal as bound goal"

  match boundGoal with
  | .forallLe _name interval func bound =>
    proveForallLeAdaptive goal interval func bound maxIters
  | .forallGe _name interval func bound =>
    proveForallGeAdaptive goal interval func bound maxIters
  | .forallLt _name _interval _func _bound =>
    throwError "interval_bound_adaptive: Strict bounds not yet supported"
  | .forallGt _name _interval _func _bound =>
    throwError "interval_bound_adaptive: Strict bounds not yet supported"

end LeanCert.Tactic.Auto
