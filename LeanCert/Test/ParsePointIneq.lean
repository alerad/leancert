/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
module

public import LeanCert.Tactic.IntervalAuto.Parse
public import Mathlib.Basic.Real.Basic

/-!
# Regression tests for `parsePointIneq`

Under the module system, the bodies of unexposed declarations such as `Real.instLT` and
`Real.instLE` are not available to downstream modules. `whnf` therefore unfolds `a < b` only as far
as the stuck projection `Real.instLT.1 a b`, which is neither `LT.lt` nor a constant whose name ends
in `lt`.

The previous definition of `parsePointIneq` called `whnf` on the goal before matching on it, so it
failed to recognise any inequality between reals. The current definition first matches on the goal
as written and only falls back to `whnf` if that fails.
-/

open Lean Meta Elab Term

namespace LeanCert.Test.ParsePointIneq

open LeanCert.Tactic.Auto

/-- The previous definition of `parsePointIneq`, kept verbatim for regression testing. -/
meta def oldParsePointIneq (goal : Lean.Expr) :
    MetaM (Option (Lean.Expr × Lean.Expr × Bool × Bool)) := do
  let goal ← whnf goal
  return parsePointIneq.parsePointIneqApp goal

/-- Elaborate `stx`, run `parse` on it and log the result. -/
meta def logParse (parse : Lean.Expr → MetaM (Option (Lean.Expr × Lean.Expr × Bool × Bool)))
    (stx : Term) : TermElabM Unit := do
  let goal ← elabTerm stx none
  match ← parse goal with
  | some (lhs, rhs, isStrict, isReversed) =>
    logInfo m!"lhs := {lhs}, rhs := {rhs}, isStrict := {isStrict}, isReversed := {isReversed}"
  | none => logInfo m!"none"

/-! ### `whnf` gets stuck on the unexposed order instances on `ℝ` -/

/-- info: Real.instLT.1 1 2 -/
#guard_msgs in
run_elab do logInfo m!"{← whnf (← elabTerm (← `((1 : ℝ) < 2)) none)}"

/-- info: Real.instLE.1 1 2 -/
#guard_msgs in
run_elab do logInfo m!"{← whnf (← elabTerm (← `((1 : ℝ) ≤ 2)) none)}"

/-! ### The previous definition fails on every inequality between reals -/

/-- info: none -/
#guard_msgs in
run_elab logParse oldParsePointIneq (← `((1 : ℝ) < 2))

/-- info: none -/
#guard_msgs in
run_elab logParse oldParsePointIneq (← `((1 : ℝ) ≤ 2))

/-- info: none -/
#guard_msgs in
run_elab logParse oldParsePointIneq (← `((1 : ℝ) > 2))

/-- info: none -/
#guard_msgs in
run_elab logParse oldParsePointIneq (← `((1 : ℝ) ≥ 2))

/-! ### The current definition handles them -/

/-- info: lhs := 1, rhs := 2, isStrict := true, isReversed := false -/
#guard_msgs in
run_elab logParse parsePointIneq (← `((1 : ℝ) < 2))

/-- info: lhs := 1, rhs := 2, isStrict := false, isReversed := false -/
#guard_msgs in
run_elab logParse parsePointIneq (← `((1 : ℝ) ≤ 2))

/-- info: lhs := 1, rhs := 2, isStrict := true, isReversed := true -/
#guard_msgs in
run_elab logParse parsePointIneq (← `((1 : ℝ) > 2))

/-- info: lhs := 1, rhs := 2, isStrict := false, isReversed := true -/
#guard_msgs in
run_elab logParse parsePointIneq (← `((1 : ℝ) ≥ 2))

/-- info: lhs := Real.exp 1, rhs := 3, isStrict := true, isReversed := false -/
#guard_msgs in
run_elab logParse parsePointIneq (← `(Real.exp 1 < 3))

end LeanCert.Test.ParsePointIneq
