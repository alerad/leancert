/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Tactic.LeanCert.Semantic.Goal

/-! # Lightweight comparison parsing

Shared comparison parsing for focused tactic front ends and the full semantic
router. This module deliberately has no solver imports.
-/

open Lean

namespace LeanCert.Tactic.Semantic

/-- A comparison application before either operand is normalized. -/
structure RawComparison where
  comparison : Comparison
  lhs : Lean.Expr
  rhs : Lean.Expr

/-- Read a comparison application without reducing either operand. -/
def parseRawComparison? (goal : Lean.Expr) : Option RawComparison := do
  let fn := goal.getAppFn
  let args := goal.getAppArgs
  if fn.isConstOf ``Eq && args.size >= 3 then
    return ⟨.eq, args[args.size - 2]!, args[args.size - 1]!⟩
  if fn.isConstOf ``LE.le && args.size >= 4 then
    return ⟨.le, args[args.size - 2]!, args[args.size - 1]!⟩
  if fn.isConstOf ``LT.lt && args.size >= 4 then
    return ⟨.lt, args[args.size - 2]!, args[args.size - 1]!⟩
  if fn.isConstOf ``GE.ge && args.size >= 4 then
    return ⟨.le, args[args.size - 1]!, args[args.size - 2]!⟩
  if fn.isConstOf ``GT.gt && args.size >= 4 then
    return ⟨.lt, args[args.size - 1]!, args[args.size - 2]!⟩
  if fn.isConstOf ``Ne && args.size >= 3 then
    return ⟨.ne, args[args.size - 2]!, args[args.size - 1]!⟩
  none

end LeanCert.Tactic.Semantic
