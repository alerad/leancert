/-
Copyright (c) 2024 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import Lean
import LeanCert.Core.IntervalRat.Basic

/-!
# Core Types for Interval Tactics

This module defines the core data structures used by interval arithmetic tactics:
- `IntervalInfo`: Information about an interval source
- `BoundGoal`: Result of analyzing a univariate bound goal
- `VarIntervalInfo`: Information about a quantified variable and its interval
- `MultivariateBoundGoal`: Result of analyzing a multivariate bound goal
- `GlobalBoundGoal`: Result of analyzing a global optimization bound goal
- `RootGoal`: Result of analyzing a root finding goal
-/

open Lean Meta

namespace LeanCert.Tactic.Auto

-- Debug trace option for interval_decide
initialize registerTraceClass `interval_decide

-- Unified debug option for all interval tactics
register_option leancert.debug : Bool := {
  defValue := false
  descr := "Enable detailed diagnostic output for all LeanCert interval tactics"
}

/-- Check if LeanCert debug mode is enabled -/
def isLeanCertDebugEnabled : CoreM Bool :=
  return (← getOptions).getBool `leancert.debug false

/-- Information about interval source -/
structure IntervalInfo where
  /-- The IntervalRat expression to use in proofs -/
  intervalRat : Lean.Expr
  /-- If converted from Set.Icc, contains (lo, hi, loRatExpr, hiRatExpr, leProof, origLoExpr, origHiExpr) -/
  fromSetIcc : Option (ℚ × ℚ × Lean.Expr × Lean.Expr × Lean.Expr × Lean.Expr × Lean.Expr) := none
  deriving Repr

/-- Result of analyzing a bound goal -/
inductive BoundGoal where
  /-- ∀ x ∈ I, f x ≤ c -/
  | forallLe (varName : Name) (interval : IntervalInfo) (func : Lean.Expr) (bound : Lean.Expr)
  /-- ∀ x ∈ I, c ≤ f x -/
  | forallGe (varName : Name) (interval : IntervalInfo) (func : Lean.Expr) (bound : Lean.Expr)
  /-- ∀ x ∈ I, f x < c -/
  | forallLt (varName : Name) (interval : IntervalInfo) (func : Lean.Expr) (bound : Lean.Expr)
  /-- ∀ x ∈ I, c < f x -/
  | forallGt (varName : Name) (interval : IntervalInfo) (func : Lean.Expr) (bound : Lean.Expr)
  deriving Repr

/-- Information about a quantified variable and its interval -/
structure VarIntervalInfo where
  /-- Variable name -/
  varName : Name
  /-- Variable type -/
  varType : Lean.Expr
  /-- Extracted interval (lo, hi rationals and their expressions) -/
  intervalRat : Lean.Expr
  /-- Original lower bound expression for Set.Icc -/
  loExpr : Lean.Expr
  /-- Original upper bound expression for Set.Icc -/
  hiExpr : Lean.Expr
  /-- Low bound as rational -/
  lo : ℚ
  /-- High bound as rational -/
  hi : ℚ
  deriving Repr, Inhabited

/-- Result of analyzing a multivariate bound goal -/
inductive MultivariateBoundGoal where
  /-- ∀ x₁ ∈ I₁, ..., ∀ xₙ ∈ Iₙ, f(x₁,...,xₙ) ≤ c -/
  | forallLe (vars : Array VarIntervalInfo) (func : Lean.Expr) (bound : Lean.Expr)
  /-- ∀ x₁ ∈ I₁, ..., ∀ xₙ ∈ Iₙ, c ≤ f(x₁,...,xₙ) -/
  | forallGe (vars : Array VarIntervalInfo) (func : Lean.Expr) (bound : Lean.Expr)
  deriving Repr

/-- Result of analyzing a global bound goal -/
inductive GlobalBoundGoal where
  /-- ∀ ρ ∈ B, (zero extension) → c ≤ f(ρ) -/
  | globalGe (box : Lean.Expr) (expr : Lean.Expr) (bound : Lean.Expr)
  /-- ∀ ρ ∈ B, (zero extension) → f(ρ) ≤ c -/
  | globalLe (box : Lean.Expr) (expr : Lean.Expr) (bound : Lean.Expr)
  deriving Repr

/-- Result of analyzing a root finding goal -/
inductive RootGoal where
  /-- ∀ x ∈ I, f x ≠ 0 -/
  | forallNeZero (varName : Name) (interval : Lean.Expr) (func : Lean.Expr)
  deriving Repr

end LeanCert.Tactic.Auto
