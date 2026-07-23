/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import Lean
import LeanCert.Tactic.LeanCert.Semantic.Domain

/-!
# Semantic Goal Representation

The public router parses a theorem once into this internal representation.
The original expression is retained for proof transport and diagnostics.
-/

open Lean

namespace LeanCert.Tactic.Semantic

/-- Stable user-facing labels for the mathematical theorem families handled by
LeanCert.  This is reporting metadata, never a substitute for parsed payload. -/
inductive GoalIntent where
  | integralBound
  | uniqueRoot
  | rootExists
  | noRoot
  | argmin
  | argmax
  | existentialMinimum
  | existentialMaximum
  | finiteSum
  | multivariateBound
  | intervalBound
  | pointInequality
  | certificateCheck
  | conjunction
  deriving Repr, BEq, Inhabited

/-- Solver-level comparisons.  `≥` and `>` are normalized by swapping sides. -/
inductive Comparison where
  | lt
  | le
  | eq
  | ne
  deriving Repr, BEq, Inhabited

/-- Quantifier attached to a zero-finding problem. -/
inductive RootKind where
  | exists
  | unique
  | excluded
  deriving Repr, BEq, Inhabited

/-- Whether an optimization theorem requests a minimum or maximum. -/
inductive ExtremumKind where
  | minimum
  | maximum
  deriving Repr, BEq, Inhabited

/-- One source binder and its mathematical domain.

`binderId` is retained when the parser has introduced a local declaration.
Solvers must not recover variables by user-facing names. -/
structure BoundVariable where
  userName : Name
  type : Lean.Expr
  binderId : Option FVarId := none
  domain : IntervalSyntax
  deriving Inhabited

structure PointSpec where
  original : Lean.Expr
  comparison : Comparison
  lhs : Lean.Expr
  rhs : Lean.Expr
  deriving Inhabited

structure BoundSpec where
  original : Lean.Expr
  boundVars : Array BoundVariable
  comparison : Comparison
  /-- Closed functions of all bound variables, preserving operand order after
  `≥`/`>` normalization.  This represents both upper and lower bounds without
  adding solver-level `ge`/`gt` cases. -/
  lhs : Lean.Expr
  rhs : Lean.Expr
  /-- Both original operands depended on quantified variables and were
  normalized to `lhs - rhs ⋚ 0`. -/
  normalizedDifference : Bool := false
  deriving Inhabited

structure RootSpec where
  original : Lean.Expr
  kind : RootKind
  boundVar : BoundVariable
  function : Lean.Expr
  /-- The source predicate was written `0 = f x` rather than `f x = 0`. -/
  equationReversed : Bool := false
  deriving Inhabited

structure ExtremumSpec where
  original : Lean.Expr
  kind : ExtremumKind
  boundVar : BoundVariable
  function : Lean.Expr
  existenceOnly : Bool
  deriving Inhabited

structure DiscoverySpec where
  original : Lean.Expr
  kind : ExtremumKind
  witnessType : Lean.Expr
  boundVars : Array BoundVariable
  function : Lean.Expr
  deriving Inhabited

structure IntegralSpec where
  original : Lean.Expr
  integral : Lean.Expr
  integrand : Lean.Expr
  lo : Lean.Expr
  hi : Lean.Expr
  comparison : Comparison
  lhs : Lean.Expr
  rhs : Lean.Expr
  deriving Inhabited

structure FiniteSumSpec where
  original : Lean.Expr
  sum : Lean.Expr
  comparison : Comparison
  lhs : Lean.Expr
  rhs : Lean.Expr
  deriving Inhabited

/-- Mathematical theorem shapes understood by the semantic front door. -/
inductive SemanticGoal where
  | point (spec : PointSpec)
  | bound (spec : BoundSpec)
  | root (spec : RootSpec)
  | extremum (spec : ExtremumSpec)
  | discovery (spec : DiscoverySpec)
  | integral (spec : IntegralSpec)
  | finiteSum (spec : FiniteSumSpec)
  | certificateCheck (original checker : Lean.Expr)
  | allOf (original : Lean.Expr) (children : Array SemanticGoal)
  deriving Inhabited

/-- The original proposition represented by a semantic goal. -/
def SemanticGoal.original : SemanticGoal → Lean.Expr
  | .point spec => spec.original
  | .bound spec => spec.original
  | .root spec => spec.original
  | .extremum spec => spec.original
  | .discovery spec => spec.original
  | .integral spec => spec.original
  | .finiteSum spec => spec.original
  | .certificateCheck original _ => original
  | .allOf original _ => original

end LeanCert.Tactic.Semantic
