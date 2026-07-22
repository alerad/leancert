/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import Lean
import LeanCert.Core.IntervalRat.Basic

/-!
# Semantic Solver Infrastructure

Shared result types for safely composing LeanCert's existing proof-producing
tactics.  The public semantic router is intentionally not defined here; these
types let dedicated solvers be hardened and tested before routing is added.
-/

open Lean

namespace LeanCert.Tactic

/-- The mathematical shape recognized by a LeanCert solver. -/
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
  deriving Repr, BEq, Inhabited

/-- A stable description of the solver which closed a focused goal. -/
structure SolverReport where
  intent : GoalIntent
  method : String
  backend : Option String := none
  enclosure : Option LeanCert.Core.IntervalRat := none
  checker : Option Name := none
  verifier : Option Name := none
  deriving Repr, Inhabited

/-- Structured reasons why a speculative solver attempt did not close its goal.

Strings are used for rendered expressions and goals deliberately: failed
attempts restore their metavariable state, so retaining `MessageData` or raw
expressions from that state would make later diagnostics unstable. -/
inductive AttemptFailure where
  | unsupportedExpression (remaining : String) (unfolded : Array Name := #[])
  | certificateRejected (enclosure : Option LeanCert.Core.IntervalRat := none)
  | incompleteProof (remainingGoals : Array String)
  | invalidDomain (detail : String)
  | budgetExhausted (reports : Array SolverReport)
  | internalFailure (detail : String)
  deriving Repr, Inhabited

end LeanCert.Tactic
