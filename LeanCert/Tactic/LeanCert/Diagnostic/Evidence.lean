/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import Lean
import LeanCert.Core.IntervalRat.Basic
import LeanCert.Tactic.LeanCert.Semantic.Domain
import LeanCert.Tactic.LeanCert.Semantic.Goal

/-!
# Structured Solver Evidence

Expected numerical and capability failures are values.  Exceptions are
reserved for implementation defects.
-/

open Lean

namespace LeanCert.Tactic.Diagnostic

structure UnsupportedEvidence where
  expression : String
  remainingHead : Option Name := none
  unfolded : Array Name := #[]
  detail : Option String := none
  deriving Inhabited

structure NumericalEvidence where
  enclosure : Option LeanCert.Core.IntervalRat := none
  requested : Option String := none
  detail : String
  deriving Inhabited

structure CandidateEvidence where
  candidate : Option String := none
  checker : Option Name := none
  enclosure : Option LeanCert.Core.IntervalRat := none
  detail : String
  deriving Inhabited

structure RefutationEvidence where
  witness : String
  enclosure : Option LeanCert.Core.IntervalRat := none
  verifier : Option Name := none
  detail : Option String := none
  deriving Inhabited

structure DomainObstruction where
  source : Semantic.IntervalSyntax
  reason : String
  operation : Option String := none
  deriving Inhabited

/-- Whether a router diagnostic should be compact (`leancert`) or explanatory
(`leancert?`). Both modes are rendered from the same typed failure. -/
inductive DiagnosticVerbosity where
  | compact
  | explain
  deriving DecidableEq, Inhabited

/-- Sanitized record of one strategy attempt. Raw exception strings remain
trace-only and never become user-facing portfolio outcomes. -/
structure AttemptDiagnostic where
  strategy : String
  outcome : String
  deriving Inhabited

/-- Major semantic-router failures. This is intentionally independent of the
solver protocol's `AttemptOutcome` to avoid an import cycle. -/
inductive RouterFailure where
  | unsupportedGoal (goal detail : String)
  | unsupportedExpression (expression detail : String)
  | unsupportedDomain (intent : Semantic.GoalIntent) (details : Array String)
  | domainObstruction (intent : Semantic.GoalIntent) (reason : String)
  | portfolioExhausted (intent : Semantic.GoalIntent)
      (attempts : Array AttemptDiagnostic) (spent budget : Nat)
  | certifiedRefutation (intent : Option Semantic.GoalIntent)
      (evidence : RefutationEvidence)
  | childFailure (index total : Nat) (intent : Option Semantic.GoalIntent)
      (detail : String)
  | conjunctionFailure (detail : String)
  | internalError (detail : String)
  deriving Inhabited

end LeanCert.Tactic.Diagnostic
