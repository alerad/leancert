/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import Lean
import LeanCert.Core.IntervalRat.Basic
import LeanCert.Tactic.LeanCert.Semantic.Domain

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

end LeanCert.Tactic.Diagnostic
