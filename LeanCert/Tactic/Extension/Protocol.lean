/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Core.IntervalRat.Basic

/-!
# Downstream enclosure extension protocol

This module defines the data shared by downstream unary enclosure rules.  Candidate
generation is deliberately untrusted: a candidate becomes usable only after its
registered Boolean checker and soundness theorem validate it.

Execution of registered rules is not part of this lightweight module. The registry is
the stable boundary consumed by the semantic tactic in a separate execution layer.
-/

namespace LeanCert.Tactic.Extension

open LeanCert.Core

/-- Input and effort controls supplied to a unary enclosure candidate generator. -/
structure UnaryEnclosureRequest where
  input : IntervalRat
  precision : Int := -53
  taylorDepth : Nat := 10
  deriving Repr

/-- Expected, non-exceptional reasons why an untrusted candidate generator may stop. -/
inductive EnclosureCandidateFailure where
  | domainObstruction (detail : String)
  | inconclusive (detail : String)
  deriving Repr, Inhabited

/-- An untrusted generator of a proposed output interval for a unary real function. -/
abbrev UnaryEnclosureCandidate :=
  UnaryEnclosureRequest → Except EnclosureCandidateFailure IntervalRat

/-- An executable checker for a proposed unary enclosure. -/
abbrev UnaryEnclosureChecker :=
  UnaryEnclosureRequest → IntervalRat → Bool

/-- Serializable metadata retained for a registered unary enclosure theorem. -/
structure UnaryEnclosureRule where
  functionName : Lean.Name
  candidateName : Lean.Name
  checkerName : Lean.Name
  theoremName : Lean.Name
  rulePriority : Nat := 1000
  deriving Repr, Inhabited, BEq

end LeanCert.Tactic.Extension
