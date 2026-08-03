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
  deriving Repr, Inhabited

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

/-- One fixed registered-rule application retained for deterministic replay.

The candidate generator is deliberately absent: replay supplies the exact
output interval and reruns the registered checker. -/
structure RegisteredEnclosureCertificateEntry where
  rule : UnaryEnclosureRule
  request : UnaryEnclosureRequest
  output : IntervalRat
  deriving Repr, Inhabited

/-- Exact subdivision and registered-rule evidence retained by a successful
unary enclosure proof.  Each leaf contains the fixed checker inputs in the
order in which the compositional executor consumes registered applications. -/
inductive RegisteredEnclosureCertificateTree where
  | leaf
      (input : IntervalRat)
      (output : IntervalRat)
      (entries : Array RegisteredEnclosureCertificateEntry)
      (compositionSteps : Nat)
  | bisect
      (input : IntervalRat)
      (left right : RegisteredEnclosureCertificateTree)
  deriving Repr, Inhabited

/-- Replayable evidence for one registered-enclosure bound. -/
structure RegisteredEnclosureCertificate where
  precision : Int
  taylorDepth : Nat
  configuredMaxDepth : Nat
  tree : RegisteredEnclosureCertificateTree
  deriving Repr, Inhabited

end LeanCert.Tactic.Extension
