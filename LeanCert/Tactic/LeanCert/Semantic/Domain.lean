/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import Lean

/-!
# Semantic Domains

Domain syntax and proof-bearing prepared domains used by the semantic
`leancert` pipeline.  In particular, an empty closed interval is a semantic
fact rather than an invalid `IntervalRat`.
-/

open Lean

namespace LeanCert.Tactic.Semantic

/-- Interval topology as written in the source theorem. -/
inductive IntervalKind where
  | closed
  | open
  | leftOpen
  | rightOpen
  | unorderedClosed
  | intervalRat
  deriving Repr, BEq, Inhabited

/-- Source-level interval information retained for diagnostics and transport. -/
structure IntervalSyntax where
  original : Lean.Expr
  kind : IntervalKind
  lo : Option Lean.Expr := none
  hi : Option Lean.Expr := none
  deriving Inhabited

/-- Why a source domain cannot currently be sent to a numerical solver. -/
inductive UnsupportedDomainReason where
  | topology (kind : IntervalKind)
  | nonRationalEndpoint (which : String) (endpoint : Lean.Expr)
  | unsupportedCarrier (type : Lean.Expr)
  | unsupportedSyntax (rendered : String)
  deriving Repr, Inhabited

/-- A domain prepared for proof construction.

Every semantic reduction carries the proof which justifies transporting the
original theorem.  `membershipIff` has the source-specific membership
equivalence type; clients validate its exact type before use. -/
inductive PreparedInterval where
  | empty
      (source : IntervalSyntax)
      (isEmpty : Lean.Expr)
  | singleton
      (source : IntervalSyntax)
      (point : Lean.Expr)
      (membershipIff : Lean.Expr)
  | closedRat
      (source : IntervalSyntax)
      (interval : Lean.Expr)
      (membershipIff : Lean.Expr)
  | symbolicClosed
      (source : IntervalSyntax)
      (lo : Lean.Expr)
      (hi : Lean.Expr)
      (ordered : Option Lean.Expr := none)
  | unsupported
      (source : IntervalSyntax)
      (reason : UnsupportedDomainReason)
  deriving Inhabited

/-- Whether a prepared domain can contain a witness. -/
def PreparedInterval.isProvablyEmpty : PreparedInterval → Bool
  | .empty .. => true
  | _ => false

end LeanCert.Tactic.Semantic
