/-
Copyright (c) 2024 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import Lean
import LeanCert.Core.IntervalRat.Basic
import LeanCert.Meta.Numeral

/-!
# Rational Extraction Utilities

Utilities for extracting rational numbers from Lean expressions representing
real number literals or coercions.
-/

open Lean Meta

namespace LeanCert.Tactic.Auto

open LeanCert.Core

/-- Try to extract a rational value from a normalized real-number expression. -/
def extractRatFromReal (e : Lean.Expr) : MetaM (Option ℚ) := do
  LeanCert.Meta.Numeral.toRealRatNormalized? e

/-- Build an IntervalRat expression from two rational expressions and their Lean representations -/
def mkIntervalRat (loExpr hiExpr : Lean.Expr) (lo hi : ℚ) : MetaM Lean.Expr := do
  if lo > hi then
    throwError "Cannot create interval: lo ({lo}) > hi ({hi})"
  -- Build ⟨lo, hi, proof⟩
  -- The proof is `lo ≤ hi` which we can close with `by norm_num` or `by decide`
  let proofType ← mkAppM ``LE.le #[loExpr, hiExpr]

  -- Create the proof using decide (works for concrete rationals)
  let proof ← mkDecideProof proofType

  mkAppM ``IntervalRat.mk #[loExpr, hiExpr, proof]

/-- Try to convert an expression directly to a rational (if it IS a rational constant) -/
def toRat? (e : Lean.Expr) : MetaM (Option ℚ) :=
  LeanCert.Meta.Numeral.toRat? e

end LeanCert.Tactic.Auto
