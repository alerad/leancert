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

/-- Extract a natural number from a Nat literal expression -/
private def extractNatLit (e : Lean.Expr) : MetaM (Option ℕ) := do
  -- Try raw literal first
  if let some n := e.rawNatLit? then
    return some n
  -- Try after reduction
  let e ← whnf e
  if let some n := e.rawNatLit? then
    return some n
  else return none

/-- Extract an integer from an Int literal expression -/
private def extractIntLit (e : Lean.Expr) : MetaM (Option ℤ) := do
  let e ← whnf e
  let fn := e.getAppFn
  let args := e.getAppArgs
  -- Int.ofNat n
  if fn.isConstOf ``Int.ofNat then
    if args.size > 0 then
      if let some n ← extractNatLit args[0]! then
        return some (n : ℤ)
    return none
  -- Int.negSucc n (represents -(n+1))
  else if fn.isConstOf ``Int.negSucc then
    if args.size > 0 then
      if let some n ← extractNatLit args[0]! then
        return some (-(n + 1 : ℤ))
    return none
  else return none

/-- Extract a rational from a Rat expression -/
private def extractRatFromRat (e : Lean.Expr) : MetaM (Option ℚ) := do
  -- Try without whnf first (preserves OfNat.ofNat structure)
  if let some q ← tryExtractRat e then
    return some q
  -- Then try with whnf
  let e' ← whnf e
  tryExtractRat e'
where
  tryExtractRat (e : Lean.Expr) : MetaM (Option ℚ) := do
    let fn := e.getAppFn
    let args := e.getAppArgs

    -- Check for Rat.ofInt
    if fn.isConstOf ``Rat.ofInt then
      if args.size > 0 then
        if let some i ← extractIntLit args[0]! then
          return some (i : ℚ)
      return none

    -- Check for OfNat.ofNat on Rat
    else if fn.isConstOf ``OfNat.ofNat then
      if args.size >= 2 then
        if let some n ← extractNatLit args[1]! then
          return some (n : ℚ)
      return none

    -- Check for Nat.cast to ℚ (handles ↑1, ↑2, etc.)
    else if fn.isConstOf ``Nat.cast || fn.isConstOf ``NatCast.natCast then
      if args.size > 0 then
        if let some n ← extractNatLit args.back! then
          return some (n : ℚ)
      return none

    -- Check for Int.cast to ℚ
    else if fn.isConstOf ``Int.cast || fn.isConstOf ``IntCast.intCast then
      if args.size > 0 then
        if let some i ← extractIntLit args.back! then
          return some (i : ℚ)
      return none

    -- Try to match Rat.mk' num den ...
    else if fn.isConstOf ``Rat.mk' then
      return none  -- TODO: implement if needed

    else
      -- Last resort: evaluate the expression directly.  Only safe for
      -- fully ground terms (no free variables or metavariables).
      if e.hasFVar || e.hasMVar then
        return none
      try
        let q ← unsafe evalExpr ℚ (mkConst ``Rat) e
        return some q
      catch _ =>
        return none

/-- Try to extract a rational value from a Lean expression that represents a real number.
    Handles: Rat.cast, OfNat.ofNat, Nat.cast, Int.cast, negations, and divisions.
    Also handles direct ℚ expressions as a fallback. -/
partial def extractRatFromReal (e : Lean.Expr) : MetaM (Option ℚ) := do
  let e ←
    if e.isMVar then
      if let some val ← getExprMVarAssignment? e.mvarId! then
        instantiateMVars val
      else
        pure e
    else
      instantiateMVars e
  -- First try without whnf (preserves structure like OfNat.ofNat)
  if let some q ← tryExtract e then
    return some q
  -- Then try with whnf
  let e' ← whnf e
  let e' ← instantiateMVars e'
  if let some q ← tryExtract e' then
    return some q
  -- Finally, try extracting from ℚ directly (for goals like ∀ x ∈ I, f(x) ≤ (1 : ℚ))
  extractRatFromRat e'
where
  tryExtract (e : Lean.Expr) : MetaM (Option ℚ) := do
    let fn := e.getAppFn
    let args := e.getAppArgs

    -- Case 1: Rat.cast q or RatCast.ratCast q
    if fn.isConstOf ``Rat.cast || fn.isConstOf ``RatCast.ratCast then
      if args.size > 0 then
        return ← extractRatFromRat args.back!
      else return none

    -- Case 2: OfNat.ofNat (for numeric literals like 2 : ℝ)
    else if fn.isConstOf ``OfNat.ofNat then
      -- OfNat.ofNat : {α : Type} → (n : ℕ) → [OfNat α n] → α
      -- args[1] is the natural number
      if args.size >= 2 then
        if let some n ← extractNatLit args[1]! then
          return some (n : ℚ)
      return none

    -- Case 3: Nat.cast n
    else if fn.isConstOf ``Nat.cast || fn.isConstOf ``NatCast.natCast then
      if args.size > 0 then
        if let some n ← extractNatLit args.back! then
          return some (n : ℚ)
      return none

    -- Case 4: Int.cast i
    else if fn.isConstOf ``Int.cast || fn.isConstOf ``IntCast.intCast then
      if args.size > 0 then
        if let some i ← extractIntLit args.back! then
          return some (i : ℚ)
      return none

    -- Case 5: Neg.neg x (for negative numbers)
    else if fn.isConstOf ``Neg.neg then
      if args.size > 0 then
        if let some q ← extractRatFromReal args.back! then
          return some (-q)
      return none

    -- Case 6: HDiv.hDiv a b (for fractions like 1/2)
    else if fn.isConstOf ``HDiv.hDiv then
      if args.size >= 6 then  -- HDiv.hDiv has 6 args: α β γ inst a b
        if let some a ← extractRatFromReal args[4]! then
          if let some b ← extractRatFromReal args[5]! then
            if b ≠ 0 then
              return some (a / b)
      return none

    -- Case 7: OfScientific.ofScientific (for decimal literals like 2.72)
    -- OfScientific.ofScientific : {α : Type} → [OfScientific α] → ℕ → Bool → ℕ → α
    -- 2.72 = ofScientific 272 true 2 = 272 * 10^(-2) = 272/100
    else if fn.isConstOf ``OfScientific.ofScientific then
      -- args: [type, inst, mantissa, isNegExp, exponent]
      if args.size >= 5 then
        if let some mantissa ← extractNatLit args[2]! then
          let isNegExp := args[3]!.isConstOf ``Bool.true
          if let some exp ← extractNatLit args[4]! then
            let base : ℚ := 10
            if isNegExp then
              -- mantissa * 10^(-exp) = mantissa / 10^exp
              return some ((mantissa : ℚ) / (base ^ exp))
            else
              -- mantissa * 10^exp
              return some ((mantissa : ℚ) * (base ^ exp))
      return none

    else return none

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
  -- Prefer the shared numeric parser used by reification.
  do
    match ← LeanCert.Meta.toRat? e with
    | some q => pure (some q)
    | none => extractRatFromReal e

end LeanCert.Tactic.Auto
