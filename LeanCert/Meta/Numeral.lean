/-
Copyright (c) 2024 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import Lean
import LeanCert.Core.Expr

/-!
# Meta-level Numeral Extraction

Utilities for extracting rational constants from elaborated Lean expressions.
The goal is to support multiple equivalent syntactic encodings (literals,
casts, scientific notation, arithmetic on constants) in one place.
-/

open Lean Meta

namespace LeanCert.Meta.Numeral

/-- Attempt to parse a Lean expression as a rational constant. -/
partial def toRat? (e : Lean.Expr) : MetaM (Option ℚ) := do
  -- Fast path: raw Nat literal
  if let some n := e.rawNatLit? then
    return some (n : ℚ)

  -- Match before reduction
  if let some q ← tryMatchNumeric e then
    return some q

  -- Match after weak-head reduction
  let e ← whnf e
  if let some q ← tryMatchNumeric e then
    return some q

  return none

where
  /-- Try to match a numeric expression directly. -/
  tryMatchNumeric (e : Lean.Expr) : MetaM (Option ℚ) := do
    let fn0 := e.getAppFn
    let args0 := e.getAppArgs
    if args0.size > 0 &&
        (fn0.isConstOf ``Nat.cast || fn0.isConstOf ``NatCast.natCast ||
         fn0.isConstOf ``Int.cast || fn0.isConstOf ``IntCast.intCast ||
         fn0.isConstOf ``Rat.cast || fn0.isConstOf ``RatCast.ratCast) then
      return ← toRat? args0.back!

    match_expr e with
    -- OfNat.ofNat α n inst
    | OfNat.ofNat _ n _ =>
      if let some k := n.rawNatLit? then
        return some (k : ℚ)
      if let some k := n.nat? then
        return some (k : ℚ)
      toRat? n

    -- Nat.cast / NatCast.natCast
    | Nat.cast _ n =>
      toRat? n
    | NatCast.natCast _ n =>
      toRat? n

    -- Int.cast / IntCast.intCast
    | Int.cast _ z =>
      toRat? z
    | IntCast.intCast _ z =>
      toRat? z

    -- Neg.neg α inst x
    | Neg.neg _ _ x =>
      if let some q ← toRat? x then
        return some (-q)
      return none

    -- HSub.hSub a b
    | HSub.hSub _ _ _ _ a b =>
      match ← toRat? a, ← toRat? b with
      | some qa, some qb => return some (qa - qb)
      | _, _ => return none

    -- HDiv.hDiv n d
    | HDiv.hDiv _ _ _ _ n d =>
      match ← toRat? n, ← toRat? d with
      | some qn, some qd =>
        if qd = 0 then
          return none
        return some (qn / qd)
      | _, _ => return none

    -- HMul.hMul a b
    | HMul.hMul _ _ _ _ a b =>
      match ← toRat? a, ← toRat? b with
      | some qa, some qb => return some (qa * qb)
      | _, _ => return none

    -- HAdd.hAdd a b
    | HAdd.hAdd _ _ _ _ a b =>
      match ← toRat? a, ← toRat? b with
      | some qa, some qb => return some (qa + qb)
      | _, _ => return none

    -- Int.ofNat n
    | Int.ofNat n =>
      if let some k := n.rawNatLit? then
        return some (k : ℚ)
      toRat? n

    -- Int.negSucc n = -(n+1)
    | Int.negSucc n =>
      if let some k := n.rawNatLit? then
        return some (-(k + 1 : ℚ))
      return none

    -- Rat.mk' num den ...
    | Rat.mk' num den _ _ =>
      match ← toRat? num, ← toRat? den with
      | some qnum, some qden =>
        if qden = 0 then
          return none
        return some (qnum / qden)
      | _, _ => return none

    -- Rat.cast / RatCast.ratCast
    | Rat.cast _ q =>
      toRat? q
    | RatCast.ratCast _ q =>
      toRat? q

    -- Rat.ofInt z
    | Rat.ofInt z =>
      toRat? z

    -- Inv.inv x = 1/x
    | Inv.inv _ _ x =>
      if let some q ← toRat? x then
        if q = 0 then
          return none
        return some ((1 : ℚ) / q)
      return none

    -- OfScientific.ofScientific mantissa exponentSign decimalExponent
    | OfScientific.ofScientific _ _ mantissa exponentSign decimalExponent =>
      let some m := mantissa.rawNatLit?
        | return none
      let some exp := decimalExponent.rawNatLit?
        | return none
      let isNegExp := exponentSign.constName? == some ``Bool.true
      let base10 : ℚ := (10 : ℚ) ^ exp
      if isNegExp then
        return some ((m : ℚ) / base10)
      return some ((m : ℚ) * base10)

    | _ =>
      let fn := e.getAppFn
      let args := e.getAppArgs
      let fnHead := fn.getAppFn
      let allArgs := fn.getAppArgs ++ args
      if allArgs.size > 0 &&
          (fnHead.isConstOf ``Nat.cast || fnHead.isConstOf ``NatCast.natCast ||
           fnHead.isConstOf ``Int.cast || fnHead.isConstOf ``IntCast.intCast ||
           fnHead.isConstOf ``Rat.cast || fnHead.isConstOf ``RatCast.ratCast) then
        return ← toRat? allArgs.back!
      let fnStr := toString (← ppExpr fn)
      if allArgs.size > 0 &&
          (fnStr.endsWith "instNatCast.1" || fnStr.endsWith "instIntCast.1" ||
           fnStr.endsWith "instRatCast.1") then
        return ← toRat? allArgs.back!
      -- Handle cast wrappers. We accept only cast-related projections/constants.
      -- This avoids accidentally classifying non-numeral projections
      -- (e.g. `x ^ (1/3)` reducing to a projection-headed term) as constants.
      let cast? ←
        match fnHead with
        | .proj s _ _ =>
          let sName := toString s
          if allArgs.size > 0 &&
              (sName.endsWith "NatCast" || sName.endsWith "IntCast" ||
               sName.endsWith "RatCast" || sName.endsWith "instNatCast" ||
               sName.endsWith "instIntCast" || sName.endsWith "instRatCast") then
            toRat? allArgs.back!
          else
            return none
        | .const n _ =>
          let s := toString n
          if allArgs.size > 0 &&
              (s.endsWith "instNatCast.1" || s.endsWith "instIntCast.1" ||
               s.endsWith "instRatCast.1") then
            toRat? allArgs.back!
          else
            return none
        | _ => return none
      if let some q := cast? then
        return some q

      -- Last resort: evaluate closed rational expressions directly.
      if e.hasFVar || e.hasMVar then
        return none
      try
        let q ← unsafe evalExpr ℚ (mkConst ``Rat) e
        return some q
      catch _ =>
        return none

/-- Attempt to parse a Lean expression as an integer constant. -/
def toInt? (e : Lean.Expr) : MetaM (Option Int) := do
  let some q ← toRat? e | return none
  if q.den = 1 then
    return some q.num
  return none

/-- Attempt to parse a Lean expression as a natural-number constant. -/
def toNat? (e : Lean.Expr) : MetaM (Option Nat) := do
  let some z ← toInt? e | return none
  if 0 ≤ z then
    return some z.toNat
  return none

/-- Alias for callers that are extracting rationals from real-valued literals. -/
partial def toRealRat? (e : Lean.Expr) : MetaM (Option ℚ) :=
  toRat? e

end LeanCert.Meta.Numeral

namespace LeanCert.Meta

/-- Compatibility alias for the canonical numeric extractor. -/
abbrev toRat? : Lean.Expr → MetaM (Option ℚ) :=
  LeanCert.Meta.Numeral.toRat?

/-- Compatibility alias for the canonical natural-number extractor. -/
abbrev toNat? : Lean.Expr → MetaM (Option Nat) :=
  LeanCert.Meta.Numeral.toNat?

/-- Compatibility alias for the canonical integer extractor. -/
abbrev toInt? : Lean.Expr → MetaM (Option Int) :=
  LeanCert.Meta.Numeral.toInt?

end LeanCert.Meta
