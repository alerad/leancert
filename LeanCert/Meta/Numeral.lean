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

namespace LeanCert.Meta

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
      -- Handle cast wrappers. We accept only cast-related projections/constants.
      -- This avoids accidentally classifying non-numeral projections
      -- (e.g. `x ^ (1/3)` reducing to a projection-headed term) as constants.
      match fn with
      | .proj s _ _ =>
        let sName := toString s
        if args.size > 0 &&
            (sName.endsWith "NatCast" || sName.endsWith "IntCast" || sName.endsWith "RatCast") then
          toRat? args.back!
        else
          return none
      | .const n _ =>
        let s := toString n
        if args.size > 0 &&
            (s.endsWith "instNatCast.1" || s.endsWith "instIntCast.1" || s.endsWith "instRatCast.1") then
          toRat? args.back!
        else
          return none
      | _ => return none

end LeanCert.Meta
