/-
Copyright (c) 2024 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import Lean
import LeanCert.Tactic.IntervalAuto.Types
import LeanCert.Tactic.IntervalAuto.Extract
import LeanCert.Meta.ToExpr

/-!
# Goal Parsing for Interval Tactics

This module provides utilities for parsing goal structure to determine
which theorem to apply. Handles:
- Univariate bound goals
- Multivariate bound goals
- Root finding goals
- Point inequalities
-/

open Lean Meta

namespace LeanCert.Tactic.Auto

open LeanCert.Core

/-! ## Univariate Goal Parsing -/

/-- Try to parse a goal as a bound goal -/
def parseBoundGoal (goal : Lean.Expr) : MetaM (Option BoundGoal) := do
  -- Reduce the goal first to handle definitional equality
  let goal ← whnf goal

  -- Check for ∀ x, x ∈ I → ...
  if goal.isForall then
    let .forallE name ty body _ := goal | return none

    -- body should be x ∈ I → comparison
    withLocalDeclD name ty fun x => do
      let body := body.instantiate1 x
      let body ← whnf body
      if body.isForall then
        let .forallE _ memTy innerBody _ := body | return none

        let parseComparison (comparison : Lean.Expr) (interval : IntervalInfo) :
            MetaM (Option BoundGoal) := do
          match_expr comparison with
          | LE.le _ _ lhs rhs =>
            let lhsHasX := lhs.containsFVar x.fvarId!
            let rhsHasX := rhs.containsFVar x.fvarId!
            if lhsHasX && !rhsHasX then
              return some (.forallLe name interval (← mkLambdaFVars #[x] lhs) rhs)
            else if rhsHasX && !lhsHasX then
              return some (.forallGe name interval (← mkLambdaFVars #[x] rhs) lhs)
            else
              return none
          | GE.ge _ _ lhs rhs =>
            let lhsHasX := lhs.containsFVar x.fvarId!
            let rhsHasX := rhs.containsFVar x.fvarId!
            if lhsHasX && !rhsHasX then
              return some (.forallGe name interval (← mkLambdaFVars #[x] lhs) rhs)
            else if rhsHasX && !lhsHasX then
              return some (.forallLe name interval (← mkLambdaFVars #[x] rhs) lhs)
            else
              return none
          | LT.lt _ _ lhs rhs =>
            let lhsHasX := lhs.containsFVar x.fvarId!
            let rhsHasX := rhs.containsFVar x.fvarId!
            if lhsHasX && !rhsHasX then
              return some (.forallLt name interval (← mkLambdaFVars #[x] lhs) rhs)
            else if rhsHasX && !lhsHasX then
              return some (.forallGt name interval (← mkLambdaFVars #[x] rhs) lhs)
            else
              return none
          | GT.gt _ _ lhs rhs =>
            let lhsHasX := lhs.containsFVar x.fvarId!
            let rhsHasX := rhs.containsFVar x.fvarId!
            if lhsHasX && !rhsHasX then
              return some (.forallGt name interval (← mkLambdaFVars #[x] lhs) rhs)
            else if rhsHasX && !lhsHasX then
              return some (.forallLt name interval (← mkLambdaFVars #[x] rhs) lhs)
            else
              return none
          | _ => return none

        -- memTy should be x ∈ I (Membership.mem x I)
        -- Don't reduce with whnf as it will expand the membership definition

        -- Try to extract interval from membership
        let interval? ← extractInterval memTy x
        if let some interval := interval? then
          -- innerBody is the comparison
          return ← withLocalDeclD `hx memTy fun _hx => do
            let comparison := innerBody.instantiate1 _hx
            parseComparison comparison interval
        let parseArrowBounds (memTy innerBody : Lean.Expr) : MetaM (Option BoundGoal) := do
          let memTyWhnf ← withTransparency TransparencyMode.all <| whnf memTy
          let memTyCandidates := if memTyWhnf == memTy then #[memTy] else #[memTy, memTyWhnf]

          let rec findSome (cands : List Lean.Expr) (f : Lean.Expr → MetaM (Option BoundGoal)) :
              MetaM (Option BoundGoal) := do
            match cands with
            | [] => return none
            | cand :: rest =>
              if let some goal ← f cand then
                return some goal
              findSome rest f

          let tryLower (memTyCand : Lean.Expr) : MetaM (Option BoundGoal) := do
            if let some loExpr ← extractLowerBound memTyCand x then
              return ← withLocalDeclD `hx1 memTy fun _hx1 => do
                let innerBodyInst := innerBody.instantiate1 _hx1
                if innerBodyInst.isForall then
                  let .forallE _ memTy2 innerBody2 _ := innerBodyInst | return none
                  let memTy2Whnf ← withTransparency TransparencyMode.all <| whnf memTy2
                  let memTy2Candidates := if memTy2Whnf == memTy2 then #[memTy2] else #[memTy2, memTy2Whnf]
                  let tryUpper (memTy2Cand : Lean.Expr) : MetaM (Option BoundGoal) := do
                    if let some hiExpr ← extractUpperBound memTy2Cand x then
                      if let some interval ← mkIntervalInfoFromBounds loExpr hiExpr then
                        return ← withLocalDeclD `hx2 memTy2 fun _hx2 => do
                          let comparison := innerBody2.instantiate1 _hx2
                          parseComparison comparison interval
                    return none
                  return ← findSome memTy2Candidates.toList tryUpper
                return none
            return none

          let tryUpper (memTyCand : Lean.Expr) : MetaM (Option BoundGoal) := do
            if let some hiExpr ← extractUpperBound memTyCand x then
              return ← withLocalDeclD `hx1 memTy fun _hx1 => do
                let innerBodyInst := innerBody.instantiate1 _hx1
                if innerBodyInst.isForall then
                  let .forallE _ memTy2 innerBody2 _ := innerBodyInst | return none
                  let memTy2Whnf ← withTransparency TransparencyMode.all <| whnf memTy2
                  let memTy2Candidates := if memTy2Whnf == memTy2 then #[memTy2] else #[memTy2, memTy2Whnf]
                  let tryLower (memTy2Cand : Lean.Expr) : MetaM (Option BoundGoal) := do
                    if let some loExpr ← extractLowerBound memTy2Cand x then
                      if let some interval ← mkIntervalInfoFromBounds loExpr hiExpr then
                        return ← withLocalDeclD `hx2 memTy2 fun _hx2 => do
                          let comparison := innerBody2.instantiate1 _hx2
                          parseComparison comparison interval
                    return none
                  return ← findSome memTy2Candidates.toList tryLower
                return none
            return none

          if let some goal ← findSome memTyCandidates.toList tryLower then
            return some goal
          if let some goal ← findSome memTyCandidates.toList tryUpper then
            return some goal
          return none

        if let some arrowGoal ← parseArrowBounds memTy innerBody then
          return some arrowGoal
        return none
      else
        return none
  else
    return none

where
  /-- Extract (lhs, rhs) from an LE.le application. -/
  getLeArgs (e : Lean.Expr) : MetaM (Option (Lean.Expr × Lean.Expr)) := do
    let fn := e.getAppFn
    let args := e.getAppArgs
    if fn.isConstOf ``LE.le && args.size >= 4 then
      return some (args[2]!, args[3]!)
    return none

  /-- Extract lower bound lo from lo ≤ x. -/
  extractLowerBound (e x : Lean.Expr) : MetaM (Option Lean.Expr) := do
    if let some (a, b) ← getLeArgs e then
      if ← isDefEq b x then
        return some a
    return none

  /-- Extract upper bound hi from x ≤ hi. -/
  extractUpperBound (e x : Lean.Expr) : MetaM (Option Lean.Expr) := do
    if let some (a, b) ← getLeArgs e then
      if ← isDefEq a x then
        return some b
    return none

  /-- Extract bounds from conjunction form lo ≤ x ∧ x ≤ hi. -/
  extractBoundsFromAnd (memTy : Lean.Expr) (x : Lean.Expr) :
      MetaM (Option (Lean.Expr × Lean.Expr)) := do
    match_expr memTy with
    | And a b =>
      if let some lo ← extractLowerBound a x then
        if let some hi ← extractUpperBound b x then
          return some (lo, hi)
      if let some lo ← extractLowerBound b x then
        if let some hi ← extractUpperBound a x then
          return some (lo, hi)
      return none
    | _ => return none

  /-- Build IntervalInfo from explicit lo/hi bounds. -/
  mkIntervalInfoFromBounds (loExpr hiExpr : Lean.Expr) : MetaM (Option IntervalInfo) := do
    if let some lo ← extractRatFromReal loExpr then
      if let some hi ← extractRatFromReal hiExpr then
        let loRatExpr := toExpr lo
        let hiRatExpr := toExpr hi
        let leProofTy ← mkAppM ``LE.le #[loRatExpr, hiRatExpr]
        let leProof ← mkDecideProof leProofTy
        let intervalRat ← mkAppM ``IntervalRat.mk #[loRatExpr, hiRatExpr, leProof]
        return some {
          intervalRat := intervalRat
          fromSetIcc := some (lo, hi, loRatExpr, hiRatExpr, leProof, loExpr, hiExpr)
        }
    return none

  /-- Extract the interval from a membership expression -/
  extractInterval (memTy : Lean.Expr) (x : Lean.Expr) : MetaM (Option IntervalInfo) := do
    -- Try direct Membership.mem match
    -- Membership.mem : {α : Type u_1} → {γ : outParam (Type u_2)} → [self : Membership α γ] → γ → α → Prop
    -- Note: The mem function takes (container, element), but notation x ∈ I displays as element ∈ container
    match_expr memTy with
    | Membership.mem _ _ _ interval xExpr =>
      -- Check if xExpr matches x (might be the same or definitionally equal)
      if ← isDefEq xExpr x then
        -- Check if interval is already an IntervalRat
        let intervalTy ← inferType interval
        if intervalTy.isConstOf ``IntervalRat then
          return some { intervalRat := interval }
        -- Check if interval is Set.Icc lo hi
        else if let some info ← tryConvertSetIcc interval then
          return some info
        else
          return some { intervalRat := interval }  -- Return as-is, let type checking fail later if wrong
      else return none
    | _ =>
      -- The memTy might be definitionally expanded - check if it's a conjunction
      if let some (loExpr, hiExpr) ← extractBoundsFromAnd memTy x then
        return ← mkIntervalInfoFromBounds loExpr hiExpr
      let memTyWhnf ← withTransparency TransparencyMode.all <| whnf memTy
      if memTyWhnf == memTy then
        return none
      if let some (loExpr, hiExpr) ← extractBoundsFromAnd memTyWhnf x then
        return ← mkIntervalInfoFromBounds loExpr hiExpr
      return none

  /-- Try to convert a Set.Icc expression to an IntervalRat with full info -/
  tryConvertSetIcc (interval : Lean.Expr) : MetaM (Option IntervalInfo) := do
    let getLeArgs (e : Lean.Expr) : MetaM (Option (Lean.Expr × Lean.Expr)) := do
      let fn := e.getAppFn
      let args := e.getAppArgs
      if fn.isConstOf ``LE.le && args.size >= 4 then
        return some (args[2]!, args[3]!)
      return none

    let extractLowerBound (e x : Lean.Expr) : MetaM (Option Lean.Expr) := do
      if let some (a, b) ← getLeArgs e then
        if ← isDefEq b x then
          return some a
      return none

    let extractUpperBound (e x : Lean.Expr) : MetaM (Option Lean.Expr) := do
      if let some (a, b) ← getLeArgs e then
        if ← isDefEq a x then
          return some b
      return none

    let parseSetIccBounds (e : Lean.Expr) : MetaM (Option (Lean.Expr × Lean.Expr)) := do
      let fn := e.getAppFn
      let args := e.getAppArgs
      -- Set.Icc : {α : Type*} → [Preorder α] → α → α → Set α
      -- So args are: [α, inst, lo, hi]
      if fn.isConstOf ``Set.Icc && args.size >= 4 then
        return some (args[2]!, args[3]!)
      return none

    let parseSetIccLambda (e : Lean.Expr) : MetaM (Option (Lean.Expr × Lean.Expr)) := do
      match e with
      | Lean.Expr.lam name ty body _ =>
        withLocalDeclD name ty fun x => do
          let bodyInst := body.instantiate1 x
          let fn := bodyInst.getAppFn
          let args := bodyInst.getAppArgs
          if fn.isConstOf ``And && args.size >= 2 then
            let left := args[0]!
            let right := args[1]!
            if let some lo ← extractLowerBound left x then
              if let some hi ← extractUpperBound right x then
                return some (lo, hi)
            if let some lo ← extractLowerBound right x then
              if let some hi ← extractUpperBound left x then
                return some (lo, hi)
          return none
      | _ => return none

    let parseBounds (e : Lean.Expr) : MetaM (Option (Lean.Expr × Lean.Expr)) := do
      if let some bounds ← parseSetIccBounds e then
        return some bounds
      parseSetIccLambda e

    let mkIntervalFromBounds (loExpr hiExpr : Lean.Expr) : MetaM (Option IntervalInfo) := do
      if let some lo ← extractRatFromReal loExpr then
        if let some hi ← extractRatFromReal hiExpr then
          let loRatExpr := toExpr lo
          let hiRatExpr := toExpr hi
          let leProofTy ← mkAppM ``LE.le #[loRatExpr, hiRatExpr]
          let leProof ← mkDecideProof leProofTy
          let intervalRat ← mkAppM ``IntervalRat.mk #[loRatExpr, hiRatExpr, leProof]
          return some {
            intervalRat := intervalRat
            fromSetIcc := some (lo, hi, loRatExpr, hiRatExpr, leProof, loExpr, hiExpr)
          }
      return none

    if let some (loExpr, hiExpr) ← parseBounds interval then
      if let some info ← mkIntervalFromBounds loExpr hiExpr then
        return some info
    let intervalWhnf ← withTransparency TransparencyMode.all <| whnf interval
    if intervalWhnf == interval then
      return none
    if let some (loExpr, hiExpr) ← parseBounds intervalWhnf then
      return ← mkIntervalFromBounds loExpr hiExpr
    return none

/-! ## Multivariate Goal Parsing -/

/-- Try to extract interval info from a Set.Icc membership type -/
private def extractIntervalFromSetIcc (memTy : Lean.Expr) (x : Lean.Expr) : MetaM (Option VarIntervalInfo) := do
  -- memTy should be x ∈ Set.Icc lo hi
  match_expr memTy with
  | Membership.mem _ _ _ interval xExpr =>
    if ← isDefEq xExpr x then
      let fn := interval.getAppFn
      let args := interval.getAppArgs
      if fn.isConstOf ``Set.Icc then
        if args.size >= 4 then
          let loExpr := args[2]!
          let hiExpr := args[3]!
          if let some lo ← extractRatFromReal loExpr then
            if let some hi ← extractRatFromReal hiExpr then
              let loRatExpr := toExpr lo
              let hiRatExpr := toExpr hi
              -- Build proof that lo ≤ hi
              let leProofTy ← mkAppM ``LE.le #[loRatExpr, hiRatExpr]
              let leProof ← mkDecideProof leProofTy
              let intervalRat ← mkAppM ``IntervalRat.mk #[loRatExpr, hiRatExpr, leProof]
              let xTy ← inferType x
              let varName ← do
                match x with
                | .fvar fv => pure (← fv.getDecl).userName
                | _ => pure `x
              return some {
                varName := varName
                varType := xTy
                intervalRat := intervalRat
                loExpr := loExpr
                hiExpr := hiExpr
                lo := lo
                hi := hi
              }
      return none
    else return none
  | _ => return none

/-- Try to extract interval info from an IntervalRat membership type -/
private def extractIntervalFromIntervalRat (memTy : Lean.Expr) (x : Lean.Expr) : MetaM (Option VarIntervalInfo) := do
  match_expr memTy with
  | Membership.mem _ _ _ interval xExpr =>
    if ← isDefEq xExpr x then
      let intervalTy ← inferType interval
      if intervalTy.isConstOf ``IntervalRat then
        -- Try to extract lo and hi from the IntervalRat structure
        -- For now, we'll assume the interval is already in the right form
        let xTy ← inferType x
        let varName ← do
          match x with
          | .fvar fv => pure (← fv.getDecl).userName
          | _ => pure `x
        let loExpr ← mkAppM ``IntervalRat.lo #[interval]
        let hiExpr ← mkAppM ``IntervalRat.hi #[interval]
        return some {
          varName := varName
          varType := xTy
          intervalRat := interval
          loExpr := loExpr
          hiExpr := hiExpr
          lo := 0  -- Placeholder - we don't need these for non-Set.Icc
          hi := 1  -- Placeholder
        }
      return none
    else return none
  | _ => return none

/-- Recursively parse a multivariate bound goal, collecting variables and intervals.
    This processes all quantifiers within nested withLocalDeclD scopes so that
    fvars remain valid for mkLambdaFVars. -/
partial def parseMultivariateBoundGoal (goal : Lean.Expr) : MetaM (Option MultivariateBoundGoal) := do
  -- We need to work within the withLocalDeclD scopes, so we'll return a function that
  -- builds the result while fvars are still valid.
  -- First, instantiate any metavariables (e.g., from refine/apply) to get the actual goal.
  let goal ← instantiateMVars goal
  let goal ← if goal.isForall then
    pure goal
  else
    whnf goal
  let extractLowerBound (memTy : Lean.Expr) (x : Lean.Expr) : MetaM (Option Lean.Expr) := do
    match_expr memTy with
    | LE.le _ _ lo xExpr =>
      if ← isDefEq xExpr x then
        return some lo
      return none
    | _ => return none

  let extractUpperBound (memTy : Lean.Expr) (x : Lean.Expr) : MetaM (Option Lean.Expr) := do
    match_expr memTy with
    | LE.le _ _ xExpr hi =>
      if ← isDefEq xExpr x then
        return some hi
      return none
    | _ => return none

  let extractBoundsFromAnd (memTy : Lean.Expr) (x : Lean.Expr) :
      MetaM (Option (Lean.Expr × Lean.Expr)) := do
    match_expr memTy with
    | And a b =>
      if let some lo ← extractLowerBound a x then
        if let some hi ← extractUpperBound b x then
          return some (lo, hi)
      if let some lo ← extractLowerBound b x then
        if let some hi ← extractUpperBound a x then
          return some (lo, hi)
      return none
    | _ => return none

  let mkVarIntervalInfoFromBounds (x : Lean.Expr) (loExpr hiExpr : Lean.Expr) :
      MetaM (Option VarIntervalInfo) := do
    if let some lo ← extractRatFromReal loExpr then
      if let some hi ← extractRatFromReal hiExpr then
        let xTy ← inferType x
        let varName ← do
          match x with
          | .fvar fv => pure (← fv.getDecl).userName
          | _ => pure `x
        let loRatExpr := toExpr lo
        let hiRatExpr := toExpr hi
        let leProofTy ← mkAppM ``LE.le #[loRatExpr, hiRatExpr]
        let leProof ← mkDecideProof leProofTy
        let intervalRat ← mkAppM ``IntervalRat.mk #[loRatExpr, hiRatExpr, leProof]
        return some {
          varName := varName
          varType := xTy
          intervalRat := intervalRat
          loExpr := loExpr
          hiExpr := hiExpr
          lo := lo
          hi := hi
        }
    return none

  let memCandidates (e : Lean.Expr) : MetaM (Array Lean.Expr) := do
    let eWhnf ← withTransparency TransparencyMode.all <| whnf e
    if eWhnf == e then
      return #[e]
    return #[e, eWhnf]

  let rec findSome (cands : List Lean.Expr)
      (f : Lean.Expr → MetaM (Option MultivariateBoundGoal)) :
      MetaM (Option MultivariateBoundGoal) := do
    match cands with
    | [] => return none
    | cand :: rest =>
      if let some goal ← f cand then
        return some goal
      findSome rest f

  let rec collect (e : Lean.Expr) (acc : Array VarIntervalInfo) (fvars : Array Lean.Expr) :
      MetaM (Option MultivariateBoundGoal) := do
    -- Don't use whnf at the top level - it might destroy the forall structure
    if !e.isForall then
      -- We've reached the inner body - process the comparison
      if acc.isEmpty then
        return none  -- No quantified variables found

      -- Match the comparison
      match_expr e with
      | LE.le _ _ lhs rhs =>
        -- Build the function as a lambda over all bound variables
        let lhsHasVars := fvars.any (fun fv => lhs.containsFVar fv.fvarId!)
        let rhsHasVars := fvars.any (fun fv => rhs.containsFVar fv.fvarId!)
        if lhsHasVars && !rhsHasVars then
          let func ← mkLambdaFVars fvars lhs
          return some (.forallLe acc func rhs)
        else if rhsHasVars && !lhsHasVars then
          let func ← mkLambdaFVars fvars rhs
          return some (.forallGe acc func lhs)
        else
          return none
      | GE.ge _ _ lhs rhs =>
        let lhsHasVars := fvars.any (fun fv => lhs.containsFVar fv.fvarId!)
        let rhsHasVars := fvars.any (fun fv => rhs.containsFVar fv.fvarId!)
        if lhsHasVars && !rhsHasVars then
          let func ← mkLambdaFVars fvars lhs
          return some (.forallGe acc func rhs)
        else if rhsHasVars && !lhsHasVars then
          let func ← mkLambdaFVars fvars rhs
          return some (.forallLe acc func lhs)
        else
          return none
      | _ => return none

    let .forallE name ty body _ := e | return none

    -- Introduce the variable (stay in this scope for the rest of parsing)
    withLocalDeclD name ty fun x => do
      let body := body.instantiate1 x

      -- Check if this is a membership quantifier (x ∈ I → ...)
      if body.isForall then
        let .forallE _ memTy innerBody _ := body | return none

        -- Try to extract interval from membership (don't whnf memTy)
        if let some info ← extractIntervalFromSetIcc memTy x then
          withLocalDeclD `_ memTy fun _hx => do
            let nextBody := innerBody.instantiate1 _hx
            collect nextBody (acc.push info) (fvars.push x)
        else if let some info ← extractIntervalFromIntervalRat memTy x then
          withLocalDeclD `_ memTy fun _hx => do
            let nextBody := innerBody.instantiate1 _hx
            collect nextBody (acc.push info) (fvars.push x)
        else
          let memTyCandidates ← memCandidates memTy
          -- Handle conjunction form: (lo ≤ x ∧ x ≤ hi) → ...
          let tryAnd (memTyCand : Lean.Expr) : MetaM (Option MultivariateBoundGoal) := do
            if let some (loExpr, hiExpr) ← extractBoundsFromAnd memTyCand x then
              if let some info ← mkVarIntervalInfoFromBounds x loExpr hiExpr then
                return ← withLocalDeclD `_ memTy fun _hx => do
                  let nextBody := innerBody.instantiate1 _hx
                  collect nextBody (acc.push info) (fvars.push x)
            return none
          if let some result ← findSome memTyCandidates.toList tryAnd then
            return some result
          -- Handle expanded bounds: lo ≤ x → x ≤ hi → ...
          let tryLower (memTyCand : Lean.Expr) : MetaM (Option MultivariateBoundGoal) := do
            if let some loExpr ← extractLowerBound memTyCand x then
              return ← withLocalDeclD `_ memTy fun _hx1 => do
                let innerBodyInst := innerBody.instantiate1 _hx1
                if innerBodyInst.isForall then
                  let .forallE _ memTy2 innerBody2 _ := innerBodyInst | return none
                  let memTy2Candidates ← memCandidates memTy2
                  let tryUpper (memTy2Cand : Lean.Expr) : MetaM (Option MultivariateBoundGoal) := do
                    if let some hiExpr ← extractUpperBound memTy2Cand x then
                      if let some info ← mkVarIntervalInfoFromBounds x loExpr hiExpr then
                        return ← withLocalDeclD `_ memTy2 fun _hx2 => do
                          let nextBody := innerBody2.instantiate1 _hx2
                          collect nextBody (acc.push info) (fvars.push x)
                    return none
                  return ← findSome memTy2Candidates.toList tryUpper
                return none
            return none
          let tryUpper (memTyCand : Lean.Expr) : MetaM (Option MultivariateBoundGoal) := do
            if let some hiExpr ← extractUpperBound memTyCand x then
              return ← withLocalDeclD `_ memTy fun _hx1 => do
                let innerBodyInst := innerBody.instantiate1 _hx1
                if innerBodyInst.isForall then
                  let .forallE _ memTy2 innerBody2 _ := innerBodyInst | return none
                  let memTy2Candidates ← memCandidates memTy2
                  let tryLower (memTy2Cand : Lean.Expr) : MetaM (Option MultivariateBoundGoal) := do
                    if let some loExpr ← extractLowerBound memTy2Cand x then
                      if let some info ← mkVarIntervalInfoFromBounds x loExpr hiExpr then
                        return ← withLocalDeclD `_ memTy2 fun _hx2 => do
                          let nextBody := innerBody2.instantiate1 _hx2
                          collect nextBody (acc.push info) (fvars.push x)
                    return none
                  return ← findSome memTy2Candidates.toList tryLower
                return none
            return none
          if let some result ← findSome memTyCandidates.toList tryLower then
            return some result
          if let some result ← findSome memTyCandidates.toList tryUpper then
            return some result
          -- Not a membership quantifier, treat as the inner body
          if acc.isEmpty then
            return none
          match_expr body with
          | LE.le _ _ lhs rhs =>
            let lhsHasVars := fvars.any (fun fv => lhs.containsFVar fv.fvarId!)
            let rhsHasVars := fvars.any (fun fv => rhs.containsFVar fv.fvarId!)
            if lhsHasVars && !rhsHasVars then
              let func ← mkLambdaFVars fvars lhs
              return some (.forallLe acc func rhs)
            else if rhsHasVars && !lhsHasVars then
              let func ← mkLambdaFVars fvars rhs
              return some (.forallGe acc func lhs)
            else
              return none
          | GE.ge _ _ lhs rhs =>
            let lhsHasVars := fvars.any (fun fv => lhs.containsFVar fv.fvarId!)
            let rhsHasVars := fvars.any (fun fv => rhs.containsFVar fv.fvarId!)
            if lhsHasVars && !rhsHasVars then
              let func ← mkLambdaFVars fvars lhs
              return some (.forallGe acc func rhs)
            else if rhsHasVars && !lhsHasVars then
              let func ← mkLambdaFVars fvars rhs
              return some (.forallLe acc func lhs)
            else
              return none
          | _ => return none
      else
        -- No more foralls - process comparison within current scope
        if acc.isEmpty then
          return none
        match_expr body with
        | LE.le _ _ lhs rhs =>
          let lhsHasVars := fvars.any (fun fv => lhs.containsFVar fv.fvarId!)
          let rhsHasVars := fvars.any (fun fv => rhs.containsFVar fv.fvarId!)
          if lhsHasVars && !rhsHasVars then
            let func ← mkLambdaFVars fvars lhs
            return some (.forallLe acc func rhs)
          else if rhsHasVars && !lhsHasVars then
            let func ← mkLambdaFVars fvars rhs
            return some (.forallGe acc func lhs)
          else
            return none
        | GE.ge _ _ lhs rhs =>
          let lhsHasVars := fvars.any (fun fv => lhs.containsFVar fv.fvarId!)
          let rhsHasVars := fvars.any (fun fv => rhs.containsFVar fv.fvarId!)
          if lhsHasVars && !rhsHasVars then
            let func ← mkLambdaFVars fvars lhs
            return some (.forallGe acc func rhs)
          else if rhsHasVars && !lhsHasVars then
            let func ← mkLambdaFVars fvars rhs
            return some (.forallLe acc func lhs)
          else
            return none
        | _ => return none

  collect goal #[] #[]

/-! ## Point Inequality Parsing -/

/-- Check if a Lean Name ends with a given suffix string -/
private def nameEndsWithStr (n : Lean.Name) (suffix : String) : Bool :=
  match n with
  | .str _ s => s == suffix || s.endsWith ("." ++ suffix)
  | _ => false

/-- Parse a point inequality goal and extract lhs, rhs, and inequality type.
    Returns (lhs, rhs, isStrict, isReversed) where:
    - isStrict: true for < or >, false for ≤ or ≥
    - isReversed: true for ≥ or > (need to flip the comparison) -/
def parsePointIneq (goal : Lean.Expr) : MetaM (Option (Lean.Expr × Lean.Expr × Bool × Bool)) := do
  let goal ← whnf goal
  let fn := goal.getAppFn
  let args := goal.getAppArgs

  if let .const name _ := fn then
    -- Check for LE/le patterns (handles both LE.le and Real.le etc.)
    -- LE.le: args = [type, inst, lhs, rhs] (4 args)
    -- Real.le: args = [lhs, rhs] (2 args)
    if name == ``LE.le && args.size >= 4 then
      return some (args[2]!, args[3]!, false, false)
    if nameEndsWithStr name "le" && args.size >= 2 then
      -- Likely a specialized le like Real.le
      return some (args[args.size - 2]!, args[args.size - 1]!, false, false)
    -- LT.lt patterns
    if name == ``LT.lt && args.size >= 4 then
      return some (args[2]!, args[3]!, true, false)
    if nameEndsWithStr name "lt" && args.size >= 2 then
      return some (args[args.size - 2]!, args[args.size - 1]!, true, false)
    -- GE.ge patterns
    if name == ``GE.ge && args.size >= 4 then
      return some (args[2]!, args[3]!, false, true)
    if nameEndsWithStr name "ge" && args.size >= 2 then
      return some (args[args.size - 2]!, args[args.size - 1]!, false, true)
    -- GT.gt patterns
    if name == ``GT.gt && args.size >= 4 then
      return some (args[2]!, args[3]!, true, true)
    if nameEndsWithStr name "gt" && args.size >= 2 then
      return some (args[args.size - 2]!, args[args.size - 1]!, true, true)
  return none

/-- Try to collect all constant rational values from an expression.
    Returns the list of rational constants found (for building the singleton interval). -/
partial def collectConstants (e : Lean.Expr) : MetaM (List ℚ) := do
  -- Don't use whnf - it expands Real.exp to Complex.exp which we don't want
  -- First try to extract as rational directly
  if let some q ← extractRatFromReal e then
    return [q]

  let fn := e.getAppFn
  let args := e.getAppArgs

  -- For function applications, collect from arguments
  if let .const name _ := fn then
    let nameStr := name.toString
    -- Unary functions: collect from the argument
    -- Check by name suffix since the full name might include module prefix
    if nameStr.endsWith "exp" || nameStr.endsWith "sin" || nameStr.endsWith "cos" ||
       nameStr.endsWith "sqrt" || nameStr.endsWith "log" || nameStr.endsWith "sinh" ||
       nameStr.endsWith "cosh" || nameStr.endsWith "tanh" || nameStr.endsWith "arctan" then
      if args.size > 0 then
        return ← collectConstants args.back!
    -- Negation
    if name == ``Neg.neg && args.size >= 3 then
      return ← collectConstants args[2]!

  -- Binary operations
  if fn.isConstOf ``HAdd.hAdd || fn.isConstOf ``HSub.hSub ||
     fn.isConstOf ``HMul.hMul || fn.isConstOf ``HDiv.hDiv then
    if args.size >= 6 then
      let lhsConsts ← collectConstants args[4]!
      let rhsConsts ← collectConstants args[5]!
      return lhsConsts ++ rhsConsts

  return []

/-! ## Root Finding Goal Parsing -/

/-- Try to parse a goal as a root finding goal -/
def parseRootGoal (goal : Lean.Expr) : MetaM (Option RootGoal) := do
  let goal ← whnf goal

  -- Check for ∀ x, x ∈ I → f x ≠ 0
  if goal.isForall then
    let .forallE name ty body _ := goal | return none

    withLocalDeclD name ty fun x => do
      let body := body.instantiate1 x
      let body ← whnf body
      if body.isForall then
        let .forallE _ memTy innerBody _ := body | return none

        -- Extract interval from membership
        let interval? ← extractInterval memTy x
        let some interval := interval? | return none

        -- innerBody should be f x ≠ 0 (which is f x = 0 → False)
        withLocalDeclD `hx memTy fun _hx => do
          let neqExpr := innerBody.instantiate1 _hx

          -- Try to match Ne (f x) 0 or f x ≠ 0
          match_expr neqExpr with
          | Ne _ lhs _rhs =>
            -- Check if lhs (the function value) depends on x
            let lhsHasX := lhs.containsFVar x.fvarId!
            if lhsHasX then
              return some (.forallNeZero name interval (← mkLambdaFVars #[x] lhs))
            else
              return none
          | _ =>
            -- Also check for Not (Eq ...)
            match_expr neqExpr with
            | Not eqExpr =>
              match_expr eqExpr with
              | Eq _ lhs _rhs =>
                let lhsHasX := lhs.containsFVar x.fvarId!
                if lhsHasX then
                  return some (.forallNeZero name interval (← mkLambdaFVars #[x] lhs))
                else
                  return none
              | _ => return none
            | _ => return none
      else
        return none
  else
    return none

where
  getLeArgs (e : Lean.Expr) : MetaM (Option (Lean.Expr × Lean.Expr)) := do
    let fn := e.getAppFn
    let args := e.getAppArgs
    if fn.isConstOf ``LE.le && args.size >= 4 then
      return some (args[2]!, args[3]!)
    return none

  extractLowerBound (e x : Lean.Expr) : MetaM (Option Lean.Expr) := do
    if let some (a, b) ← getLeArgs e then
      if ← isDefEq b x then
        return some a
    return none

  extractUpperBound (e x : Lean.Expr) : MetaM (Option Lean.Expr) := do
    if let some (a, b) ← getLeArgs e then
      if ← isDefEq a x then
        return some b
    return none

  extractBoundsFromAnd (memTy : Lean.Expr) (x : Lean.Expr) :
      MetaM (Option (Lean.Expr × Lean.Expr)) := do
    match_expr memTy with
    | And a b =>
      if let some lo ← extractLowerBound a x then
        if let some hi ← extractUpperBound b x then
          return some (lo, hi)
      if let some lo ← extractLowerBound b x then
        if let some hi ← extractUpperBound a x then
          return some (lo, hi)
      return none
    | _ => return none

  mkIntervalRatFromBounds (loExpr hiExpr : Lean.Expr) : MetaM (Option Lean.Expr) := do
    if let some lo ← extractRatFromReal loExpr then
      if let some hi ← extractRatFromReal hiExpr then
        let loRatExpr := toExpr lo
        let hiRatExpr := toExpr hi
        let leProofTy ← mkAppM ``LE.le #[loRatExpr, hiRatExpr]
        let leProof ← mkDecideProof leProofTy
        let intervalRat ← mkAppM ``IntervalRat.mk #[loRatExpr, hiRatExpr, leProof]
        return some intervalRat
    return none

  /-- Extract the interval from a membership expression -/
  extractInterval (memTy : Lean.Expr) (x : Lean.Expr) : MetaM (Option Lean.Expr) := do
    match_expr memTy with
    | Membership.mem _ _ _ interval xExpr =>
      if ← isDefEq xExpr x then return some interval else return none
    | _ =>
      if let some (loExpr, hiExpr) ← extractBoundsFromAnd memTy x then
        return ← mkIntervalRatFromBounds loExpr hiExpr
      let memTyWhnf ← withTransparency TransparencyMode.all <| whnf memTy
      if memTyWhnf == memTy then
        return none
      if let some (loExpr, hiExpr) ← extractBoundsFromAnd memTyWhnf x then
        return ← mkIntervalRatFromBounds loExpr hiExpr
      return none

/-! ## Global Optimization Goal Parsing -/

/-- Check if expression is Expr.eval (checking both short and full names) -/
def isExprEval (e : Lean.Expr) : Bool :=
  let fn := e.getAppFn
  fn.isConstOf ``LeanCert.Core.Expr.eval || fn.isConstOf ``Expr.eval

/-- Check if name ends with Expr.eval -/
def isExprEvalName (name : Lean.Name) : Bool :=
  (`Expr.eval).isSuffixOf name

/-- Try to parse an already-intro'd goal as a global optimization bound.
    After intro ρ hρ hzero, the goal should be a comparison: Expr.eval ρ e ≤ c or c ≤ Expr.eval ρ e -/
def parseSimpleBoundGoal (goal : Lean.Expr) : MetaM (Option GlobalBoundGoal) := do
  let goal ← whnf goal
  -- Check if it's an application of LE.le
  let fn := goal.getAppFn
  let args := goal.getAppArgs
  if let .const name _ := fn then
    -- Should be LE.le or a variant
    if name == ``LE.le && args.size ≥ 4 then
      -- args are: [type, inst, lhs, rhs]
      let lhs := args[2]!
      let rhs := args[3]!
      -- Check if lhs is Expr.eval
      let lhsFn := lhs.getAppFn
      if let .const lhsName _ := lhsFn then
        if isExprEvalName lhsName then
          let lhsArgs := lhs.getAppArgs
          if lhsArgs.size ≥ 2 then
            return some (.globalLe (Lean.mkConst ``Unit) lhsArgs[1]! rhs)
      -- Check if rhs is Expr.eval
      let rhsFn := rhs.getAppFn
      if let .const rhsName _ := rhsFn then
        if isExprEvalName rhsName then
          let rhsArgs := rhs.getAppArgs
          if rhsArgs.size ≥ 2 then
            return some (.globalGe (Lean.mkConst ``Unit) rhsArgs[1]! lhs)
  return none

end LeanCert.Tactic.Auto
