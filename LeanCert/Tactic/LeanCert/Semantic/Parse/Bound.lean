/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Core.IntervalRat.Basic
import LeanCert.Tactic.LeanCert.Semantic.Parse.Comparison

/-! # Lightweight quantified interval-bound parsing

This is the shared parser for focused bound tactics and the full `leancert`
router. Keeping it solver-free lets downstream users import a dedicated tactic
without loading unrelated tactic families.
-/

open Lean Meta

namespace LeanCert.Tactic.Semantic

def intervalSyntax? (interval : Lean.Expr) : MetaM (Option IntervalSyntax) := do
  let mkBinary (kind : IntervalKind) : Option IntervalSyntax := do
    let args := interval.getAppArgs
    guard (args.size >= 4)
    some {
      original := interval
      kind
      lo := some args[args.size - 2]!
      hi := some args[args.size - 1]!
    }
  let fn := interval.getAppFn
  if fn.isConstOf ``Set.Icc then return mkBinary .closed
  if fn.isConstOf ``Set.Ioo then return mkBinary .open
  if fn.isConstOf ``Set.Ioc then return mkBinary .leftOpen
  if fn.isConstOf ``Set.Ico then return mkBinary .rightOpen
  if fn.isConstOf ``Set.uIcc then return mkBinary .unorderedClosed
  let type ← inferType interval
  if type.isConstOf ``LeanCert.Core.IntervalRat then
    return some { original := interval, kind := .intervalRat }
  return none

def parseMembershipDomain? (membership boundExpr : Lean.Expr) :
    MetaM (Option IntervalSyntax) := do
  let fn := membership.getAppFn
  let args := membership.getAppArgs
  if fn.isConstOf ``Membership.mem && args.size >= 2 then
    let interval := args[args.size - 2]!
    let element := args[args.size - 1]!
    unless ← isDefEq element boundExpr do return none
    return ← intervalSyntax? interval
  return none

/-- Recognize the implication-style spelling `lo ≤ x ∧ x ≤ hi`. -/
def parseConjunctiveIcc? (assumption x : Lean.Expr) :
    MetaM (Option IntervalSyntax) := do
  unless assumption.isAppOfArity ``And 2 do return none
  let conjuncts := assumption.getAppArgs
  let some first := parseRawComparison? conjuncts[0]! | return none
  let some second := parseRawComparison? conjuncts[1]! | return none
  if first.comparison != .le || second.comparison != .le then return none
  let findBounds (lower upper : RawComparison) : MetaM (Option IntervalSyntax) := do
    unless ← isDefEq lower.rhs x do return none
    unless ← isDefEq upper.lhs x do return none
    if lower.lhs.containsFVar x.fvarId! || upper.rhs.containsFVar x.fvarId! then
      return none
    let interval ← mkAppM ``Set.Icc #[lower.lhs, upper.rhs]
    return some {
      original := interval
      kind := .closed
      lo := some lower.lhs
      hi := some upper.rhs
    }
  if let some domain ← findBounds first second then return some domain
  findBounds second first

/-- Parse all quantified interval variables and the final comparison in one
scope-preserving traversal. -/
partial def parseQuantifiedComparison?
    (original current : Lean.Expr)
    (boundVars : Array BoundVariable := #[])
    (fvars : Array Lean.Expr := #[]) : MetaM (Option BoundSpec) := do
  match current with
  | .forallE name type body _ =>
      withLocalDeclD name type fun x => do
        let instantiated ← whnf (body.instantiate1 x)
        let .forallE _ membership conclusion _ := instantiated | return none
        let domain? ←
          match ← parseMembershipDomain? membership x with
          | some domain => pure (some domain)
          | none => parseConjunctiveIcc? membership x
        let some domain := domain? | return none
        withLocalDeclD `hmem membership fun hypothesis => do
          parseQuantifiedComparison? original (conclusion.instantiate1 hypothesis)
            (boundVars.push {
              userName := name
              type
              binderId := some x.fvarId!
              domain
            })
            (fvars.push x)
  | _ =>
      if boundVars.isEmpty then return none
      let some comparison := parseRawComparison? current | return none
      let lhsUses := fvars.any fun x => comparison.lhs.containsFVar x.fvarId!
      let rhsUses := fvars.any fun x => comparison.rhs.containsFVar x.fvarId!
      if !lhsUses && !rhsUses then return none
      let normalizedDifference := lhsUses && rhsUses &&
        (comparison.comparison == .le || comparison.comparison == .lt)
      let (lhsBody, rhsBody) ←
        if normalizedDifference then
          let difference ← mkAppM ``HSub.hSub #[comparison.lhs, comparison.rhs]
          let differenceType ← inferType difference
          let zero ← mkAppOptM ``OfNat.ofNat
            #[some differenceType, some (mkRawNatLit 0), none]
          pure (difference, zero)
        else
          pure (comparison.lhs, comparison.rhs)
      let lhs ← mkLambdaFVars fvars lhsBody
      let rhs ← mkLambdaFVars fvars rhsBody
      return some {
        original
        boundVars
        comparison := comparison.comparison
        lhs
        rhs
        normalizedDifference
      }

/-- Parse a quantified `≤`/`<` interval-bound goal. -/
def parseBound? (goal : Lean.Expr) : MetaM (Option BoundSpec) := do
  let some spec ← parseQuantifiedComparison? goal goal | return none
  if spec.comparison == .le || spec.comparison == .lt then
    return some spec
  return none

end LeanCert.Tactic.Semantic
