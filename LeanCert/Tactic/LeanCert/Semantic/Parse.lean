/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import LeanCert.Meta.Numeral
import LeanCert.Tactic.FinSumBound
import LeanCert.Tactic.LeanCert.Semantic.Goal

/-!
# Parse-Once Semantic Goal Parser

This is the only theorem-shape parser used by the `leancert` front door.
Every successful parse retains the payload required by preparation and solver
selection; there is deliberately no intent-only compatibility fallback.
-/

open Lean Meta

namespace LeanCert.Tactic.Semantic

structure ParseFailure where
  goal : Lean.Expr
  detail : String
  deriving Inhabited

private structure RawComparison where
  comparison : Comparison
  lhs : Lean.Expr
  rhs : Lean.Expr

/-- Read a comparison application without reducing either operand. -/
private def parseRawComparison? (goal : Lean.Expr) : Option RawComparison := do
  let fn := goal.getAppFn
  let args := goal.getAppArgs
  if fn.isConstOf ``Eq && args.size >= 3 then
    return ⟨.eq, args[args.size - 2]!, args[args.size - 1]!⟩
  if fn.isConstOf ``LE.le && args.size >= 4 then
    return ⟨.le, args[args.size - 2]!, args[args.size - 1]!⟩
  if fn.isConstOf ``LT.lt && args.size >= 4 then
    return ⟨.lt, args[args.size - 2]!, args[args.size - 1]!⟩
  if fn.isConstOf ``GE.ge && args.size >= 4 then
    return ⟨.le, args[args.size - 1]!, args[args.size - 2]!⟩
  if fn.isConstOf ``GT.gt && args.size >= 4 then
    return ⟨.lt, args[args.size - 1]!, args[args.size - 2]!⟩
  if fn.isConstOf ``Ne && args.size >= 3 then
    return ⟨.ne, args[args.size - 2]!, args[args.size - 1]!⟩
  none

private def parseIntegralTerm? (e : Lean.Expr) :
    Option (Lean.Expr × Lean.Expr × Lean.Expr) :=
  if e.getAppFn.constName? == some ``intervalIntegral && e.getAppNumArgs >= 4 then
    let args := e.getAppArgs
    some (args[args.size - 4]!, args[args.size - 3]!, args[args.size - 2]!)
  else
    none

private def parseIntegral? (goal : Lean.Expr) : Option IntegralSpec := do
  let comparison ← parseRawComparison? goal
  if let some (integrand, lo, hi) := parseIntegralTerm? comparison.lhs then
    return {
      original := goal
      integral := comparison.lhs
      integrand
      lo
      hi
      comparison := comparison.comparison
      lhs := comparison.lhs
      rhs := comparison.rhs
    }
  if let some (integrand, lo, hi) := parseIntegralTerm? comparison.rhs then
    return {
      original := goal
      integral := comparison.rhs
      integrand
      lo
      hi
      comparison := comparison.comparison
      lhs := comparison.lhs
      rhs := comparison.rhs
    }
  none

private def intervalSyntax? (interval : Lean.Expr) : MetaM (Option IntervalSyntax) := do
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

private def parseMembershipDomain? (membership boundExpr : Lean.Expr) :
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
private def parseConjunctiveIcc? (assumption x : Lean.Expr) :
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
private partial def parseQuantifiedComparison?
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

private def parseBound? (goal : Lean.Expr) : MetaM (Option BoundSpec) := do
  let some spec ← parseQuantifiedComparison? goal goal | return none
  if spec.comparison == .le || spec.comparison == .lt then
    return some spec
  return none

private def isZero (expression : Lean.Expr) : MetaM Bool := do
  return (← LeanCert.Meta.Numeral.toRealRatNormalized? expression) == some 0

private def rootFunction? (lhs rhs xVar : Lean.Expr) :
    MetaM (Option (Lean.Expr × Bool)) := do
  let lhsUses := lhs.containsFVar xVar.fvarId!
  let rhsUses := rhs.containsFVar xVar.fvarId!
  if !lhsUses && !rhsUses then return none
  if lhsUses && (← isZero rhs) then
    return some (← mkLambdaFVars #[xVar] lhs, false)
  if rhsUses && (← isZero lhs) then
    return some (← mkLambdaFVars #[xVar] rhs, true)
  let difference ← mkAppM ``HSub.hSub #[lhs, rhs]
  return some (← mkLambdaFVars #[xVar] difference, false)

private def parseRootPredicate? (predicate xVar : Lean.Expr) :
    MetaM (Option (Lean.Expr × Bool)) := do
  let some comparison := parseRawComparison? predicate | return none
  if comparison.comparison != .eq && comparison.comparison != .ne then
    return none
  rootFunction? comparison.lhs comparison.rhs xVar

private def parseDomainAndPredicate? (conjunction x : Lean.Expr) :
    MetaM (Option (IntervalSyntax × Lean.Expr)) := do
  unless conjunction.isAppOfArity ``And 2 do return none
  let conjuncts := conjunction.getAppArgs
  if let some domain ← parseMembershipDomain? conjuncts[0]! x then
    return some (domain, conjuncts[1]!)
  if let some domain ← parseMembershipDomain? conjuncts[1]! x then
    return some (domain, conjuncts[0]!)
  return none

private def parseRootExists? (goal : Lean.Expr) : MetaM (Option RootSpec) := do
  match_expr goal with
  | Exists _ body =>
      let .lam name type inner _ := body | return none
      withLocalDeclD name type fun x => do
        let instantiated ← whnf (inner.instantiate1 x)
        match ← parseDomainAndPredicate? instantiated x with
        | some (domain, equality) =>
            let some (function, equationReversed) ← parseRootPredicate? equality x | return none
            return some {
              original := goal
              kind := .exists
              boundVar := { userName := name, type, binderId := some x.fvarId!, domain }
              function
              equationReversed
            }
        | none => return none
  | _ => return none

private def parseUniqueRoot? (goal : Lean.Expr) : MetaM (Option RootSpec) := do
  match_expr goal with
  | ExistsUnique _ body =>
      let .lam name type inner _ := body | return none
      withLocalDeclD name type fun x => do
        let instantiated ← whnf (inner.instantiate1 x)
        match ← parseDomainAndPredicate? instantiated x with
        | some (domain, equality) =>
            let some (function, equationReversed) ← parseRootPredicate? equality x | return none
            return some {
              original := goal
              kind := .unique
              boundVar := { userName := name, type, binderId := some x.fvarId!, domain }
              function
              equationReversed
            }
        | none => return none
  | _ => return none

private def parseNoRoot? (goal : Lean.Expr) : MetaM (Option RootSpec) := do
  let some spec ← parseQuantifiedComparison? goal goal | return none
  if spec.comparison != .ne || spec.boundVars.size != 1 then return none
  let variableType := spec.boundVars[0]!.type
  withLocalDeclD `x variableType fun x => do
    let lhs := (mkApp spec.lhs x).headBeta
    let rhs := (mkApp spec.rhs x).headBeta
    let some (function, equationReversed) ← rootFunction? lhs rhs x | return none
    return some {
      original := goal
      kind := .excluded
      boundVar := spec.boundVars[0]!
      function
      equationReversed
    }

private def parseExtremum? (goal : Lean.Expr) : MetaM (Option ExtremumSpec) := do
  match_expr goal with
  | Exists _ body =>
      let .lam name type inner _ := body | return none
      withLocalDeclD name type fun x => do
        let instantiated ← whnf (inner.instantiate1 x)
        match ← parseDomainAndPredicate? instantiated x with
        | some (domain, remainder) =>
            let .forallE yName yType yBody _ := remainder | return none
            withLocalDeclD yName yType fun y => do
              let yInstantiated ← whnf (yBody.instantiate1 y)
              let .forallE _ yMembership comparisonBody _ := yInstantiated | return none
              let some yDomain ← parseMembershipDomain? yMembership y | return none
              unless ← isDefEq domain.original yDomain.original do return none
              withLocalDeclD `hy yMembership fun hy => do
                let some comparison :=
                  parseRawComparison? (comparisonBody.instantiate1 hy) | return none
                if comparison.comparison != .le then return none
                let lhsUsesX := comparison.lhs.containsFVar x.fvarId!
                let lhsUsesY := comparison.lhs.containsFVar y.fvarId!
                let rhsUsesX := comparison.rhs.containsFVar x.fvarId!
                let rhsUsesY := comparison.rhs.containsFVar y.fvarId!
                let kind ←
                  if lhsUsesX && !lhsUsesY && rhsUsesY && !rhsUsesX then
                    pure ExtremumKind.minimum
                  else if lhsUsesY && !lhsUsesX && rhsUsesX && !rhsUsesY then
                    pure ExtremumKind.maximum
                  else
                    return none
                let functionBody :=
                  if kind == .minimum then comparison.rhs else comparison.lhs
                let candidateValue :=
                  if kind == .minimum then comparison.lhs else comparison.rhs
                let function ← mkLambdaFVars #[y] functionBody
                unless ← isDefEq candidateValue (mkApp function x) do return none
                return some {
                  original := goal
                  kind
                  boundVar := { userName := name, type, binderId := some x.fvarId!, domain }
                  function
                  existenceOnly := true
                }
        | none => return none
  | _ => return none

private def parseDiscovery? (goal : Lean.Expr) : MetaM (Option DiscoverySpec) := do
  match_expr goal with
  | Exists witnessType body =>
      let .lam witnessName _ inner _ := body | return none
      withLocalDeclD witnessName witnessType fun witness => do
        let innerTheorem := inner.instantiate1 witness
        let some spec ← parseQuantifiedComparison? innerTheorem innerTheorem | return none
        if spec.comparison != .le then return none
        let lhsHasWitness := spec.lhs.containsFVar witness.fvarId!
        let rhsHasWitness := spec.rhs.containsFVar witness.fvarId!
        if lhsHasWitness == rhsHasWitness then return none
        let kind := if rhsHasWitness then ExtremumKind.maximum else ExtremumKind.minimum
        let function := if rhsHasWitness then spec.lhs else spec.rhs
        return some {
          original := goal
          kind
          witnessType
          boundVars := spec.boundVars
          function
        }
  | _ => return none

private partial def containsFinsetSum (e : Lean.Expr) : Bool :=
  if e.getAppFn.isConstOf ``Finset.sum then true
  else e.getAppArgs.any containsFinsetSum

private def parseFiniteSum? (goal : Lean.Expr) : Option FiniteSumSpec := do
  let comparison ← parseRawComparison? goal
  let lhsSum := containsFinsetSum comparison.lhs
  let rhsSum := containsFinsetSum comparison.rhs
  if lhsSum == rhsSum then none
  else
    some {
      original := goal
      sum := if lhsSum then comparison.lhs else comparison.rhs
      comparison := comparison.comparison
      lhs := comparison.lhs
      rhs := comparison.rhs
    }

private def parseCertificateCheck? (goal : Lean.Expr) : Option Lean.Expr := do
  let comparison ← parseRawComparison? goal
  guard (comparison.comparison == .eq)
  let checker ←
    if comparison.rhs.isConstOf ``Bool.true then some comparison.lhs
    else if comparison.lhs.isConstOf ``Bool.true then some comparison.rhs
    else none
  guard (!checker.hasFVar)
  let name ← checker.getAppFn.constName?
  guard (name.getRoot == `LeanCert)
  some checker

private def parsePoint? (goal : Lean.Expr) : Option PointSpec := do
  if goal.isForall then none
  else
    let comparison ← parseRawComparison? goal
    some {
      original := goal
      comparison := comparison.comparison
      lhs := comparison.lhs
      rhs := comparison.rhs
    }

private partial def splitConjunction? (goal : Lean.Expr) :
    Option (Lean.Expr × Lean.Expr) :=
  if goal.isAppOfArity ``And 2 then
    let args := goal.getAppArgs
    some (args[0]!, args[1]!)
  else
    match goal with
    | .forallE name type body binderInfo =>
        match splitConjunction? body with
        | some (lhs, rhs) =>
            some (.forallE name type lhs binderInfo, .forallE name type rhs binderInfo)
        | none => none
    | _ => none

/-- Parse one theorem into a semantic goal. -/
partial def parseGoal (goal : Lean.Expr) : MetaM (Except ParseFailure SemanticGoal) := do
  if let some (lhsGoal, rhsGoal) := splitConjunction? goal then
    let left ← parseGoal lhsGoal
    let right ← parseGoal rhsGoal
    match left, right with
    | .ok lhs, .ok rhs => return .ok (.allOf goal #[lhs, rhs])
    | .error failure, _ | _, .error failure => return .error failure
  if goal.isAppOfArity ``Or 2 then
    return .error {
      goal
      detail := "disjunction routing is intentionally unsupported until branch proof \
        composition is implemented"
    }
  if let some integral := parseIntegral? goal then return .ok (.integral integral)
  if let some root ← parseUniqueRoot? goal then return .ok (.root root)
  if let some root ← parseRootExists? goal then return .ok (.root root)
  if let some root ← parseNoRoot? goal then return .ok (.root root)
  if let some extremum ← parseExtremum? goal then return .ok (.extremum extremum)
  if let some discovery ← parseDiscovery? goal then return .ok (.discovery discovery)
  if let some finiteSum := parseFiniteSum? goal then return .ok (.finiteSum finiteSum)
  if let some checker := parseCertificateCheck? goal then
    return .ok (.certificateCheck goal checker)
  if let some bound ← parseBound? goal then return .ok (.bound bound)
  if let some point := parsePoint? goal then return .ok (.point point)
  return .error { goal, detail := "unsupported mathematical theorem shape" }

end LeanCert.Tactic.Semantic
