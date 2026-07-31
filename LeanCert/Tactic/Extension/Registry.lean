/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Tactic.Extension.Protocol
import Lean.Compiler.IR.CompilerM
import Lean.Elab.Term

/-!
# Persistent registry for downstream enclosure rules

`@[leancert_enclosure candidate := c]` registers a theorem with the exact shape

```lean
theorem rule
    {request : UnaryEnclosureRequest} {x : ℝ} {output : IntervalRat}
    (hx : x ∈ request.input)
    (hcheck : checker request output = true) :
    f x ∈ output
```

The attribute validates the candidate, checker, function, and theorem types before
adding serializable declaration metadata to a persistent environment extension.
-/

open Lean Meta Elab

namespace LeanCert.Tactic.Extension

open LeanCert.Core

/-- Attribute syntax for registering a unary enclosure theorem and its candidate generator. -/
syntax (name := leancertEnclosureAttr) "leancert_enclosure" ppSpace "candidate" " := " ident
  ("," ppSpace "priority" " := " num)? : attr

private def insertRule (rules : Array UnaryEnclosureRule) (rule : UnaryEnclosureRule) :
    Array UnaryEnclosureRule :=
  rules.push rule

/-- Persistent registry of downstream unary enclosure rules. -/
initialize unaryEnclosureRuleExt :
    SimplePersistentEnvExtension UnaryEnclosureRule (Array UnaryEnclosureRule) ←
  registerSimplePersistentEnvExtension {
    name := `unaryEnclosureRuleExt
    addEntryFn := insertRule
    addImportedFn := fun imported => imported.foldl (init := #[]) fun acc rules => acc ++ rules
  }

private def ruleLt (a b : UnaryEnclosureRule) : Bool :=
  a.rulePriority > b.rulePriority ||
    (a.rulePriority == b.rulePriority && a.theoremName.toString < b.theoremName.toString)

/-- All registered unary enclosure rules, sorted deterministically. -/
def getAllUnaryEnclosureRules (env : Environment) : Array UnaryEnclosureRule :=
  (unaryEnclosureRuleExt.getState env).qsort ruleLt

/-- Registered unary enclosure rules for a particular function head. -/
def getUnaryEnclosureRules (env : Environment) (functionName : Name) :
    Array UnaryEnclosureRule :=
  (getAllUnaryEnclosureRules env).filter fun rule => rule.functionName == functionName

private def ensureDefEq (actual expected : Expr) (message : MessageData) : MetaM Unit := do
  unless ← isDefEq actual expected do
    throwError message

private def explicitMembership? (type : Expr) : Option (Expr × Expr) := do
  guard <| type.getAppFn.constName? == some ``Membership.mem
  let args := type.getAppArgs
  guard <| 2 ≤ args.size
  return (args[args.size - 1]!, args[args.size - 2]!)

private def explicitEq? (type : Expr) : Option (Expr × Expr) := do
  guard <| type.getAppFn.constName? == some ``Eq
  let args := type.getAppArgs
  guard <| 2 ≤ args.size
  return (args[args.size - 2]!, args[args.size - 1]!)

private def validateUnaryRule (theoremName candidateName : Name) (rulePriority : Nat) :
    MetaM UnaryEnclosureRule := do
  let candidateInfo ← getConstInfo candidateName
  ensureDefEq candidateInfo.type (mkConst ``UnaryEnclosureCandidate)
    m!"invalid @[leancert_enclosure] candidate `{candidateName}`: expected type \
      `UnaryEnclosureCandidate`, found{indentExpr candidateInfo.type}"

  let theoremInfo ← getConstInfo theoremName
  unless theoremInfo matches .thmInfo _ do
    throwError "invalid @[leancert_enclosure] declaration `{theoremName}`: soundness boundary must \
      be a proved theorem, not an axiom or definition"
  forallTelescopeReducing theoremInfo.type fun xs conclusion => do
    unless xs.size == 5 do
      throwError "invalid @[leancert_enclosure] theorem `{theoremName}`: expected exactly \
        three data binders and two hypotheses, but found {xs.size} binders"

    let request := xs[0]!
    let x := xs[1]!
    let output := xs[2]!
    let hx := xs[3]!
    let hcheck := xs[4]!

    ensureDefEq (← inferType request) (mkConst ``UnaryEnclosureRequest)
      m!"invalid @[leancert_enclosure] theorem `{theoremName}`: first binder must have type \
        `UnaryEnclosureRequest`"
    ensureDefEq (← inferType x) (mkConst ``Real)
      m!"invalid @[leancert_enclosure] theorem `{theoremName}`: second binder must have type `ℝ`"
    ensureDefEq (← inferType output) (mkConst ``IntervalRat)
      m!"invalid @[leancert_enclosure] theorem `{theoremName}`: third binder must have type \
        `IntervalRat`"

    let input ← mkAppM ``UnaryEnclosureRequest.input #[request]
    let some (hxValue, hxInterval) := explicitMembership? (← inferType hx)
      | throwError "invalid @[leancert_enclosure] theorem `{theoremName}`: fourth binder must \
          prove `x ∈ request.input`"
    ensureDefEq hxValue x
      m!"invalid @[leancert_enclosure] theorem `{theoremName}`: input-membership hypothesis \
        must concern the theorem's real argument"
    ensureDefEq hxInterval input
      m!"invalid @[leancert_enclosure] theorem `{theoremName}`: input-membership hypothesis \
        must use `request.input`"

    let some (checkValue, checkExpected) := explicitEq? (← inferType hcheck)
      | throwError "invalid @[leancert_enclosure] theorem `{theoremName}`: fifth binder must \
          prove `checker request output = true`"
    ensureDefEq checkExpected (mkConst ``Bool.true)
      m!"invalid @[leancert_enclosure] theorem `{theoremName}`: checker hypothesis must compare \
        against `true`"
    let checkerFn := checkValue.getAppFn
    let some checkerName := checkerFn.constName?
      | throwError "invalid @[leancert_enclosure] theorem `{theoremName}`: checker must have a \
          declaration head"
    let checkerArgs := checkValue.getAppArgs
    unless checkerArgs.size == 2 do
      throwError "invalid @[leancert_enclosure] theorem `{theoremName}`: checker must be applied \
        exactly to `request` and `output`"
    ensureDefEq checkerArgs[0]! request
      m!"invalid @[leancert_enclosure] theorem `{theoremName}`: checker must use the theorem's \
        request"
    ensureDefEq checkerArgs[1]! output
      m!"invalid @[leancert_enclosure] theorem `{theoremName}`: checker must use the theorem's \
        output interval"
    let checkerInfo ← getConstInfo checkerName
    ensureDefEq checkerInfo.type (mkConst ``UnaryEnclosureChecker)
      m!"invalid @[leancert_enclosure] checker `{checkerName}`: expected type \
        `UnaryEnclosureChecker`, found{indentExpr checkerInfo.type}"

    let some (resultValue, resultInterval) := explicitMembership? conclusion
      | throwError "invalid @[leancert_enclosure] theorem `{theoremName}`: conclusion must have \
          the form `f x ∈ output`"
    ensureDefEq resultInterval output
      m!"invalid @[leancert_enclosure] theorem `{theoremName}`: conclusion must use the theorem's \
        output interval"
    let functionFn := resultValue.getAppFn
    let some functionName := functionFn.constName?
      | throwError "invalid @[leancert_enclosure] theorem `{theoremName}`: enclosed function \
          must have a declaration head"
    let functionArgs := resultValue.getAppArgs
    unless functionArgs.size == 1 do
      throwError "invalid @[leancert_enclosure] theorem `{theoremName}`: enclosed function must \
        be a unary `ℝ → ℝ` declaration"
    ensureDefEq functionArgs[0]! x
      m!"invalid @[leancert_enclosure] theorem `{theoremName}`: conclusion must apply the \
        enclosed function to the theorem's real argument"
    let functionInfo ← getConstInfo functionName
    let expectedFunctionType ← mkArrow (mkConst ``Real) (mkConst ``Real)
    ensureDefEq functionInfo.type expectedFunctionType
      m!"invalid @[leancert_enclosure] function `{functionName}`: expected type `ℝ → ℝ`, \
        found{indentExpr functionInfo.type}"

    return {
      functionName
      candidateName
      checkerName
      theoremName
      rulePriority
    }

initialize registerBuiltinAttribute {
  name := `leancertEnclosureAttr
  descr := "register a checked unary real enclosure rule"
  applicationTime := .afterCompilation
  add := fun theoremName stx kind => do
    unless kind == AttributeKind.global do
      throwError "invalid attribute 'leancert_enclosure': registration must be global"
    let env ← getEnv
    unless (env.getModuleIdxFor? theoremName).isNone do
      throwError "invalid attribute 'leancert_enclosure': declaration is in an imported module"
    if let some sorryDecl := IR.getSorryDep env theoremName then
      throwError "invalid @[leancert_enclosure] theorem `{theoremName}`: soundness theorem depends \
        on sorry declaration `{sorryDecl}`"
    let (candidateStx, rulePriority) ← match stx with
      | `(attr| leancert_enclosure candidate := $candidateStx:ident) =>
          pure (candidateStx, 1000)
      | `(attr| leancert_enclosure candidate := $candidateStx:ident, priority := $priorityStx:num) =>
          pure (candidateStx, priorityStx.getNat)
      | _ => throwUnsupportedSyntax
    let candidateName ← resolveGlobalConstNoOverload candidateStx
    let rule ← MetaM.run' <| validateUnaryRule theoremName candidateName rulePriority
    let rules := getAllUnaryEnclosureRules env
    if rules.any fun existing => existing.theoremName == theoremName then
      throwError "duplicate @[leancert_enclosure] registration for theorem `{theoremName}`"
    setEnv <| unaryEnclosureRuleExt.addEntry env rule
    recordExtraRevUseOfCurrentModule
}

end LeanCert.Tactic.Extension
