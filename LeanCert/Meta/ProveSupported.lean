/-
Copyright (c) 2024 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import Lean
import LeanCert.Meta.ToExpr
import LeanCert.Engine.IntervalEval
import LeanCert.Engine.AD

/-!
# Automatic Support Proof Generation

This module provides metaprogramming infrastructure to automatically generate
`ExprSupportedCore` proof terms for reified LeanCert expressions.

Given a reified AST `e : LeanCert.Core.Expr`, we can construct a proof that
`ExprSupportedCore e` by recursively matching on the AST structure.

## Main definitions

* `LeanCert.Meta.mkSupportedCoreProof` - Generate `ExprSupportedCore` proofs
* `#check_supported` - Debug command to test proof generation

## Usage

```lean
#check_supported (fun x => x * x + 1)
-- Output: Generated proof type: ExprSupportedCore (Expr.add (Expr.mul (Expr.var 0) (Expr.var 0)) (Expr.const 1))
```

## Design notes

Unlike Phase 1 where we matched on Lean's math operations (HAdd.hAdd, etc.),
here we match on our own AST constructors (LeanCert.Core.Expr.add, etc.).
-/

open Lean Meta Elab Command Term

namespace LeanCert.Meta

/-! ## Shared AST Proof Helpers -/

private structure UnarySupportCtor where
  exprCtor : Name
  proofCtor : Name

private structure BinarySupportCtor where
  exprCtor : Name
  proofCtor : Name

private def lookupUnarySupportCtor (fn : Lean.Expr) (table : List UnarySupportCtor) :
    Option Name :=
  table.findSome? fun entry =>
    if fn.isConstOf entry.exprCtor then some entry.proofCtor else none

private def lookupBinarySupportCtor (fn : Lean.Expr) (table : List BinarySupportCtor) :
    Option Name :=
  table.findSome? fun entry =>
    if fn.isConstOf entry.exprCtor then some entry.proofCtor else none

private def tryUnarySupportProof
    (rec : Lean.Expr → MetaM Lean.Expr)
    (fn : Lean.Expr) (args : Array Lean.Expr) (table : List UnarySupportCtor) :
    MetaM (Option Lean.Expr) := do
  let some proofCtor := lookupUnarySupportCtor fn table | return none
  if args.size != 1 then
    throwError "Malformed unary LeanCert expression: expected one argument"
  let e := args[0]!
  let h ← rec e
  return some (← mkAppM proofCtor #[h])

private def tryBinarySupportProof
    (rec : Lean.Expr → MetaM Lean.Expr)
    (fn : Lean.Expr) (args : Array Lean.Expr) (table : List BinarySupportCtor) :
    MetaM (Option Lean.Expr) := do
  let some proofCtor := lookupBinarySupportCtor fn table | return none
  if args.size != 2 then
    throwError "Malformed binary LeanCert expression: expected two arguments"
  let e₁ := args[0]!
  let e₂ := args[1]!
  let h₁ ← rec e₁
  let h₂ ← rec e₂
  return some (← mkAppM proofCtor #[h₁, h₂])

/-! ## UsesOnlyVar0 Proof Generation

Generate proof terms of type `UsesOnlyVar0 e` by recursively matching
on the structure of `e : LeanCert.Core.Expr`.
-/

/-- Generate a proof of `UsesOnlyVar0 e_ast` by matching on the AST structure.

    This function inspects the head constant of the AST expression and
    recursively builds the appropriate proof constructor.

    Supported: all `Expr` constructors, provided every variable is `var 0`.
    Not supported: `var n` for `n ≠ 0`. -/
partial def mkUsesOnlyVar0Proof (e_ast : Lean.Expr) : MetaM Lean.Expr := do
  -- Get the head constant and arguments
  let fn := e_ast.getAppFn
  let args := e_ast.getAppArgs

  -- Match on AST constructors
  if fn.isConstOf ``LeanCert.Core.Expr.const then
    -- Expr.const q => UsesOnlyVar0.const q
    let q := args[0]!
    mkAppM ``LeanCert.Engine.UsesOnlyVar0.const #[q]

  else if fn.isConstOf ``LeanCert.Core.Expr.var then
    -- Expr.var 0 => UsesOnlyVar0.var0
    -- Check that it's var 0
    let idx := args[0]!
    let idxVal ← whnf idx
    -- Check if it's a raw nat literal (OfNat.ofNat Nat 0 ...)
    let isZero ← isDefEq idxVal (mkRawNatLit 0)
    if isZero then
      pure <| Lean.mkConst ``LeanCert.Engine.UsesOnlyVar0.var0
    else
      throwError "Cannot generate UsesOnlyVar0 proof for: {e_ast}\n\
                  Expression uses a variable other than var 0."

  else if fn.isConstOf ``LeanCert.Core.Expr.add then
    -- Expr.add e₁ e₂ => UsesOnlyVar0.add e₁ e₂ h₁ h₂
    let e₁ := args[0]!
    let e₂ := args[1]!
    let h₁ ← mkUsesOnlyVar0Proof e₁
    let h₂ ← mkUsesOnlyVar0Proof e₂
    mkAppM ``LeanCert.Engine.UsesOnlyVar0.add #[e₁, e₂, h₁, h₂]

  else if fn.isConstOf ``LeanCert.Core.Expr.mul then
    -- Expr.mul e₁ e₂ => UsesOnlyVar0.mul e₁ e₂ h₁ h₂
    let e₁ := args[0]!
    let e₂ := args[1]!
    let h₁ ← mkUsesOnlyVar0Proof e₁
    let h₂ ← mkUsesOnlyVar0Proof e₂
    mkAppM ``LeanCert.Engine.UsesOnlyVar0.mul #[e₁, e₂, h₁, h₂]

  else if fn.isConstOf ``LeanCert.Core.Expr.neg then
    -- Expr.neg e => UsesOnlyVar0.neg e h
    let e := args[0]!
    let h ← mkUsesOnlyVar0Proof e
    mkAppM ``LeanCert.Engine.UsesOnlyVar0.neg #[e, h]

  else if fn.isConstOf ``LeanCert.Core.Expr.sin then
    -- Expr.sin e => UsesOnlyVar0.sin e h
    let e := args[0]!
    let h ← mkUsesOnlyVar0Proof e
    mkAppM ``LeanCert.Engine.UsesOnlyVar0.sin #[e, h]

  else if fn.isConstOf ``LeanCert.Core.Expr.cos then
    -- Expr.cos e => UsesOnlyVar0.cos e h
    let e := args[0]!
    let h ← mkUsesOnlyVar0Proof e
    mkAppM ``LeanCert.Engine.UsesOnlyVar0.cos #[e, h]

  else if fn.isConstOf ``LeanCert.Core.Expr.exp then
    -- Expr.exp e => UsesOnlyVar0.exp e h
    let e := args[0]!
    let h ← mkUsesOnlyVar0Proof e
    mkAppM ``LeanCert.Engine.UsesOnlyVar0.exp #[e, h]

  else if fn.isConstOf ``LeanCert.Core.Expr.atan then
    -- Expr.atan e => UsesOnlyVar0.atan e h
    let e := args[0]!
    let h ← mkUsesOnlyVar0Proof e
    mkAppM ``LeanCert.Engine.UsesOnlyVar0.atan #[e, h]

  else if fn.isConstOf ``LeanCert.Core.Expr.arsinh then
    -- Expr.arsinh e => UsesOnlyVar0.arsinh e h
    let e := args[0]!
    let h ← mkUsesOnlyVar0Proof e
    mkAppM ``LeanCert.Engine.UsesOnlyVar0.arsinh #[e, h]

  else if fn.isConstOf ``LeanCert.Core.Expr.inv then
    let e := args[0]!
    let h ← mkUsesOnlyVar0Proof e
    mkAppM ``LeanCert.Engine.UsesOnlyVar0.inv #[e, h]

  else if fn.isConstOf ``LeanCert.Core.Expr.log then
    let e := args[0]!
    let h ← mkUsesOnlyVar0Proof e
    mkAppM ``LeanCert.Engine.UsesOnlyVar0.log #[e, h]

  else if fn.isConstOf ``LeanCert.Core.Expr.atanh then
    let e := args[0]!
    let h ← mkUsesOnlyVar0Proof e
    mkAppM ``LeanCert.Engine.UsesOnlyVar0.atanh #[e, h]

  else if fn.isConstOf ``LeanCert.Core.Expr.sinc then
    let e := args[0]!
    let h ← mkUsesOnlyVar0Proof e
    mkAppM ``LeanCert.Engine.UsesOnlyVar0.sinc #[e, h]

  else if fn.isConstOf ``LeanCert.Core.Expr.erf then
    let e := args[0]!
    let h ← mkUsesOnlyVar0Proof e
    mkAppM ``LeanCert.Engine.UsesOnlyVar0.erf #[e, h]

  else if fn.isConstOf ``LeanCert.Core.Expr.sinh then
    let e := args[0]!
    let h ← mkUsesOnlyVar0Proof e
    mkAppM ``LeanCert.Engine.UsesOnlyVar0.sinh #[e, h]

  else if fn.isConstOf ``LeanCert.Core.Expr.cosh then
    let e := args[0]!
    let h ← mkUsesOnlyVar0Proof e
    mkAppM ``LeanCert.Engine.UsesOnlyVar0.cosh #[e, h]

  else if fn.isConstOf ``LeanCert.Core.Expr.tanh then
    let e := args[0]!
    let h ← mkUsesOnlyVar0Proof e
    mkAppM ``LeanCert.Engine.UsesOnlyVar0.tanh #[e, h]

  else if fn.isConstOf ``LeanCert.Core.Expr.sqrt then
    let e := args[0]!
    let h ← mkUsesOnlyVar0Proof e
    mkAppM ``LeanCert.Engine.UsesOnlyVar0.sqrt #[e, h]

  else if fn.isConstOf ``LeanCert.Core.Expr.namedConst then
    let c := args[0]!
    mkAppM ``LeanCert.Engine.UsesOnlyVar0.namedConst #[c]

  else
    throwError "Cannot generate UsesOnlyVar0 proof for: {e_ast}\n\
                UsesOnlyVar0 supports all Expr constructors, but every variable must be var 0."

/-! ## ADSupported Proof Generation

Generate proof terms of type `ADSupported e` by recursively matching
on the structure of `e : LeanCert.Core.Expr`.

Note: ADSupported is a strict subset of ExprSupportedCore.
ADSupported only supports: const, var, add, mul, neg, sin, cos, exp
-/

/-- Generate a proof of `ADSupported e_ast` by matching on the AST structure.

    This function inspects the head constant of the AST expression and
    recursively builds the appropriate proof constructor.

    Supported: const, var, add, mul, neg, sin, cos, exp
    Not supported: log, sqrt, sinh, cosh, tanh, pi, inv, atan, arsinh, atanh -/
partial def mkSupportedProof (e_ast : Lean.Expr) : MetaM Lean.Expr := do
  let fn := e_ast.getAppFn
  let args := e_ast.getAppArgs

  if fn.isConstOf ``LeanCert.Core.Expr.const then
    let q := args[0]!
    mkAppM ``LeanCert.Core.ADSupported.const #[q]

  else if fn.isConstOf ``LeanCert.Core.Expr.var then
    let idx := args[0]!
    mkAppM ``LeanCert.Core.ADSupported.var #[idx]

  else
    if let some h ← tryBinarySupportProof mkSupportedProof fn args
        [ ⟨``LeanCert.Core.Expr.add, ``LeanCert.Core.ADSupported.add⟩
        , ⟨``LeanCert.Core.Expr.mul, ``LeanCert.Core.ADSupported.mul⟩ ] then
      return h
    if let some h ← tryUnarySupportProof mkSupportedProof fn args
        [ ⟨``LeanCert.Core.Expr.neg, ``LeanCert.Core.ADSupported.neg⟩
        , ⟨``LeanCert.Core.Expr.sin, ``LeanCert.Core.ADSupported.sin⟩
        , ⟨``LeanCert.Core.Expr.cos, ``LeanCert.Core.ADSupported.cos⟩
        , ⟨``LeanCert.Core.Expr.exp, ``LeanCert.Core.ADSupported.exp⟩ ] then
      return h
    throwError "Cannot generate ADSupported proof for: {e_ast}\n\
                ADSupported only covers: const, var, add, mul, neg, sin, cos, exp.\n\
                This expression uses unsupported operations (log, sqrt, sinh, cosh, tanh, pi, inv, etc.).\n\
                For unique root finding, the function must be in this restricted set."

/-! ## ExprSupportedCore Proof Generation

Generate proof terms of type `ExprSupportedCore e` by recursively matching
on the structure of `e : LeanCert.Core.Expr`.
-/

/-- Generate a proof of `ExprSupportedCore e_ast` by matching on the AST structure.

    This function inspects the head constant of the AST expression and
    recursively builds the appropriate proof constructor.

    Supported: const, var, add, mul, neg, sin, cos, exp, log, sqrt, sinh,
    cosh, tanh, erf, named constants
    Not supported: inv, atan, arsinh, atanh -/
partial def mkSupportedCoreProof (e_ast : Lean.Expr) : MetaM Lean.Expr := do
  -- Get the head constant and arguments
  let fn := e_ast.getAppFn
  let args := e_ast.getAppArgs

  -- Match on AST constructors
  if fn.isConstOf ``LeanCert.Core.Expr.const then
    -- Expr.const q => ExprSupportedCore.const q
    let q := args[0]!
    mkAppM ``LeanCert.Core.ExprSupportedCore.const #[q]

  else if fn.isConstOf ``LeanCert.Core.Expr.var then
    -- Expr.var idx => ExprSupportedCore.var idx
    let idx := args[0]!
    mkAppM ``LeanCert.Core.ExprSupportedCore.var #[idx]

  else if fn.isConstOf ``LeanCert.Core.Expr.namedConst then
    let c := args[0]!
    mkAppM ``LeanCert.Core.ExprSupportedCore.namedConst #[c]

  else
    if let some h ← tryBinarySupportProof mkSupportedCoreProof fn args
        [ ⟨``LeanCert.Core.Expr.add, ``LeanCert.Core.ExprSupportedCore.add⟩
        , ⟨``LeanCert.Core.Expr.mul, ``LeanCert.Core.ExprSupportedCore.mul⟩ ] then
      return h
    if let some h ← tryUnarySupportProof mkSupportedCoreProof fn args
        [ ⟨``LeanCert.Core.Expr.neg, ``LeanCert.Core.ExprSupportedCore.neg⟩
        , ⟨``LeanCert.Core.Expr.sin, ``LeanCert.Core.ExprSupportedCore.sin⟩
        , ⟨``LeanCert.Core.Expr.cos, ``LeanCert.Core.ExprSupportedCore.cos⟩
        , ⟨``LeanCert.Core.Expr.exp, ``LeanCert.Core.ExprSupportedCore.exp⟩
        , ⟨``LeanCert.Core.Expr.log, ``LeanCert.Core.ExprSupportedCore.log⟩
        , ⟨``LeanCert.Core.Expr.sqrt, ``LeanCert.Core.ExprSupportedCore.sqrt⟩
        , ⟨``LeanCert.Core.Expr.sinh, ``LeanCert.Core.ExprSupportedCore.sinh⟩
        , ⟨``LeanCert.Core.Expr.cosh, ``LeanCert.Core.ExprSupportedCore.cosh⟩
        , ⟨``LeanCert.Core.Expr.tanh, ``LeanCert.Core.ExprSupportedCore.tanh⟩
        , ⟨``LeanCert.Core.Expr.erf, ``LeanCert.Core.ExprSupportedCore.erf⟩ ] then
      return h
    throwError "Cannot generate ExprSupportedCore proof for: {e_ast}\n\
                This expression contains operations outside the total core evaluator.\n\
                Checked evaluators accept arbitrary expressions without a support proof."

/-! ## Testing Infrastructure -/

/-- Elaborate a term, reify it to a LeanCert expression, and generate
    an ExprSupportedCore proof. Useful for debugging. -/
elab "#check_supported " t:term : command => do
  let (ast, proof, proofType) ← liftTermElabM do
    -- Elaborate and reify the term
    let t ← elabTerm t none
    let t ← instantiateMVars t
    let ast := (← reifyWithReport t).expr
    -- Generate the support proof
    let proof ← mkSupportedCoreProof ast
    let proofType ← inferType proof
    return (ast, proof, proofType)
  logInfo m!"AST: {ast}"
  logInfo m!"Generated proof: {proof}"
  logInfo m!"Proof type: {proofType}"

/-! ## Combined Reification and Support Proof

Convenience functions that combine reification and support proof generation.
-/

/-- Reify a Lean expression and generate both the AST and its ExprSupportedCore proof. -/
def reifyWithSupportCore (e : Lean.Expr) : MetaM (Lean.Expr × Lean.Expr) := do
  let ast := (← reifyWithReport e).expr
  let proof ← mkSupportedCoreProof ast
  return (ast, proof)

end LeanCert.Meta
