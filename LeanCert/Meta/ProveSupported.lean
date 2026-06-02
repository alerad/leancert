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
* `LeanCert.Meta.mkSupportedWithInvProof` - Generate `ExprSupportedWithInv` proofs
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
  if args.size < 1 then
    throwError "Malformed unary LeanCert expression: expected one argument"
  let e := args[0]!
  let h ← rec e
  return some (← mkAppM proofCtor #[h])

private def tryBinarySupportProof
    (rec : Lean.Expr → MetaM Lean.Expr)
    (fn : Lean.Expr) (args : Array Lean.Expr) (table : List BinarySupportCtor) :
    MetaM (Option Lean.Expr) := do
  let some proofCtor := lookupBinarySupportCtor fn table | return none
  if args.size < 2 then
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

    Supported: const, var 0, add, mul, neg, sin, cos, exp, atan, arsinh
    Not supported: var n (n ≠ 0), inv, log, atanh -/
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

  else
    throwError "Cannot generate UsesOnlyVar0 proof for: {e_ast}\n\
                This expression contains unsupported operations (inv, log, atanh, or var n with n ≠ 0)."

/-! ## ExprSupported Proof Generation

Generate proof terms of type `ExprSupported e` by recursively matching
on the structure of `e : LeanCert.Core.Expr`.

Note: ExprSupported is a strict subset of ExprSupportedCore.
ExprSupported only supports: const, var, add, mul, neg, sin, cos, exp
-/

/-- Generate a proof of `ExprSupported e_ast` by matching on the AST structure.

    This function inspects the head constant of the AST expression and
    recursively builds the appropriate proof constructor.

    Supported: const, var, add, mul, neg, sin, cos, exp
    Not supported: log, sqrt, sinh, cosh, tanh, pi, inv, atan, arsinh, atanh -/
partial def mkSupportedProof (e_ast : Lean.Expr) : MetaM Lean.Expr := do
  let fn := e_ast.getAppFn
  let args := e_ast.getAppArgs

  if fn.isConstOf ``LeanCert.Core.Expr.const then
    let q := args[0]!
    mkAppM ``LeanCert.Core.ExprSupported.const #[q]

  else if fn.isConstOf ``LeanCert.Core.Expr.var then
    let idx := args[0]!
    mkAppM ``LeanCert.Core.ExprSupported.var #[idx]

  else
    if let some h ← tryBinarySupportProof mkSupportedProof fn args
        [ ⟨``LeanCert.Core.Expr.add, ``LeanCert.Core.ExprSupported.add⟩
        , ⟨``LeanCert.Core.Expr.mul, ``LeanCert.Core.ExprSupported.mul⟩ ] then
      return h
    if let some h ← tryUnarySupportProof mkSupportedProof fn args
        [ ⟨``LeanCert.Core.Expr.neg, ``LeanCert.Core.ExprSupported.neg⟩
        , ⟨``LeanCert.Core.Expr.sin, ``LeanCert.Core.ExprSupported.sin⟩
        , ⟨``LeanCert.Core.Expr.cos, ``LeanCert.Core.ExprSupported.cos⟩
        , ⟨``LeanCert.Core.Expr.exp, ``LeanCert.Core.ExprSupported.exp⟩ ] then
      return h
    throwError "Cannot generate ExprSupported proof for: {e_ast}\n\
                ExprSupported only covers: const, var, add, mul, neg, sin, cos, exp.\n\
                This expression uses unsupported operations (log, sqrt, sinh, cosh, tanh, pi, inv, etc.).\n\
                For unique root finding, the function must be in this restricted set."

/-! ## ExprSupportedCore Proof Generation

Generate proof terms of type `ExprSupportedCore e` by recursively matching
on the structure of `e : LeanCert.Core.Expr`.
-/

/-- Generate a proof of `ExprSupportedCore e_ast` by matching on the AST structure.

    This function inspects the head constant of the AST expression and
    recursively builds the appropriate proof constructor.

    Supported: const, var, add, mul, neg, sin, cos, exp, log, sqrt, sinh, cosh, tanh, erf, pi
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
                This expression contains unsupported operations (inv, atan, arsinh, or atanh).\n\
                Use mkSupportedWithInvProof for expressions with inv."

/-! ## ExprSupportedWithInv Proof Generation

Generate proof terms of type `ExprSupportedWithInv e` by recursively matching
on the structure of `e : LeanCert.Core.Expr`. This supports the full expression language.
-/

/-- Generate a proof of `ExprSupportedWithInv e_ast` by matching on the AST structure.

    This function supports all expression constructors including inv, log, atan, arsinh, and atanh. -/
partial def mkSupportedWithInvProof (e_ast : Lean.Expr) : MetaM Lean.Expr := do
  -- Get the head constant and arguments
  let fn := e_ast.getAppFn
  let args := e_ast.getAppArgs

  -- Match on AST constructors
  if fn.isConstOf ``LeanCert.Core.Expr.const then
    let q := args[0]!
    mkAppM ``LeanCert.Core.ExprSupportedWithInv.const #[q]

  else if fn.isConstOf ``LeanCert.Core.Expr.var then
    let idx := args[0]!
    mkAppM ``LeanCert.Core.ExprSupportedWithInv.var #[idx]

  else if fn.isConstOf ``LeanCert.Core.Expr.namedConst then
    let c := args[0]!
    mkAppM ``LeanCert.Core.ExprSupportedWithInv.namedConst #[c]

  else
    if let some h ← tryBinarySupportProof mkSupportedWithInvProof fn args
        [ ⟨``LeanCert.Core.Expr.add, ``LeanCert.Core.ExprSupportedWithInv.add⟩
        , ⟨``LeanCert.Core.Expr.mul, ``LeanCert.Core.ExprSupportedWithInv.mul⟩ ] then
      return h
    if let some h ← tryUnarySupportProof mkSupportedWithInvProof fn args
        [ ⟨``LeanCert.Core.Expr.neg, ``LeanCert.Core.ExprSupportedWithInv.neg⟩
        , ⟨``LeanCert.Core.Expr.inv, ``LeanCert.Core.ExprSupportedWithInv.inv⟩
        , ⟨``LeanCert.Core.Expr.sin, ``LeanCert.Core.ExprSupportedWithInv.sin⟩
        , ⟨``LeanCert.Core.Expr.cos, ``LeanCert.Core.ExprSupportedWithInv.cos⟩
        , ⟨``LeanCert.Core.Expr.exp, ``LeanCert.Core.ExprSupportedWithInv.exp⟩
        , ⟨``LeanCert.Core.Expr.log, ``LeanCert.Core.ExprSupportedWithInv.log⟩
        , ⟨``LeanCert.Core.Expr.atan, ``LeanCert.Core.ExprSupportedWithInv.atan⟩
        , ⟨``LeanCert.Core.Expr.arsinh, ``LeanCert.Core.ExprSupportedWithInv.arsinh⟩
        , ⟨``LeanCert.Core.Expr.atanh, ``LeanCert.Core.ExprSupportedWithInv.atanh⟩
        , ⟨``LeanCert.Core.Expr.sinc, ``LeanCert.Core.ExprSupportedWithInv.sinc⟩
        , ⟨``LeanCert.Core.Expr.erf, ``LeanCert.Core.ExprSupportedWithInv.erf⟩
        , ⟨``LeanCert.Core.Expr.sqrt, ``LeanCert.Core.ExprSupportedWithInv.sqrt⟩ ] then
      return h
    throwError "Cannot generate ExprSupportedWithInv proof for: {e_ast}\n\
                Unrecognized expression structure."

/-! ## Testing Infrastructure -/

/-- Elaborate a term, reify it to a LeanCert expression, and generate
    an ExprSupportedCore proof. Useful for debugging. -/
elab "#check_supported " t:term : command => do
  let (ast, proof, proofType) ← liftTermElabM do
    -- Elaborate and reify the term
    let t ← elabTerm t none
    let t ← instantiateMVars t
    let ast ← reify t
    -- Generate the support proof
    let proof ← mkSupportedCoreProof ast
    let proofType ← inferType proof
    return (ast, proof, proofType)
  logInfo m!"AST: {ast}"
  logInfo m!"Generated proof: {proof}"
  logInfo m!"Proof type: {proofType}"

/-- Similar to #check_supported but for ExprSupportedWithInv. -/
elab "#check_supported_inv " t:term : command => do
  let (ast, proof, proofType) ← liftTermElabM do
    let t ← elabTerm t none
    let t ← instantiateMVars t
    let ast ← reify t
    let proof ← mkSupportedWithInvProof ast
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
  let ast ← reify e
  let proof ← mkSupportedCoreProof ast
  return (ast, proof)

/-- Reify a Lean expression and generate both the AST and its ExprSupportedWithInv proof. -/
def reifyWithSupportInv (e : Lean.Expr) : MetaM (Lean.Expr × Lean.Expr) := do
  let ast ← reify e
  let proof ← mkSupportedWithInvProof ast
  return (ast, proof)

end LeanCert.Meta
