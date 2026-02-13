/-
Copyright (c) 2024 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import Lean
import LeanCert.Core.Expr
import LeanCert.Meta.Numeral

/-!
# Metaprogram for Reifying Lean Expressions to LeanCert AST

This module provides metaprogramming infrastructure to translate Lean kernel
expressions (e.g., `fun (x : ℝ) => x + 2`) into `LeanCert.Core.Expr` terms
(e.g., `Expr.add (Expr.var 0) (Expr.const 2)`).

## Main definitions

* `LeanCert.Meta.Context` - Context tracking free variables and their de Bruijn indices
* `LeanCert.Meta.TranslateM` - The translation monad
* `LeanCert.Meta.toLeanCertExpr` - Main recursive translation function
* `LeanCert.Meta.reify` - Entry point that handles lambda expressions

## Usage

```lean
#leancert_reflect (fun x => x * x + 1)
-- Output: Expr.add (Expr.mul (Expr.var 0) (Expr.var 0)) (Expr.const 1)
```
-/

open Lean Meta Elab Command Term

namespace LeanCert.Meta

/-- Closed-form rewrite for max on reals, used for reification via existing Expr nodes. -/
theorem max_eq_half_add_abs_sub (a b : Real) :
    max a b = (a + b + |b + (-a)|) / 2 := by
  have h1 : min a b + max a b = a + b := min_add_max a b
  have h2 : max a b - min a b = |b + (-a)| := by
    simpa [sub_eq_add_neg] using (max_sub_min_eq_abs a b)
  linarith

/-- Closed-form rewrite for min on reals, used for reification via existing Expr nodes. -/
theorem min_eq_half_sub_abs_sub (a b : Real) :
    min a b = (a + b - |b + (-a)|) / 2 := by
  have h1 : min a b + max a b = a + b := min_add_max a b
  have h2 : max a b - min a b = |b + (-a)| := by
    simpa [sub_eq_add_neg] using (max_sub_min_eq_abs a b)
  linarith

/-- Context for the translation. Stores fvars of the lambda being traversed.
    `vars[0]` corresponds to `var 0`, `vars[1]` to `var 1`, etc. -/
structure Context where
  /-- Array of free variables from the lambda telescope -/
  vars : Array Lean.Expr := #[]

/-- The translation monad: ReaderT over MetaM with our Context. -/
abbrev TranslateM := ReaderT Context MetaM

/-- Look up a Free Variable in the context. Returns its de Bruijn index if found. -/
def findVarIdx? (e : Lean.Expr) : TranslateM (Option Nat) := do
  let ctx ← read
  return ctx.vars.findIdx? (fun x => x == e)

/-! ## Helper Functions: AST Constructors

These functions build `LeanCert.Core.Expr` syntax trees. They construct Lean
expressions that *represent* LeanCert AST terms.
-/

/-- Build `LeanCert.Core.Expr.const q` for a rational number. -/
def mkExprConst (q : ℚ) : MetaM Lean.Expr := do
  -- Build the rational literal manually
  -- Rat.divInt num den creates num / den as a rational
  let numExpr := toExpr q.num  -- Int
  let ratExpr ← mkAppM ``Rat.divInt #[numExpr, toExpr (q.den : ℤ)]
  mkAppM ``LeanCert.Core.Expr.const #[ratExpr]

/-- ToExpr instance for ℚ (rationals) -/
instance : ToExpr ℚ where
  toExpr q := mkApp2 (mkConst ``Rat.divInt) (toExpr q.num) (toExpr (q.den : ℤ))
  toTypeExpr := mkConst ``Rat

/-- Build `LeanCert.Core.Expr.var idx` for a variable index. -/
def mkExprVar (idx : Nat) : MetaM Lean.Expr :=
  mkAppM ``LeanCert.Core.Expr.var #[toExpr idx]

/-- Build `LeanCert.Core.Expr.add e1 e2`. -/
def mkExprAdd (e1 e2 : Lean.Expr) : MetaM Lean.Expr :=
  mkAppM ``LeanCert.Core.Expr.add #[e1, e2]

/-- Build `LeanCert.Core.Expr.mul e1 e2`. -/
def mkExprMul (e1 e2 : Lean.Expr) : MetaM Lean.Expr :=
  mkAppM ``LeanCert.Core.Expr.mul #[e1, e2]

/-- Build `LeanCert.Core.Expr.neg e`. -/
def mkExprNeg (e : Lean.Expr) : MetaM Lean.Expr :=
  mkAppM ``LeanCert.Core.Expr.neg #[e]

/-- Build subtraction `e1 - e2` as `e1 + (-e2)` in Expr AST. -/
def mkExprSub (e1 e2 : Lean.Expr) : MetaM Lean.Expr := do
  mkExprAdd e1 (← mkExprNeg e2)

/-- Build `LeanCert.Core.Expr.inv e`. -/
def mkExprInv (e : Lean.Expr) : MetaM Lean.Expr :=
  mkAppM ``LeanCert.Core.Expr.inv #[e]

/-- Build `LeanCert.Core.Expr.sin e`. -/
def mkExprSin (e : Lean.Expr) : MetaM Lean.Expr :=
  mkAppM ``LeanCert.Core.Expr.sin #[e]

/-- Build `LeanCert.Core.Expr.cos e`. -/
def mkExprCos (e : Lean.Expr) : MetaM Lean.Expr :=
  mkAppM ``LeanCert.Core.Expr.cos #[e]

/-- Build `LeanCert.Core.Expr.exp e`. -/
def mkExprExp (e : Lean.Expr) : MetaM Lean.Expr :=
  mkAppM ``LeanCert.Core.Expr.exp #[e]

/-- Build `LeanCert.Core.Expr.log e`. -/
def mkExprLog (e : Lean.Expr) : MetaM Lean.Expr :=
  mkAppM ``LeanCert.Core.Expr.log #[e]

/-- Build `LeanCert.Core.Expr.atan e`. -/
def mkExprAtan (e : Lean.Expr) : MetaM Lean.Expr :=
  mkAppM ``LeanCert.Core.Expr.atan #[e]

/-- Build `LeanCert.Core.Expr.arsinh e`. -/
def mkExprArsinh (e : Lean.Expr) : MetaM Lean.Expr :=
  mkAppM ``LeanCert.Core.Expr.arsinh #[e]

/-- Build `LeanCert.Core.Expr.atanh e`. -/
def mkExprAtanh (e : Lean.Expr) : MetaM Lean.Expr :=
  mkAppM ``LeanCert.Core.Expr.atanh #[e]

/-- Build `LeanCert.Core.Expr.sinc e`. -/
def mkExprSinc (e : Lean.Expr) : MetaM Lean.Expr :=
  mkAppM ``LeanCert.Core.Expr.sinc #[e]

/-- Build `LeanCert.Core.Expr.erf e`. -/
def mkExprErf (e : Lean.Expr) : MetaM Lean.Expr :=
  mkAppM ``LeanCert.Core.Expr.erf #[e]

/-- Build `LeanCert.Core.Expr.sqrt e`. -/
def mkExprSqrt (e : Lean.Expr) : MetaM Lean.Expr :=
  mkAppM ``LeanCert.Core.Expr.sqrt #[e]

/-- Build absolute value as `sqrt (e * e)`. -/
def mkExprAbs (e : Lean.Expr) : MetaM Lean.Expr := do
  mkExprSqrt (← mkExprMul e e)

/-- Build `LeanCert.Core.Expr.sinh e`. -/
def mkExprSinh (e : Lean.Expr) : MetaM Lean.Expr :=
  mkAppM ``LeanCert.Core.Expr.sinh #[e]

/-- Build `LeanCert.Core.Expr.cosh e`. -/
def mkExprCosh (e : Lean.Expr) : MetaM Lean.Expr :=
  mkAppM ``LeanCert.Core.Expr.cosh #[e]

/-- Build `LeanCert.Core.Expr.tanh e`. -/
def mkExprTanh (e : Lean.Expr) : MetaM Lean.Expr :=
  mkAppM ``LeanCert.Core.Expr.tanh #[e]

/-- Build `LeanCert.Core.Expr.pi`. -/
def mkExprPi : MetaM Lean.Expr :=
  mkAppM ``LeanCert.Core.Expr.pi #[]

/-- Build max(a,b) via `(a + b + |b - a|) / 2` in existing Expr constructors. -/
def mkExprMaxViaAbs (a b : Lean.Expr) : MetaM Lean.Expr := do
  let sumAB ← mkExprAdd a b
  let diffBA ← mkExprSub b a
  let absDiff ← mkExprAbs diffBA
  let numer ← mkExprAdd sumAB absDiff
  let half ← mkExprConst ((1 : ℚ) / 2)
  mkExprMul half numer

/-- Build min(a,b) via `(a + b - |b - a|) / 2` in existing Expr constructors. -/
def mkExprMinViaAbs (a b : Lean.Expr) : MetaM Lean.Expr := do
  let sumAB ← mkExprAdd a b
  let diffBA ← mkExprSub b a
  let absDiff ← mkExprAbs diffBA
  let numer ← mkExprSub sumAB absDiff
  let half ← mkExprConst ((1 : ℚ) / 2)
  mkExprMul half numer

/-! ## Constant Extraction

Numeric parsing is shared in `LeanCert.Meta.Numeral.toRat?`.
-/

/-! ## Main Reification Loop

The recursive function that traverses the Lean expression tree and builds
the corresponding LeanCert AST.
-/

/-- Main recursive translation from Lean.Expr to LeanCert.Core.Expr (as Lean.Expr).

Logic:
1. Check if it's a variable in our context
2. Check if it's a constant number
3. Check if it's a known arithmetic operator (+, *, -, /)
4. Check if it's a known transcendental (sin, cos, exp, log, etc.)
5. Fail if unrecognized
-/
partial def toLeanCertExpr (e : Lean.Expr) : TranslateM Lean.Expr := do
  -- 1. Check if it is a free variable in our context
  if let some idx ← findVarIdx? e then
    return ← mkExprVar idx

  -- 2. Check if it is a numeric constant
  if let some q ← toRat? e then
    return ← mkExprConst q

  -- 3. Try to match on unreduced expression first (important!)
  if let some result ← tryMatchExpr e then
    return result

  -- 4. If no match, try reducing with whnf and matching again
  let eReduced ← whnf e
  if eReduced != e then
    if let some result ← tryMatchExpr eReduced then
      return result

  -- 5. Try to unfold definitions and retry
  let e' ← unfoldDefinition? e
  match e' with
  | some unfolded =>
    if unfolded != e then
      toLeanCertExpr unfolded
    else
      throwUnsupported e
  | none =>
    throwUnsupported e

where
  /-- Try to match the expression against known patterns. -/
  tryMatchExpr (e : Lean.Expr) : TranslateM (Option Lean.Expr) := do
    -- For `Real`, `abs x` often elaborates to a max/sup form like
    -- `SemilatticeSup.toMax.1 x (-x)` or a private `Real.sup` helper.
    -- Recognize these shapes and normalize them to sqrt(x * x).
    if let some (a, b) := (← toMaxArgs? e) then
      let absArg? : Option Lean.Expr ←
        match_expr b with
        | Neg.neg _ _ b' =>
          if b' == a then
            pure (some a)
          else
            pure none
        | _ =>
          match_expr a with
          | Neg.neg _ _ a' =>
            if a' == b then
              pure (some b)
            else
              pure none
          | _ => pure none
      if let some x := absArg? then
        let ex ← toLeanCertExpr x
        let exSq ← mkExprMul ex ex
        return some (← mkExprSqrt exSq)
      -- Generic max case: reify via a closed form with abs.
      let ea ← toLeanCertExpr a
      let eb ← toLeanCertExpr b
      return some (← mkExprMaxViaAbs ea eb)

    -- Generic min case: reify via a closed form with abs.
    if let some (a, b) := (← toMinArgs? e) then
      let ea ← toLeanCertExpr a
      let eb ← toLeanCertExpr b
      return some (← mkExprMinViaAbs ea eb)

    let fn := e.getAppFn
    let args := e.getAppArgs
    let some headName := fn.constName?
      | return none

    -- Nullary constants
    if headName == ``Real.pi then
      return some (← mkExprPi)

    -- Unary operations dispatched from a table
    if let some mk := lookupUnary headName then
      if let some x := lastArg? args then
        let ex ← toLeanCertExpr x
        return some (← mk ex)
      return none

    -- Binary operations with direct constructors
    if let some mk := lookupBinary headName then
      if let some (a, b) := lastTwoArgs? args then
        let ea ← toLeanCertExpr a
        let eb ← toLeanCertExpr b
        return some (← mk ea eb)
      return none

    -- Subtraction: a - b  ↦  a + (-b)
    if headName == ``HSub.hSub then
      if let some (a, b) := lastTwoArgs? args then
        let ea ← toLeanCertExpr a
        let eb ← toLeanCertExpr b
        let neg_b ← mkExprNeg eb
        return some (← mkExprAdd ea neg_b)
      return none

    -- Division: a / b  ↦  a * (1/b) when b is constant; else a * inv(b)
    if headName == ``HDiv.hDiv then
      if let some (a, b) := lastTwoArgs? args then
        let ea ← toLeanCertExpr a
        if let some qb ← toRat? b then
          if qb ≠ 0 then
            let eRecip ← mkExprConst ((1 : ℚ) / qb)
            return some (← mkExprMul ea eRecip)
        let eb ← toLeanCertExpr b
        let inv_b ← mkExprInv eb
        return some (← mkExprMul ea inv_b)
      return none

    -- Power with rational exponents.
    if headName == ``HPow.hPow then
      if let some (base, exp) := lastTwoArgs? args then
        if let some q ← toRat? exp then
          let ebase ← toLeanCertExpr base
          if q.den == 1 then
            return some (← mkPowInt ebase q.num)
          if q.den == 2 then
            return some (← mkHalfIntegerPow ebase q.num)
          -- General rational exponents are lowered to exp(log(base) * q).
          -- This keeps the AST small while making domain constraints explicit
          -- through `log` (which must be certified on positive intervals).
          let qExpr ← mkExprConst q
          let logBase ← mkExprLog ebase
          let prod ← mkExprMul logBase qExpr
          return some (← mkExprExp prod)
      return none

    return none

  /-- Unary head-symbol handlers. -/
  lookupUnary (n : Name) : Option (Lean.Expr → MetaM Lean.Expr) :=
    unaryTable.findSome? (fun (name, mk) =>
      if name == n then some mk else none)

  /-- Binary head-symbol handlers. -/
  lookupBinary (n : Name) : Option (Lean.Expr → Lean.Expr → MetaM Lean.Expr) :=
    binaryTable.findSome? (fun (name, mk) =>
      if name == n then some mk else none)

  /-- Table for unary operations. -/
  unaryTable : List (Name × (Lean.Expr → MetaM Lean.Expr)) :=
    [ (``Neg.neg, mkExprNeg)
    , (``Inv.inv, mkExprInv)
    , (``Real.sin, mkExprSin)
    , (``Real.cos, mkExprCos)
    , (``Real.exp, mkExprExp)
    , (``Real.log, mkExprLog)
    , (``Real.arctan, mkExprAtan)
    , (``Real.arsinh, mkExprArsinh)
    , (``LeanCert.Core.Real.atanh, mkExprAtanh)
    , (``Real.sinc, mkExprSinc)
    , (``LeanCert.Core.Real.erf, mkExprErf)
    , (``Real.sqrt, mkExprSqrt)
    , (``Real.sinh, mkExprSinh)
    , (``Real.cosh, mkExprCosh)
    , (``Real.tanh, mkExprTanh)
    , (``abs, fun x => do
        let xSq ← mkExprMul x x
        mkExprSqrt xSq)
    ]

  /-- Table for binary operations with direct AST constructors. -/
  binaryTable : List (Name × (Lean.Expr → Lean.Expr → MetaM Lean.Expr)) :=
    [ (``HAdd.hAdd, mkExprAdd)
    , (``HMul.hMul, mkExprMul)
    ]

  /-- Last argument of an application (if present). -/
  lastArg? (args : Array Lean.Expr) : Option Lean.Expr :=
    if _h : args.size ≥ 1 then
      some (args[args.size - 1]!)
    else
      none

  /-- Last two arguments of an application (if present). -/
  lastTwoArgs? (args : Array Lean.Expr) : Option (Lean.Expr × Lean.Expr) :=
    if _h : args.size ≥ 2 then
      some (args[args.size - 2]!, args[args.size - 1]!)
    else
      none

  /-- Rich unsupported-expression diagnostics (head symbol + arity). -/
  throwUnsupported {α : Type} (e : Lean.Expr) : TranslateM α := do
    let eTy ← inferType e
    let ePP ← Meta.ppExpr e
    let eTyPP ← Meta.ppExpr eTy
    let head := e.getAppFn
    let headPP ← Meta.ppExpr head
    let headName := head.constName?.map toString |>.getD "(non-const head)"
    let args := e.getAppArgs
    throwError "Unsupported expression for LeanCert: {ePP}\n\n\
                Expression type: {eTyPP}\n\
                Head symbol: {headName}\n\
                Head term: {headPP}\n\
                Arity: {args.size}\n\n\
                Supported operations:\n\
                • Arithmetic: +, -, *, /, ^ (integer, half-integer, and general rational exponents), abs, max, min\n\
                • Transcendentals: Real.sin, Real.cos, Real.exp, Real.log,\n\
                  Real.sqrt, Real.arctan, Real.arsinh, Real.atanh,\n\
                  Real.sinc, Real.erf, Real.sinh, Real.cosh, Real.tanh\n\
                • Constants: rational numbers, Real.pi\n\n\
                Suggestions:\n\
                • Normalize first with `interval_norm`\n\
                • Unfold custom definitions with `simp only [myDef]`\n\
                • Add a handler for the head symbol above if this form should be supported"

  /-- Build a power expression using repeated multiplication.
      pow(base, k) = base * base * ... * base (k times) or 1 if k = 0. -/
  mkPow (base : Lean.Expr) (k : Nat) : MetaM Lean.Expr := do
    if k == 0 then
      mkExprConst 1
    else if k == 1 then
      return base
    else
      let rest ← mkPow base (k - 1)
      mkExprMul base rest

  /-- Build `base ^ z` for integer `z` using `Expr.pow` + `Expr.inv`. -/
  mkPowInt (base : Lean.Expr) (z : Int) : MetaM Lean.Expr := do
    if z ≥ 0 then
      mkPow base z.toNat
    else
      let p ← mkPow base z.natAbs
      mkExprInv p

  /-- Build `base ^ (n/2)` for integer numerator `n` (half-integers). -/
  mkHalfIntegerPow (base : Lean.Expr) (n : Int) : MetaM Lean.Expr := do
    -- n/2 in reduced form always has odd |n|. We still handle all cases defensively.
    if n = 0 then
      mkExprConst 1
    else
      let absN : Nat := n.natAbs
      let k : Nat := (absN - 1) / 2
      let sqrtBase ← mkExprSqrt base
      let posPart ←
        if k == 0 then
          pure sqrtBase
        else
          let p ← mkPow base k
          mkExprMul p sqrtBase
      if n ≥ 0 then
        pure posPart
      else
        mkExprInv posPart

  /-- Try to decompose `e` as `max a b` using definitional equality.
      This is robust against internal projection names changing across
      Mathlib versions. -/
  toMaxArgs? (e : Lean.Expr) : MetaM (Option (Lean.Expr × Lean.Expr)) := do
    let args := e.getAppArgs
    if args.size < 2 then return none
    let a := args[args.size - 2]!
    let b := args[args.size - 1]!
    try
      let maxExpr ← mkAppM ``max #[a, b]
      if (← isDefEq e maxExpr) then
        return some (a, b)
    catch _ => pure ()
    return none

  /-- Try to decompose `e` as `min a b` using definitional equality. -/
  toMinArgs? (e : Lean.Expr) : MetaM (Option (Lean.Expr × Lean.Expr)) := do
    let args := e.getAppArgs
    if args.size < 2 then return none
    let a := args[args.size - 2]!
    let b := args[args.size - 1]!
    try
      let minExpr ← mkAppM ``min #[a, b]
      if (← isDefEq e minExpr) then
        return some (a, b)
    catch _ => pure ()
    return none

/-! ## Entry Point

The main entry point that strips the leading lambda and initializes the context.
-/

/-- Entry point: Takes a lambda `fun x y ... => body` and returns the LeanCert AST.

This function uses `lambdaTelescope` to introduce the lambda-bound variables
as free variables, then translates the body with those variables tracked in
the context.
-/
def reify (e : Lean.Expr) : MetaM Lean.Expr := do
  lambdaTelescope e fun vars body => do
    -- 'vars' are the fvars for the lambda arguments
    let ctx : Context := { vars := vars }
    (toLeanCertExpr body).run ctx

/-! ## Testing Infrastructure -/

/-- Elaborate a term and reify it to a LeanCert expression.
    Useful for debugging the reification process. -/
elab "#leancert_reflect " t:term : command => do
  let e ← liftTermElabM do
    let t ← elabTerm t none
    let t ← instantiateMVars t
    reify t
  logInfo m!"Reified: {e}"

end LeanCert.Meta
