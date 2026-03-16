/-
Copyright (c) 2024 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import Lean
import LeanCert.Core.Expr

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

/-- Build `LeanCert.Core.Expr.abs e` (= `Expr.sqrt (Expr.mul e e)`). -/
def mkExprAbs (e : Lean.Expr) : MetaM Lean.Expr :=
  mkAppM ``LeanCert.Core.Expr.abs #[e]

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

/-! ## Constant Extraction

Lean stores numbers as complex hierarchies of type classes (`OfNat.ofNat`,
`Rat.cast`, etc.). We need a pattern matcher that digs out the actual number.
-/

/-- Attempt to parse a Lean Expr as a constant rational number.
    Handles various encodings: Nat literals, Int literals, OfNat, Neg, etc. -/
partial def toRat? (e : Lean.Expr) : MetaM (Option ℚ) := do
  -- Case 1: Simple Nat literal
  if let some n := e.rawNatLit? then
    return some (n : ℚ)

  -- Case 2: Try matching before whnf
  if let some q ← tryMatchNumeric e then
    return some q

  -- Case 3: Reduce the expression to handle type class projections
  let e ← whnf e

  -- Case 4: Try matching after whnf
  if let some q ← tryMatchNumeric e then
    return some q

  return none

where
  /-- Try to match a numeric expression. -/
  tryMatchNumeric (e : Lean.Expr) : MetaM (Option ℚ) := do
    match_expr e with
    -- OfNat.ofNat α n inst => extract n
    | OfNat.ofNat _ n _ =>
      if let some k := n.rawNatLit? then
        return some (k : ℚ)
      -- For natural number literals like (2 : ℝ), the second arg contains the nat
      if let some k := n.nat? then
        return some (k : ℚ)
      -- Try to recursively extract from n
      toRat? n

    -- Neg.neg α inst x => negate the result
    | Neg.neg _ _ x =>
      if let some q ← toRat? x then
        return some (-q)
      else
        return none

    -- HSub.hSub for constant subtraction
    | HSub.hSub _ _ _ _ a b =>
      match ← toRat? a, ← toRat? b with
      | some qa, some qb => return some (qa - qb)
      | _, _ => return none

    -- HDiv.hDiv α β γ inst n d => n / d
    | HDiv.hDiv _ _ _ _ n d =>
      match ← toRat? n, ← toRat? d with
      | some qn, some qd => return some (qn / qd)
      | _, _ => return none

    -- HMul.hMul for constant multiplication
    | HMul.hMul _ _ _ _ a b =>
      match ← toRat? a, ← toRat? b with
      | some qa, some qb => return some (qa * qb)
      | _, _ => return none

    -- HAdd.hAdd for constant addition
    | HAdd.hAdd _ _ _ _ a b =>
      match ← toRat? a, ← toRat? b with
      | some qa, some qb => return some (qa + qb)
      | _, _ => return none

    -- Int.ofNat n => positive integer
    | Int.ofNat n =>
      if let some k := n.rawNatLit? then
        return some (k : ℚ)
      else
        toRat? n

    -- Int.negSucc n => -(n+1)
    | Int.negSucc n =>
      if let some k := n.rawNatLit? then
        return some (-(k + 1 : ℚ))
      else
        return none

    -- Rat.mk' num den (normalized rational)
    | Rat.mk' num den _ _ =>
      match ← toRat? num, ← toRat? den with
      | some qnum, some qden => return some (qnum / qden)
      | _, _ => return none

    -- Rat.cast α inst q => extract q (handles ↑(q : ℚ) : ℝ)
    | Rat.cast _ _ q => toRat? q

    -- RatCast.ratCast α inst q (alternative form)
    | RatCast.ratCast _ _ q => toRat? q

    -- Nat.cast α inst n => extract n (handles ↑(n : ℕ) : ℝ)
    | Nat.cast _ _ n => toRat? n

    -- NatCast.natCast α inst n (alternative form)
    | NatCast.natCast _ _ n => toRat? n

    -- Int.cast α inst z => extract z (handles ↑(z : ℤ) : ℝ)
    | Int.cast _ _ z => toRat? z

    -- IntCast.intCast α inst z (alternative form)
    | IntCast.intCast _ _ z => toRat? z

    -- OfScientific.ofScientific α inst mantissa exponentSign decimalExponent
    -- Represents: mantissa * 10^(if exponentSign then -decimalExponent else decimalExponent)
    -- E.g., 2.5 = 25 * 10^(-1) → mantissa=25, exponentSign=true, decimalExponent=1
    | OfScientific.ofScientific _ _ mantissa exponentSign decimalExponent =>
      let some m := mantissa.rawNatLit?
        | return none
      let some exp := decimalExponent.rawNatLit?
        | return none
      -- Check exponentSign: true means negative exponent (like 2.5 = 25e-1)
      let isNegExp := exponentSign.constName? == some ``Bool.true
      let base10 : ℚ := (10 : ℚ) ^ exp
      if isNegExp then
        return some ((m : ℚ) / base10)  -- e.g., 25 / 10 = 2.5
      else
        return some ((m : ℚ) * base10)  -- e.g., 25 * 10 = 250

    | _ => return none

/-! ## Main Reification Loop

The recursive function that traverses the Lean expression tree and builds
the corresponding LeanCert AST.
-/

/-- Main recursive translation from Lean.Expr to LeanCert.Core.Expr (as Lean.Expr).

Logic:
1. Check if it's a variable in our context
2. Try to match a known operator/function (+, *, -, /, sin, cos, exp, etc.)
3. Check if it's a numeric constant (ℕ, ℤ, ℚ literals and casts)
4. Reduce with whnf and retry
5. Unfold definitions and retry

**Important**: Step 2 (operator matching) must come before step 3 (numeric constant).
Otherwise `toRat?` eagerly constant-folds compound expressions like `↑(-2 : ℤ) + 3`
into `const(1)`, losing the syntactic structure needed by the bridge converter.
With operators first, this reifies as `add(const(-2), const(3))` which the bridge
can match against the goal. -/
partial def toLeanCertExpr (e : Lean.Expr) : TranslateM Lean.Expr := do
  -- 1. Check if it is a free variable in our context
  if let some idx ← findVarIdx? e then
    return ← mkExprVar idx

  -- 2. Try to match on unreduced expression first (important!)
  -- This must come BEFORE toRat? so that compound expressions like
  -- `↑(-2 : ℤ) + 3` are reified structurally (as add(const(-2), const(3)))
  -- rather than constant-folded by toRat? (which would produce const(1),
  -- losing the structure needed for the bridge converter to match the goal).
  if let some result ← tryMatchExpr e then
    return result

  -- 3. Check if it is a numeric constant (leaf values only at this point)
  if let some q ← toRat? e then
    return ← mkExprConst q

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
      let eTy ← inferType e
      let ePP ← Meta.ppExpr e
      let eTyPP ← Meta.ppExpr eTy
      throwError "Unsupported expression for LeanCert: {ePP}\n\n\
                  Expression type: {eTyPP}\n\n\
                  Supported operations:\n\
                  • Arithmetic: +, -, *, /, ^ (with constant exponent)\n\
                  • Transcendentals: Real.sin, Real.cos, Real.exp, Real.log\n\
                  • Constants: rational numbers, Real.pi\n\n\
                  Suggestions:\n\
                  • If using a custom definition, try unfolding it first with `simp only [myDef]`\n\
                  • Check that all functions are from the Real namespace\n\
                  • Complex expressions may need manual rewriting"
  | none =>
    let eTy ← inferType e
    let ePP ← Meta.ppExpr e
    let eTyPP ← Meta.ppExpr eTy
    throwError "Unsupported expression for LeanCert: {ePP}\n\n\
                Expression type: {eTyPP}\n\n\
                Supported operations:\n\
                • Arithmetic: +, -, *, /, ^ (with constant exponent)\n\
                • Transcendentals: Real.sin, Real.cos, Real.exp, Real.log\n\
                • Constants: rational numbers, Real.pi\n\n\
                Suggestions:\n\
                • If using a custom definition, try unfolding it first with `simp only [myDef]`\n\
                • Check that all functions are from the Real namespace\n\
                • Complex expressions may need manual rewriting"

where
  /-- Try to match the expression against known patterns. -/
  tryMatchExpr (e : Lean.Expr) : TranslateM (Option Lean.Expr) := do
    match_expr e with
    -- Addition: HAdd.hAdd α β γ inst a b
    | HAdd.hAdd _ _ _ _ a b =>
      let ea ← toLeanCertExpr a
      let eb ← toLeanCertExpr b
      return some (← mkExprAdd ea eb)

    -- Multiplication: HMul.hMul α β γ inst a b
    | HMul.hMul _ _ _ _ a b =>
      let ea ← toLeanCertExpr a
      let eb ← toLeanCertExpr b
      return some (← mkExprMul ea eb)

    -- Subtraction: HSub.hSub α β γ inst a b
    -- Convert a - b to add(a, neg(b))
    | HSub.hSub _ _ _ _ a b =>
      let ea ← toLeanCertExpr a
      let eb ← toLeanCertExpr b
      let neg_b ← mkExprNeg eb
      return some (← mkExprAdd ea neg_b)

    -- Negation: Neg.neg α inst x
    | Neg.neg _ _ x =>
      let ex ← toLeanCertExpr x
      return some (← mkExprNeg ex)

    -- Division: HDiv.hDiv α β γ inst a b
    -- If b is a nonzero constant, convert a / b to mul(a, const(1/b)) to avoid Expr.inv
    -- Otherwise, convert a / b to mul(a, inv(b))
    | HDiv.hDiv _ _ _ _ a b =>
      let ea ← toLeanCertExpr a
      -- Check if b is a constant rational
      if let some qb ← toRat? b then
        if qb ≠ 0 then
          -- b is a nonzero constant: use a * (1/b) as Expr.const
          let reciprocal := (1 : ℚ) / qb
          let eRecip ← mkExprConst reciprocal
          return some (← mkExprMul ea eRecip)
      -- b is not a constant or is zero: fall back to a * inv(b)
      let eb ← toLeanCertExpr b
      let inv_b ← mkExprInv eb
      return some (← mkExprMul ea inv_b)

    -- Inverse: Inv.inv α inst x
    | Inv.inv _ _ x =>
      let ex ← toLeanCertExpr x
      return some (← mkExprInv ex)

    -- Power: HPow.hPow α β γ inst base exp
    | HPow.hPow _ _ _ _ base exp =>
      -- Try to extract natural number exponent
      if let some q ← toRat? exp then
        if q.den == 1 && q.num ≥ 0 then
          let ebase ← toLeanCertExpr base
          return some (← mkPow ebase q.num.toNat)
      return none

    -- Transcendental functions
    | Real.sin x =>
      let ex ← toLeanCertExpr x
      return some (← mkExprSin ex)

    | Real.cos x =>
      let ex ← toLeanCertExpr x
      return some (← mkExprCos ex)

    | Real.exp x =>
      let ex ← toLeanCertExpr x
      return some (← mkExprExp ex)

    | Real.log x =>
      let ex ← toLeanCertExpr x
      return some (← mkExprLog ex)

    | Real.arctan x =>
      let ex ← toLeanCertExpr x
      return some (← mkExprAtan ex)

    | Real.arsinh x =>
      let ex ← toLeanCertExpr x
      return some (← mkExprArsinh ex)

    -- Handle Real.atanh from our own definition
    | LeanCert.Core.Real.atanh x =>
      let ex ← toLeanCertExpr x
      return some (← mkExprAtanh ex)

    -- Handle Real.sinc from Mathlib
    | Real.sinc x =>
      let ex ← toLeanCertExpr x
      return some (← mkExprSinc ex)

    -- Handle Real.erf from our own definition
    | LeanCert.Core.Real.erf x =>
      let ex ← toLeanCertExpr x
      return some (← mkExprErf ex)

    -- Handle Real.sqrt
    | Real.sqrt x =>
      let ex ← toLeanCertExpr x
      return some (← mkExprSqrt ex)

    -- Handle hyperbolic functions
    | Real.sinh x =>
      let ex ← toLeanCertExpr x
      return some (← mkExprSinh ex)

    | Real.cosh x =>
      let ex ← toLeanCertExpr x
      return some (← mkExprCosh ex)

    | Real.tanh x =>
      let ex ← toLeanCertExpr x
      return some (← mkExprTanh ex)

    -- The constant π
    | Real.pi => return some (← mkExprPi)

    -- Absolute value: |x| → sqrt(x * x)
    | abs _ _ _ x =>
      let ex ← toLeanCertExpr x
      let ex_sq ← mkExprMul ex ex
      return some (← mkExprSqrt ex_sq)

    | _ => return none

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
