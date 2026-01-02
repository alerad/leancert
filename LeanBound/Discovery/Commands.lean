/-
Copyright (c) 2024 LeanBound Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanBound Contributors
-/
import Lean
import LeanBound.Discovery.Find
import LeanBound.Meta.ToExpr
import LeanBound.Meta.ProveSupported

/-!
# Discovery Mode: Elaboration Commands

This module provides interactive commands for exploring mathematical functions:

* `#minimize` - Find the global minimum of an expression on a domain
* `#maximize` - Find the global maximum of an expression on a domain
* `#bounds` - Find both min and max bounds
* `#eval_interval` - Quick interval evaluation

## Usage Examples

```lean
-- Find minimum of x² + sin(x) on [-2, 2]
#minimize (fun x => x^2 + Real.sin x) on [-2, 2]

-- Find maximum with higher precision
#maximize (fun x => Real.exp x - x^2) on [0, 1] precision 20

-- Find bounds for a 2D function
#bounds (fun x y => x*y + x^2) on [-1, 1] × [-1, 1]
```

## Implementation

The commands work by:
1. Elaborating the user's expression
2. Reifying it to a `LeanBound.Core.Expr` AST
3. Running the optimization algorithm
4. Pretty-printing the result
-/

open Lean Meta Elab Command Term

namespace LeanBound.Discovery.Commands

open LeanBound.Core
open LeanBound.Numerics
open LeanBound.Numerics.Optimization
open LeanBound.Meta

-- Use explicit alias to avoid ambiguity with Lean.Expr
abbrev LExpr := LeanBound.Core.Expr

/-! ## Interval Parsing Helpers -/

/-- Parse a rational number from a Lean expression (partial due to nested recursion) -/
partial def parseRat (e : Lean.Expr) : MetaM ℚ := do
  -- Try direct Nat literal
  if let some n := e.rawNatLit? then
    return n
  -- Try matching after reduction
  let e ← whnf e
  if let some n := e.rawNatLit? then
    return n
  -- Try OfNat
  match_expr e with
  | OfNat.ofNat _ n _ =>
    if let some k := n.rawNatLit? then
      return k
    if let some k := n.nat? then
      return k
    throwError "Cannot parse numeric: {e}"
  | Neg.neg _ _ x =>
    let q ← parseRat x
    return -q
  | HDiv.hDiv _ _ _ _ a b =>
    let qa ← parseRat a
    let qb ← parseRat b
    if qb == 0 then throwError "Division by zero in interval bound"
    return qa / qb
  | _ => throwError "Cannot parse as rational: {e}"

/-- Parse an interval from syntax like `[a, b]` -/
def parseInterval (stx : Syntax) : TermElabM IntervalRat := do
  match stx with
  | `([$lo:term, $hi:term]) =>
    let loExpr ← elabTerm lo (some (mkConst ``Real))
    let hiExpr ← elabTerm hi (some (mkConst ``Real))
    let loQ ← parseRat loExpr
    let hiQ ← parseRat hiExpr
    if h : loQ ≤ hiQ then
      return { lo := loQ, hi := hiQ, le := h }
    else
      throwError "Invalid interval: lo > hi ({loQ} > {hiQ})"
  | _ => throwError "Expected interval syntax [lo, hi]"

/-- Parse a box (product of intervals) -/
partial def parseBox (stx : Syntax) : TermElabM Box := do
  -- Handle single interval
  if let `([$_lo:term, $_hi:term]) := stx then
    let I ← parseInterval stx
    return [I]
  -- Handle product × syntax
  if let `($left × $right) := stx then
    let leftBox ← parseBox left
    let rightBox ← parseBox right
    return leftBox ++ rightBox
  -- Handle explicit box list
  throwError "Expected interval [lo, hi] or product [a,b] × [c,d]"

/-! ## Result Formatting -/

/-- Format a rational for display as a decimal string -/
def formatRat (q : ℚ) (_precision : Nat := 6) : String :=
  -- Convert to decimal approximation
  let num := q.num
  let den := q.den
  if den == 1 then
    toString num
  else
    -- Compute decimal approximation manually
    let (sign, absNum) := if num < 0 then ("-", -num) else ("", num)
    let intPart := absNum / den
    let fracPart := absNum % den
    if fracPart == 0 then
      s!"{sign}{intPart}"
    else
      -- Compute 6 decimal digits
      let scaled := fracPart * 1000000 / den
      s!"{sign}{intPart}.{scaled}"

/-- Format an interval for display -/
def formatInterval (I : IntervalRat) : String :=
  s!"[{formatRat I.lo}, {formatRat I.hi}]"

/-! ## #minimize Command -/

/-- Syntax for #minimize command -/
syntax (name := minimizeCmd) "#minimize " term " on " term (" precision " num)? : command

/-- Elaborator for #minimize -/
@[command_elab minimizeCmd]
unsafe def elabMinimize : CommandElab := fun stx => do
  match stx with
  | `(command| #minimize $func on $dom $[precision $prec]?) =>
    liftTermElabM do
      -- 1. Elaborate the function
      let funcExpr ← elabTerm func none
      let funcExpr ← instantiateMVars funcExpr

      -- 2. Reify to LeanBound AST
      let ast ← reify funcExpr

      -- 3. Parse the domain
      let box ← parseBox dom

      -- 4. Get configuration
      let taylorDepth := match prec with
        | some n => n.getNat
        | none => 10

      -- 5. Run optimization
      let optCfg : GlobalOptConfig := {
        maxIterations := 1000,
        tolerance := 1/1000,
        taylorDepth := taylorDepth,
        useMonotonicity := true
      }
      let astVal ← Meta.evalExpr LExpr (mkConst ``LeanBound.Core.Expr) ast
      let result := globalMinimizeCore astVal box optCfg

      -- 6. Format and display
      logInfo m!"━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
#minimize Results
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  Minimum bound: {formatRat result.bound.lo}
  Upper bound:   {formatRat result.bound.hi}
  Width:         {formatRat (result.bound.hi - result.bound.lo)}
  Iterations:    {result.bound.iterations}
  Verified:      ✓ (rigorous interval arithmetic)
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
  | _ => throwUnsupportedSyntax

/-! ## #maximize Command -/

/-- Syntax for #maximize command -/
syntax (name := maximizeCmd) "#maximize " term " on " term (" precision " num)? : command

/-- Elaborator for #maximize -/
@[command_elab maximizeCmd]
unsafe def elabMaximize : CommandElab := fun stx => do
  match stx with
  | `(command| #maximize $func on $dom $[precision $prec]?) =>
    liftTermElabM do
      let funcExpr ← elabTerm func none
      let funcExpr ← instantiateMVars funcExpr
      let ast ← reify funcExpr
      let box ← parseBox dom
      let taylorDepth := match prec with
        | some n => n.getNat
        | none => 10

      let optCfg : GlobalOptConfig := {
        maxIterations := 1000,
        tolerance := 1/1000,
        taylorDepth := taylorDepth,
        useMonotonicity := true
      }
      let astVal ← Meta.evalExpr LExpr (mkConst ``LeanBound.Core.Expr) ast
      let result := globalMaximizeCore astVal box optCfg

      logInfo m!"━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
#maximize Results
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  Maximum bound: {formatRat result.bound.hi}
  Lower bound:   {formatRat result.bound.lo}
  Width:         {formatRat (result.bound.hi - result.bound.lo)}
  Iterations:    {result.bound.iterations}
  Verified:      ✓ (rigorous interval arithmetic)
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
  | _ => throwUnsupportedSyntax

/-! ## #bounds Command -/

/-- Syntax for #bounds command -/
syntax (name := boundsCmd) "#bounds " term " on " term (" precision " num)? : command

/-- Elaborator for #bounds -/
@[command_elab boundsCmd]
unsafe def elabBounds : CommandElab := fun stx => do
  match stx with
  | `(command| #bounds $func on $dom $[precision $prec]?) =>
    liftTermElabM do
      let funcExpr ← elabTerm func none
      let funcExpr ← instantiateMVars funcExpr
      let ast ← reify funcExpr
      let box ← parseBox dom
      let taylorDepth := match prec with
        | some n => n.getNat
        | none => 10

      let optCfg : GlobalOptConfig := {
        maxIterations := 1000,
        tolerance := 1/1000,
        taylorDepth := taylorDepth,
        useMonotonicity := true
      }

      let astVal ← Meta.evalExpr LExpr (mkConst ``LeanBound.Core.Expr) ast
      let minResult := globalMinimizeCore astVal box optCfg
      let maxResult := globalMaximizeCore astVal box optCfg

      logInfo m!"━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
#bounds Results
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  f(x) ∈ [{formatRat minResult.bound.lo}, {formatRat maxResult.bound.hi}]

  Minimum: {formatRat minResult.bound.lo} (± {formatRat (minResult.bound.hi - minResult.bound.lo)})
  Maximum: {formatRat maxResult.bound.hi} (± {formatRat (maxResult.bound.hi - maxResult.bound.lo)})

  Total iterations: {minResult.bound.iterations + maxResult.bound.iterations}
  Verified: ✓
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
  | _ => throwUnsupportedSyntax

/-! ## #eval_interval Command -/

/-- Syntax for quick interval evaluation -/
syntax (name := evalIntervalCmd) "#eval_interval " term " on " term (" precision " num)? : command

/-- Elaborator for #eval_interval -/
@[command_elab evalIntervalCmd]
unsafe def elabEvalInterval : CommandElab := fun stx => do
  match stx with
  | `(command| #eval_interval $func on $dom $[precision $prec]?) =>
    liftTermElabM do
      let funcExpr ← elabTerm func none
      let funcExpr ← instantiateMVars funcExpr
      let ast ← reify funcExpr
      let box ← parseBox dom
      let taylorDepth := match prec with
        | some n => n.getNat
        | none => 10

      let evalCfg : EvalConfig := { taylorDepth := taylorDepth }
      let env : IntervalEnv := fun i => box.getD i (IntervalRat.singleton 0)
      let astVal ← Meta.evalExpr LExpr (mkConst ``LeanBound.Core.Expr) ast
      let result := evalIntervalCore astVal env evalCfg

      logInfo m!"━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
#eval_interval Results
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  f(x) ∈ [{formatRat result.lo}, {formatRat result.hi}]
  Width: {formatRat result.width}
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
  | _ => throwUnsupportedSyntax

end LeanBound.Discovery.Commands
