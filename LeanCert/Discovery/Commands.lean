/-
Copyright (c) 2024 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import Lean
import LeanCert.Discovery.Find
import LeanCert.Meta.ToExpr
import LeanCert.Meta.Numeral
import LeanCert.Meta.ProveSupported

/-!
# Discovery Mode: Elaboration Commands

This module provides interactive commands for exploring mathematical functions:

* `#find_min` - Find the global minimum of an expression on a domain
* `#find_max` - Find the global maximum of an expression on a domain
* `#bounds` - Find both min and max bounds
* `#eval_interval` - Quick interval evaluation

## Usage Examples

```lean
-- Find minimum of x² + sin(x) on [-2, 2]
#find_min (fun x => x^2 + Real.sin x) on [-2, 2]

-- Find maximum with higher precision
#find_max (fun x => Real.exp x - x^2) on [0, 1] precision 20

-- Find bounds for a 2D function
#bounds (fun x y => x*y + x^2) on [-1, 1] × [-1, 1]
```

## Implementation

The commands work by:
1. Elaborating the user's expression
2. Reifying it to a `LeanCert.Core.Expr` AST
3. Running the optimization algorithm
4. Pretty-printing the result
-/

open Lean Meta Elab Command Term

namespace LeanCert.Discovery.Commands

open LeanCert.Core
open LeanCert.Engine
open LeanCert.Engine.Optimization
open LeanCert.Meta

-- Use explicit alias to avoid ambiguity with Lean.Expr
abbrev LExpr := LeanCert.Core.Expr

/-! ## Interval Parsing Helpers -/

/-- Parse a rational expression structurally for interactive discovery commands. -/
partial def parseRat (e : Lean.Expr) : MetaM ℚ := do
  if let some q ← LeanCert.Meta.Numeral.toRatFolded? e then
    return q
  let e ← reduce e (skipTypes := true) (skipProofs := true)
  if let some q ← LeanCert.Meta.Numeral.toRatFolded? e then
    return q
  throwError "Cannot parse as rational: {e}"

/-- Parse an integer from a reduced Lean expression -/
partial def parseIntFromExpr (e : Lean.Expr) : MetaM ℤ := do
  -- Fully reduce the expression to get concrete values
  let e ← reduce e (skipTypes := true) (skipProofs := true)
  -- Check for Int.ofNat n
  match_expr e with
  | Int.ofNat n =>
    let n ← reduce n (skipTypes := true) (skipProofs := true)
    if let some k := n.rawNatLit? then
      return k
    match_expr n with
    | OfNat.ofNat _ m _ =>
      if let some k := m.rawNatLit? then
        return k
      let m ← reduce m (skipTypes := true) (skipProofs := true)
      if let some k := m.rawNatLit? then
        return k
      throwError "Cannot parse nat in Int.ofNat: {n}"
    | _ => throwError "Cannot parse Int.ofNat argument: {n}"
  | Int.negSucc n =>
    let n ← reduce n (skipTypes := true) (skipProofs := true)
    if let some k := n.rawNatLit? then
      return Int.negSucc k
    throwError "Cannot parse Int.negSucc argument: {n}"
  | Int.negOfNat n =>
    let n ← reduce n (skipTypes := true) (skipProofs := true)
    if let some k := n.rawNatLit? then
      return -(k : ℤ)
    throwError "Cannot parse Int.negOfNat argument: {n}"
  | Neg.neg _ _ x =>
    let v ← parseIntFromExpr x
    return -v
  | OfNat.ofNat _ n _ =>
    let n ← reduce n (skipTypes := true) (skipProofs := true)
    if let some k := n.rawNatLit? then
      return k
    throwError "Cannot parse ofNat: {n}"
  | _ =>
    if let some k := e.rawNatLit? then
      return k
    throwError "Cannot parse as integer: {e}"

/-- Parse an integer directly from term syntax -/
partial def parseIntFromSyntax (stx : Syntax) : TermElabM ℤ := do
  -- Handle negative: -n
  if let `(-$n:term) := stx then
    let v ← parseIntFromSyntax n
    return -v
  -- Handle numeric literal
  if let `($n:num) := stx then
    return n.getNat
  throwError "Cannot parse as integer: {stx}"

/-- Parse an interval from syntax like `[a, b]` -/
def parseInterval (stx : Syntax) : TermElabM IntervalRat := do
  match stx with
  | `([$lo:term, $hi:term]) =>
    -- Parse directly from syntax to avoid elaboration issues
    let loI ← parseIntFromSyntax lo
    let hiI ← parseIntFromSyntax hi
    let loQ : ℚ := loI
    let hiQ : ℚ := hiI
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

/-! ## #find_min Command -/

/-- Syntax for #find_min command -/
syntax (name := findMinCmd) "#find_min " term " on " term (" precision " num)? : command

/-- Elaborator for #find_min -/
@[command_elab findMinCmd]
unsafe def elabFindMin : CommandElab := fun stx => do
  match stx with
  | `(command| #find_min $func on $dom $[precision $prec]?) =>
    liftTermElabM do
      -- 1. Elaborate the function
      let funcExpr ← elabTerm func none
      let funcExpr ← instantiateMVars funcExpr

      -- 2. Reify to LeanCert AST
      let ast := (← reifyWithReport funcExpr).expr

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
      let astVal ← Meta.evalExpr LExpr (mkConst ``LeanCert.Core.Expr) ast
      let result := globalMinimizeCore astVal box optCfg

      -- 6. Format and display
      logInfo m!"━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
#find_min Results
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  Minimum bound: {formatRat result.bound.lo}
  Upper bound:   {formatRat result.bound.hi}
  Width:         {formatRat (result.bound.hi - result.bound.lo)}
  Iterations:    {result.bound.iterations}
  Verified:      ✓ (rigorous interval arithmetic)
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
  | _ => throwUnsupportedSyntax

/-! ## #find_max Command -/

/-- Syntax for #find_max command -/
syntax (name := findMaxCmd) "#find_max " term " on " term (" precision " num)? : command

/-- Elaborator for #find_max -/
@[command_elab findMaxCmd]
unsafe def elabFindMax : CommandElab := fun stx => do
  match stx with
  | `(command| #find_max $func on $dom $[precision $prec]?) =>
    liftTermElabM do
      let funcExpr ← elabTerm func none
      let funcExpr ← instantiateMVars funcExpr
      let ast := (← reifyWithReport funcExpr).expr
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
      let astVal ← Meta.evalExpr LExpr (mkConst ``LeanCert.Core.Expr) ast
      let result := globalMaximizeCore astVal box optCfg

      logInfo m!"━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
#find_max Results
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
      let ast := (← reifyWithReport funcExpr).expr
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

      let astVal ← Meta.evalExpr LExpr (mkConst ``LeanCert.Core.Expr) ast
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
      let ast := (← reifyWithReport funcExpr).expr
      let box ← parseBox dom
      let taylorDepth := match prec with
        | some n => n.getNat
        | none => 10

      let evalCfg : EvalConfig := { taylorDepth := taylorDepth }
      let env : IntervalEnv := fun i => box.getD i (IntervalRat.singleton 0)
      let astVal ← Meta.evalExpr LExpr (mkConst ``LeanCert.Core.Expr) ast
      let result := LeanCert.Internal.Rational.evalTotalCore astVal env evalCfg

      logInfo m!"━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
#eval_interval Results
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  f(x) ∈ [{formatRat result.lo}, {formatRat result.hi}]
  Width: {formatRat result.width}
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
  | _ => throwUnsupportedSyntax

end LeanCert.Discovery.Commands
