/-
Copyright (c) 2024 LeanBound Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanBound Contributors
-/
import Lean
import LeanBound.Meta.ProveSupported
import LeanBound.Meta.ToExpr
import LeanBound.Numerics.Certificate

/-!
# Automated Interval Arithmetic Tactics

This file provides smart tactics that automatically:
1. Reify Lean expressions to LeanBound AST (Phase 1)
2. Generate ExprSupportedCore proofs (Phase 2)
3. Apply the appropriate verification theorem and close the goal (Phase 3)

## Main tactics

* `interval_bound` - Automatically prove bounds using interval arithmetic

## Usage

```lean
-- Automatically proves the bound
example : ∀ x ∈ I01, x * x + Real.sin x ≤ 2 := by
  interval_bound

-- With custom Taylor depth for exp
example : ∀ x ∈ I01, Real.exp x ≤ 3 := by
  interval_bound { taylorDepth := 20 }
```

## Design notes

The tactic detects the goal structure:
- `∀ x ∈ I, f x ≤ c` → uses `verify_upper_bound`
- `∀ x ∈ I, c ≤ f x` → uses `verify_lower_bound`
-/

open Lean Meta Elab Tactic Term

namespace LeanBound.Tactic.Auto

open LeanBound.Meta
open LeanBound.Core
open LeanBound.Numerics
open LeanBound.Numerics.Certificate

/-! ## Goal Analysis

Utilities for analyzing the goal structure to determine which theorem to apply.
-/

/-- Result of analyzing a bound goal -/
inductive BoundGoal where
  /-- ∀ x ∈ I, f x ≤ c -/
  | forallLe (varName : Name) (interval : Lean.Expr) (func : Lean.Expr) (bound : Lean.Expr)
  /-- ∀ x ∈ I, c ≤ f x -/
  | forallGe (varName : Name) (interval : Lean.Expr) (func : Lean.Expr) (bound : Lean.Expr)
  /-- ∀ x ∈ I, f x < c -/
  | forallLt (varName : Name) (interval : Lean.Expr) (func : Lean.Expr) (bound : Lean.Expr)
  /-- ∀ x ∈ I, c < f x -/
  | forallGt (varName : Name) (interval : Lean.Expr) (func : Lean.Expr) (bound : Lean.Expr)
  deriving Repr

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

        -- memTy should be x ∈ I (Membership.mem x I)
        -- Don't reduce with whnf as it will expand the membership definition

        -- Try to extract interval from membership
        let interval? ← extractInterval memTy x
        let some interval := interval? | return none

        -- innerBody is the comparison
        withLocalDeclD `hx memTy fun _hx => do
          let comparison := innerBody.instantiate1 _hx
          -- Don't use whnf here as it reduces LE.le to instance-specific versions

          -- Try to match LE.le, GE.ge, LT.lt, GT.gt
          -- We need to figure out which side is the function and which is the bound
          match_expr comparison with
          | LE.le _ _ lhs rhs =>
            -- lhs ≤ rhs
            -- Check which side contains the function application (depends on x)
            let lhsHasX := lhs.containsFVar x.fvarId!
            let rhsHasX := rhs.containsFVar x.fvarId!
            if lhsHasX && !rhsHasX then
              -- f(x) ≤ c → upper bound
              return some (.forallLe name interval (← mkLambdaFVars #[x] lhs) rhs)
            else if rhsHasX && !lhsHasX then
              -- c ≤ f(x) → lower bound
              return some (.forallGe name interval (← mkLambdaFVars #[x] rhs) lhs)
            else
              return none  -- Ambiguous or neither depends on x
          | GE.ge _ _ lhs rhs =>
            -- lhs ≥ rhs means rhs ≤ lhs
            let lhsHasX := lhs.containsFVar x.fvarId!
            let rhsHasX := rhs.containsFVar x.fvarId!
            if lhsHasX && !rhsHasX then
              -- f(x) ≥ c → lower bound on f
              return some (.forallGe name interval (← mkLambdaFVars #[x] lhs) rhs)
            else if rhsHasX && !lhsHasX then
              -- c ≥ f(x) → upper bound on f
              return some (.forallLe name interval (← mkLambdaFVars #[x] rhs) lhs)
            else
              return none
          | LT.lt _ _ lhs rhs =>
            let lhsHasX := lhs.containsFVar x.fvarId!
            let rhsHasX := rhs.containsFVar x.fvarId!
            if lhsHasX && !rhsHasX then
              -- f(x) < c → strict upper bound
              return some (.forallLt name interval (← mkLambdaFVars #[x] lhs) rhs)
            else if rhsHasX && !lhsHasX then
              -- c < f(x) → strict lower bound
              return some (.forallGt name interval (← mkLambdaFVars #[x] rhs) lhs)
            else
              return none
          | GT.gt _ _ lhs rhs =>
            let lhsHasX := lhs.containsFVar x.fvarId!
            let rhsHasX := rhs.containsFVar x.fvarId!
            if lhsHasX && !rhsHasX then
              -- f(x) > c → strict lower bound
              return some (.forallGt name interval (← mkLambdaFVars #[x] lhs) rhs)
            else if rhsHasX && !lhsHasX then
              -- c > f(x) → strict upper bound
              return some (.forallLt name interval (← mkLambdaFVars #[x] rhs) lhs)
            else
              return none
          | _ => return none
      else
        return none
  else
    return none

where
  /-- Extract the interval from a membership expression -/
  extractInterval (memTy : Lean.Expr) (x : Lean.Expr) : MetaM (Option Lean.Expr) := do
    -- Try direct Membership.mem match
    -- Membership.mem : {α : Type u_1} → {γ : outParam (Type u_2)} → [self : Membership α γ] → γ → α → Prop
    -- Note: The mem function takes (container, element), but notation x ∈ I displays as element ∈ container
    match_expr memTy with
    | Membership.mem _ _ _ interval xExpr =>
      -- Check if xExpr matches x (might be the same or definitionally equal)
      if ← isDefEq xExpr x then return some interval else return none
    | _ =>
      -- The memTy might be definitionally expanded - check if it's a conjunction
      -- For IntervalRat: x ∈ I unfolds to (I.lo : ℝ) ≤ x ∧ x ≤ (I.hi : ℝ)
      -- This is tricky to reverse, so let's try looking at the original unexpanded form
      return none

/-! ## Main Tactic Implementation -/

/-- The main interval_bound tactic implementation -/
def intervalBoundCore (taylorDepth : Nat) : TacticM Unit := do
  let goal ← getMainGoal
  let goalType ← goal.getType

  -- Parse the goal
  let some boundGoal ← parseBoundGoal goalType
    | do
      -- Debug: show the goal structure
      let goalWhnf ← whnf goalType
      throwError "interval_bound: Could not parse goal as a bound. Expected:\n\
                  • ∀ x ∈ I, f x ≤ c\n\
                  • ∀ x ∈ I, c ≤ f x\n\
                  • ∀ x ∈ I, f x < c\n\
                  • ∀ x ∈ I, c < f x\n\
                  \nGoal type: {goalType}\n\
                  Goal (whnf): {goalWhnf}"

  match boundGoal with
  | .forallLe _name interval func bound =>
    proveForallLe goal interval func bound taylorDepth
  | .forallGe _name interval func bound =>
    proveForallGe goal interval func bound taylorDepth
  | .forallLt _name interval func bound =>
    proveForallLt goal interval func bound taylorDepth
  | .forallGt _name interval func bound =>
    proveForallGt goal interval func bound taylorDepth

where
  /-- Try to extract the rational from a bound expression (possibly coerced to ℝ) -/
  extractRatBound (bound : Lean.Expr) : TacticM Lean.Expr := do
    -- The bound might be:
    -- 1. A direct ℚ literal
    -- 2. A coercion ↑q where q : ℚ (as Rat.cast)
    -- 3. A coercion instance application (Real.instRatCast.1 q)
    let fn := bound.getAppFn
    let args := bound.getAppArgs

    -- Check for Rat.cast (which is what ↑ becomes for ℚ → ℝ)
    if fn.isConstOf ``Rat.cast then
      -- Rat.cast inst q - the last arg is the rational
      if args.size > 0 then
        return args.back!
      else
        throwError "Unexpected Rat.cast structure"
    else
      -- Check for the RatCast.ratCast form (the actual implementation)
      if fn.isConstOf ``RatCast.ratCast then
        -- RatCast.ratCast inst q - the last arg is the rational
        if args.size > 0 then
          return args.back!
        else
          throwError "Unexpected RatCast.ratCast structure"
      else
        -- Check if the type is already ℚ
        let boundTy ← inferType bound
        if boundTy.isConstOf ``Rat then
          return bound
        else
          -- Last resort: try to see if this is a reducible form
          let boundReduced ← whnf bound
          let fnReduced := boundReduced.getAppFn
          if fnReduced.isConstOf ``Rat.cast || fnReduced.isConstOf ``RatCast.ratCast then
            let argsReduced := boundReduced.getAppArgs
            if argsReduced.size > 0 then
              return argsReduced.back!
            else
              throwError "Unexpected reduced coercion structure"
          else
            throwError "Cannot extract rational from bound: {bound} (type: {boundTy})"

  /-- Try to extract AST from an Expr.eval application, or reify if it's a raw expression -/
  getAst (func : Lean.Expr) : TacticM Lean.Expr := do
    -- func is (fun x => body) where body might be Expr.eval or a raw expression
    lambdaTelescope func fun _vars body => do
      -- Check if body is an Expr.eval application
      let fn := body.getAppFn
      if fn.isConstOf ``LeanBound.Core.Expr.eval then
        -- It's Expr.eval env ast - extract the ast
        let args := body.getAppArgs
        -- Expr.eval takes: (env : Nat → ℝ) → Expr → ℝ
        -- So args[0] is env, args[1] is ast
        if args.size ≥ 2 then
          return args[1]!
        else
          throwError "Unexpected Expr.eval application structure"
      else
        -- It's a raw expression - reify it
        reify func

  /-- Prove ∀ x ∈ I, f x ≤ c -/
  proveForallLe (goal : MVarId) (interval func bound : Lean.Expr)
      (taylorDepth : Nat) : TacticM Unit := do
    goal.withContext do
      -- 1. Get AST (either from Expr.eval or by reifying)
      let ast ← getAst func

      -- 2. Extract rational bound from possible coercion
      let boundRat ← extractRatBound bound

      -- 3. Generate support proof
      let supportProof ← mkSupportedCoreProof ast

      -- 4. Build config expression
      let cfgExpr ← mkAppM ``EvalConfig.mk #[toExpr taylorDepth]

      -- 5. Apply verify_upper_bound_smart theorem (uses monotonicity for tighter bounds)
      let proof ← mkAppM ``verify_upper_bound_smart #[ast, supportProof, interval, boundRat, cfgExpr]

      -- 6. Apply the proof - this leaves the certificate check as a goal
      let newGoals ← goal.apply proof
      setGoals newGoals

      -- 7. Solve remaining goals with native_decide
      for g in newGoals do
        setGoals [g]
        evalTactic (← `(tactic| native_decide))

  /-- Prove ∀ x ∈ I, c ≤ f x -/
  proveForallGe (goal : MVarId) (interval func bound : Lean.Expr)
      (taylorDepth : Nat) : TacticM Unit := do
    goal.withContext do
      let ast ← getAst func
      let boundRat ← extractRatBound bound
      let supportProof ← mkSupportedCoreProof ast
      let cfgExpr ← mkAppM ``EvalConfig.mk #[toExpr taylorDepth]

      -- Use smart checker with monotonicity support
      let proof ← mkAppM ``verify_lower_bound_smart #[ast, supportProof, interval, boundRat, cfgExpr]
      let newGoals ← goal.apply proof
      setGoals newGoals

      for g in newGoals do
        setGoals [g]
        evalTactic (← `(tactic| native_decide))

  /-- Prove ∀ x ∈ I, f x < c -/
  proveForallLt (goal : MVarId) (interval func bound : Lean.Expr)
      (taylorDepth : Nat) : TacticM Unit := do
    goal.withContext do
      let ast ← getAst func
      let boundRat ← extractRatBound bound
      let supportProof ← mkSupportedCoreProof ast
      let cfgExpr ← mkAppM ``EvalConfig.mk #[toExpr taylorDepth]

      let proof ← mkAppM ``verify_strict_upper_bound #[ast, supportProof, interval, boundRat, cfgExpr]
      let newGoals ← goal.apply proof
      setGoals newGoals

      for g in newGoals do
        setGoals [g]
        evalTactic (← `(tactic| native_decide))

  /-- Prove ∀ x ∈ I, c < f x -/
  proveForallGt (goal : MVarId) (interval func bound : Lean.Expr)
      (taylorDepth : Nat) : TacticM Unit := do
    goal.withContext do
      let ast ← getAst func
      let boundRat ← extractRatBound bound
      let supportProof ← mkSupportedCoreProof ast
      let cfgExpr ← mkAppM ``EvalConfig.mk #[toExpr taylorDepth]

      let proof ← mkAppM ``verify_strict_lower_bound #[ast, supportProof, interval, boundRat, cfgExpr]
      let newGoals ← goal.apply proof
      setGoals newGoals

      for g in newGoals do
        setGoals [g]
        evalTactic (← `(tactic| native_decide))

/-! ## Tactic Syntax -/

/-- The interval_bound tactic.

    Automatically proves bounds on expressions using interval arithmetic.

    Usage:
    - `interval_bound` - uses default Taylor depth of 10
    - `interval_bound 20` - uses Taylor depth of 20

    Supports goals of the form:
    - `∀ x ∈ I, f x ≤ c`
    - `∀ x ∈ I, c ≤ f x`
    - `∀ x ∈ I, f x < c`
    - `∀ x ∈ I, c < f x`
-/
elab "interval_bound" depth:(num)? : tactic => do
  let taylorDepth := match depth with
    | some n => n.getNat
    | none => 10
  intervalBoundCore taylorDepth

/-! ## Global Optimization Tactic

The `opt_bound` tactic handles goals of the form:
- `∀ ρ, Box.envMem ρ B → (∀ i, i ≥ B.length → ρ i = 0) → c ≤ Expr.eval ρ e`
- `∀ ρ, Box.envMem ρ B → (∀ i, i ≥ B.length → ρ i = 0) → Expr.eval ρ e ≤ c`

This uses global branch-and-bound optimization with optional monotonicity pruning.
-/

/-- Skip through foralls (from ≥ binder notation) to get to the final comparison -/
partial def skipForallsAux (e : Lean.Expr) : MetaM Lean.Expr := do
  let e ← whnf e
  if e.isForall then
    let .forallE _ _ body _ := e | return e
    skipForallsAux body
  else
    return e

open LeanBound.Numerics.Optimization in
/-- Result of analyzing a global bound goal -/
inductive GlobalBoundGoal where
  /-- ∀ ρ ∈ B, (zero extension) → c ≤ f(ρ) -/
  | globalGe (box : Lean.Expr) (expr : Lean.Expr) (bound : Lean.Expr)
  /-- ∀ ρ ∈ B, (zero extension) → f(ρ) ≤ c -/
  | globalLe (box : Lean.Expr) (expr : Lean.Expr) (bound : Lean.Expr)
  deriving Repr

/-- Check if expression is Expr.eval (checking both short and full names) -/
def isExprEval (e : Lean.Expr) : Bool :=
  let fn := e.getAppFn
  fn.isConstOf ``LeanBound.Core.Expr.eval || fn.isConstOf ``Expr.eval

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

open LeanBound.Numerics.Optimization in
/-- Build a GlobalOptConfig expression -/
def mkGlobalOptConfigExpr (maxIters : Nat) (tolerance : ℚ) (useMonotonicity : Bool) (taylorDepth : Nat) : MetaM Lean.Expr := do
  mkAppM ``GlobalOptConfig.mk #[toExpr maxIters, toExpr tolerance, toExpr useMonotonicity, toExpr taylorDepth]

open LeanBound.Numerics.Optimization in
/-- The main opt_bound tactic implementation -/
def optBoundCore (maxIters : Nat) (useMonotonicity : Bool) (taylorDepth : Nat) : TacticM Unit := do
  -- Apply verify_global_upper_bound or verify_global_lower_bound using plain apply
  -- Let Lean figure out the unification

  let cfgExpr ← mkGlobalOptConfigExpr maxIters ((1 : ℚ)/1000) useMonotonicity taylorDepth

  -- First try applying upper bound theorem (for f(ρ) ≤ c goals)
  let goal ← getMainGoal
  try
    let proof ← mkAppOptM ``LeanBound.Numerics.Certificate.GlobalOpt.verify_global_upper_bound
      #[none, none, none, none, some cfgExpr]
    let newGoals ← goal.apply proof
    setGoals newGoals
    -- Now prove the remaining goals: hsupp and h_cert
    let goals ← getGoals
    for g in goals do
      setGoals [g]
      let gType ← g.getType
      -- Check if this is a support goal or a decidable goal
      if gType.getAppFn.isConstOf ``ExprSupportedCore then
        -- Generate support proof
        proveSupport g
      else
        evalTactic (← `(tactic| native_decide))
    return
  catch _ => pure ()

  -- Try lower bound theorem (for c ≤ f(ρ) goals)
  let goal ← getMainGoal
  try
    let proof ← mkAppOptM ``LeanBound.Numerics.Certificate.GlobalOpt.verify_global_lower_bound
      #[none, none, none, none, some cfgExpr]
    let newGoals ← goal.apply proof
    setGoals newGoals
    let goals ← getGoals
    for g in goals do
      setGoals [g]
      let gType ← g.getType
      if gType.getAppFn.isConstOf ``ExprSupportedCore then
        proveSupport g
      else
        evalTactic (← `(tactic| native_decide))
    return
  catch _ => pure ()

  throwError "opt_bound: Could not apply global bound theorem. Check that goal has form:\n\
              • ∀ ρ, Box.envMem ρ B → (∀ i ≥ B.length, ρ i = 0) → c ≤ Expr.eval ρ e\n\
              • ∀ ρ, Box.envMem ρ B → (∀ i ≥ B.length, ρ i = 0) → Expr.eval ρ e ≤ c"

where
  /-- Prove ExprSupportedCore goal by generating the proof -/
  proveSupport (goal : MVarId) : TacticM Unit := do
    goal.withContext do
      let gType ← goal.getType
      -- gType should be ExprSupportedCore e for some e
      let args := gType.getAppArgs
      if args.size ≥ 1 then
        let expr := args[0]!
        let proof ← mkSupportedCoreProof expr
        goal.assign proof

/-- The opt_bound tactic.

    Automatically proves global bounds on expressions over boxes using
    branch-and-bound optimization.

    Usage:
    - `opt_bound` - uses defaults (1000 iterations, no monotonicity, Taylor depth 10)
    - `opt_bound 2000` - uses 2000 iterations
    - `opt_bound 1000 mono` - enables monotonicity pruning

    Supports goals of the form:
    - `∀ ρ, Box.envMem ρ B → (∀ i, i ≥ B.length → ρ i = 0) → c ≤ Expr.eval ρ e`
    - `∀ ρ, Box.envMem ρ B → (∀ i, i ≥ B.length → ρ i = 0) → Expr.eval ρ e ≤ c`
-/
elab "opt_bound" iters:(num)? mono:("mono")? : tactic => do
  let maxIters := match iters with
    | some n => n.getNat
    | none => 1000
  let useMonotonicity := mono.isSome
  optBoundCore maxIters useMonotonicity 10

/-! ## Root Finding Tactic

The `root_bound` tactic handles goals related to root finding:
- `∀ x ∈ I, f x ≠ 0` (no root exists) - uses verify_no_root
-/

/-- Result of analyzing a root finding goal -/
inductive RootGoal where
  /-- ∀ x ∈ I, f x ≠ 0 -/
  | forallNeZero (varName : Name) (interval : Lean.Expr) (func : Lean.Expr)
  deriving Repr

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
  /-- Extract the interval from a membership expression -/
  extractInterval (memTy : Lean.Expr) (x : Lean.Expr) : MetaM (Option Lean.Expr) := do
    match_expr memTy with
    | Membership.mem _ _ _ interval xExpr =>
      if ← isDefEq xExpr x then return some interval else return none
    | _ => return none

/-- The main root_bound tactic implementation -/
def rootBoundCore (taylorDepth : Nat) : TacticM Unit := do
  let goal ← getMainGoal
  let goalType ← goal.getType

  -- Parse the goal
  let some rootGoal ← parseRootGoal goalType
    | do
      let goalWhnf ← whnf goalType
      throwError "root_bound: Could not parse goal as a root goal. Expected:\n\
                  • ∀ x ∈ I, f x ≠ 0\n\
                  \nGoal type: {goalType}\n\
                  Goal (whnf): {goalWhnf}"

  match rootGoal with
  | .forallNeZero _name interval func =>
    proveForallNeZero goal interval func taylorDepth

where
  /-- Try to extract AST from an Expr.eval application, or reify if it's a raw expression -/
  getAst (func : Lean.Expr) : TacticM Lean.Expr := do
    lambdaTelescope func fun _vars body => do
      let fn := body.getAppFn
      if fn.isConstOf ``LeanBound.Core.Expr.eval then
        let args := body.getAppArgs
        if args.size ≥ 2 then
          return args[1]!
        else
          throwError "Unexpected Expr.eval application structure"
      else
        reify func

  /-- Prove ∀ x ∈ I, f x ≠ 0 using verify_no_root -/
  proveForallNeZero (goal : MVarId) (interval func : Lean.Expr)
      (taylorDepth : Nat) : TacticM Unit := do
    goal.withContext do
      -- 1. Get AST
      let ast ← getAst func

      -- 2. Generate ExprSupportedCore proof
      let supportProof ← mkSupportedCoreProof ast

      -- 3. Build config expression
      let cfgExpr ← mkAppM ``EvalConfig.mk #[toExpr taylorDepth]

      -- 4. Apply verify_no_root theorem
      let proof ← mkAppM ``Certificate.RootFinding.verify_no_root
        #[ast, supportProof, interval, cfgExpr]

      -- 5. Apply the proof - this leaves the certificate check as a goal
      let newGoals ← goal.apply proof

      setGoals newGoals

      -- 6. Solve remaining goals with native_decide
      for g in newGoals do
        setGoals [g]
        evalTactic (← `(tactic| native_decide))

/-- The root_bound tactic.

    Automatically proves root-related properties using interval arithmetic.

    Usage:
    - `root_bound` - uses default Taylor depth of 10
    - `root_bound 20` - uses Taylor depth of 20

    Supports goals of the form:
    - `∀ x ∈ I, f x ≠ 0` (proves no root exists in interval)
-/
elab "root_bound" depth:(num)? : tactic => do
  let taylorDepth := match depth with
    | some n => n.getNat
    | none => 10
  rootBoundCore taylorDepth

end LeanBound.Tactic.Auto
