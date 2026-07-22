/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import Lean
import LeanCert.Engine.FinSumDyadic
import LeanCert.Meta.ToExpr
import LeanCert.Meta.ProveSupported
import LeanCert.Tactic.IntervalAuto
import LeanCert.Tactic.FinsetParse
import LeanCert.Tactic.FinSumWitness
import LeanCert.Tactic.BridgeNative
import Mathlib.Algebra.BigOperators.Fin

/-!
# `finsum_bound`: O(1) Proof-Size Tactic for Finite Sum Bounds

Proves bounds of the form `∑ k ∈ S, f k ≤ target` (or `≥`)
using `native_decide` with O(1) proof size, regardless of the number of terms.

Supports `Finset.Icc`, `Ico`, `Ioc`, `Ioo`, `range`, explicit sets `{a,b,c}`,
and `∑ i : Fin n, f ↑i` (auto-rewrites to `Finset.range`).

## Motivation

`finsum_expand` expands sums symbolically, creating O(N) proof terms that blow up
for N > ~100. `finsum_bound` uses an accumulator-based evaluator over `Core.Expr`
with `native_decide`, keeping proof size constant.

## Usage

```lean
-- Upper bound on harmonic-like sum
example : ∑ k ∈ Finset.Icc 1 100, (1 : ℝ) / (k * k) ≤ 2 := by
  finsum_bound

-- Lower bound
example : (4 : ℝ) ≤ ∑ k ∈ Finset.Icc 1 100, 1 / k := by
  finsum_bound

-- Fin n sums (auto-rewritten to Finset.range)
example : ∑ i : Fin 5, Real.exp (↑i : ℝ) ≤ 234 := by
  finsum_bound

-- Higher precision
example : ∑ k ∈ Finset.Icc 1 500, (1 : ℝ) / (k * k) ≤ 2 := by
  finsum_bound 100

-- Witness mode with auto-proved membership
example : ∑ _k ∈ Finset.Icc 1 5, (1 : ℝ) ≤ 6 := by
  finsum_bound auto constOneEval
```

## Architecture

```
(Fin n rewrite) → Parse goal → reify body (ℕ → ℝ) to Core.Expr
  → select the checked Dyadic evaluation path
  → build DyadicConfig
  → checkFinSumUpperBoundFull/LowerBoundFull : Bool (domain + bound)
  → native_decide
  → verify_finsum_upper_full/lower_full (bridge theorem)
```
-/

open Lean Meta Elab Tactic Term

namespace LeanCert.Tactic

open LeanCert.Meta
open LeanCert.Core
open LeanCert.Engine

initialize registerTraceClass `finsum_bound

/-! ## Goal Parsing -/

/-- Result of parsing a finite sum bound goal. -/
structure FinSumGoal where
  /-- Lower range bound (ℕ expression) -/
  aExpr : Lean.Expr
  /-- Upper range bound (ℕ expression) -/
  bExpr : Lean.Expr
  /-- Sum body as lambda (ℕ → ℝ) -/
  bodyLambda : Lean.Expr
  /-- Bound target (ℝ expression) -/
  targetExpr : Lean.Expr
  /-- true for `sum ≤ target`, false for `target ≤ sum` -/
  isUpper : Bool

/-- Parse a goal of the form `∑ k ∈ Finset.Icc a b, f k ≤ target`
    or `target ≤ ∑ k ∈ Finset.Icc a b, f k`. -/
def parseFinSumGoal (goalType : Lean.Expr) : Option FinSumGoal := do
  -- Match LE.le _ _ lhs rhs
  let_expr LE.le _ _ lhs rhs := goalType | none
  -- Check if lhs is a Finset.Icc sum
  if let some (a, b, f) := extractFinsetIccSum lhs then
    return { aExpr := a, bExpr := b, bodyLambda := f, targetExpr := rhs, isUpper := true }
  -- Check if rhs is a Finset.Icc sum
  if let some (a, b, f) := extractFinsetIccSum rhs then
    return { aExpr := a, bExpr := b, bodyLambda := f, targetExpr := lhs, isUpper := false }
  none

/-! ## Generalized Finset Parsing (List Path) -/

/-- Result of parsing a finite sum bound goal over an arbitrary Finset. -/
structure FinSumGoalList where
  /-- The Finset expression from the goal -/
  finsetExpr : Lean.Expr
  /-- The List Nat literal of elements -/
  indicesExpr : Lean.Expr
  /-- Sum body as lambda (ℕ → ℝ) -/
  bodyLambda : Lean.Expr
  /-- Bound target (ℝ expression) -/
  targetExpr : Lean.Expr
  /-- true for `sum ≤ target`, false for `target ≤ sum` -/
  isUpper : Bool

/-- Parse a goal for the list path: ∑ k ∈ S, f k ≤ target (any Finset S). -/
def parseFinSumGoalList (goalType : Lean.Expr) : MetaM (Option FinSumGoalList) := do
  let_expr LE.le _ _ lhs rhs := goalType | return none
  let tryExtract (sumSide otherSide : Lean.Expr) (isUpper : Bool) :
      MetaM (Option FinSumGoalList) := do
    if let some (finsetExpr, bodyLambda) := extractFinsetSum sumSide then
      if let some indices := ← extractFinsetElements finsetExpr then
        let indicesExpr := toExpr indices
        return some { finsetExpr, indicesExpr, bodyLambda, targetExpr := otherSide, isUpper }
    return none
  if let some g := ← tryExtract lhs rhs true then return some g
  if let some g := ← tryExtract rhs lhs false then return some g
  return none

/-! ## Body Reification -/

/-- Check if an expression is `k` or `Fin.val k` (or similar coercions) for the given fvar. -/
private def isFVarOrFinVal (e : Lean.Expr) (kFVarId : FVarId) : Bool :=
  if e.isFVar && e.fvarId! == kFVarId then true
  else
    -- Check for Fin.val k / Fin.toNat k
    let fn := e.getAppFn
    let args := e.getAppArgs
    if args.size ≥ 1 then
      let lastArg := args.back!
      lastArg.isFVar && lastArg.fvarId! == kFVarId &&
        (fn.isConstOf ``Fin.val || fn.isConstOf ``Fin.toNat)
    else false

/-- Build a real numeral expression. -/
private def mkRealNatLit (n : Nat) : MetaM Lean.Expr :=
  mkAppOptM ``OfNat.ofNat #[some (mkConst ``Real), some (mkNatLit n), none]

/-- Build a real addition expression. -/
private def mkRealAdd (a b : Lean.Expr) : MetaM Lean.Expr :=
  mkAppM ``HAdd.hAdd #[a, b]

/-- Build a real multiplication expression. -/
private def mkRealMul (a b : Lean.Expr) : MetaM Lean.Expr :=
  mkAppM ``HMul.hMul #[a, b]

/-- Last two arguments of an application, if present. -/
private def lastTwoArgs? (args : Array Lean.Expr) : Option (Lean.Expr × Lean.Expr) :=
  if _h : args.size ≥ 2 then
    some (args[args.size - 2]!, args[args.size - 1]!)
  else
    none

/-- Translate simple Nat index expressions to real expressions in a fresh variable.

This supports the semiring-homomorphic fragment used by generated finite-sum
tables: `k`, `Fin.val k`, Nat literals, `k + c`, `c + k`, and products such as
`2 * k`. It intentionally does not translate Nat subtraction, since
`Nat.cast (k - c)` needs a side condition. -/
private partial def reifyNatIndexExprAsReal?
    (natExpr : Lean.Expr) (kFVarId : FVarId) (x : Lean.Expr) : MetaM (Option Lean.Expr) := do
  if isFVarOrFinVal natExpr kFVarId then
    return some x
  if let some n := ← extractNatLit natExpr then
    return some (← mkRealNatLit n)
  let fn := natExpr.getAppFn
  let args := natExpr.getAppArgs
  if fn.isConstOf ``Nat.succ && args.size ≥ 1 then
    if let some e ← reifyNatIndexExprAsReal? args.back! kFVarId x then
      return some (← mkRealAdd e (← mkRealNatLit 1))
  if (fn.isConstOf ``HAdd.hAdd || fn.isConstOf ``Nat.add) then
    if let some (a, b) := lastTwoArgs? args then
      match ← reifyNatIndexExprAsReal? a kFVarId x,
          ← reifyNatIndexExprAsReal? b kFVarId x with
      | some ar, some br => return some (← mkRealAdd ar br)
      | _, _ => return none
  if (fn.isConstOf ``HMul.hMul || fn.isConstOf ``Nat.mul) then
    if let some (a, b) := lastTwoArgs? args then
      match ← reifyNatIndexExprAsReal? a kFVarId x,
          ← reifyNatIndexExprAsReal? b kFVarId x with
      | some ar, some br => return some (← mkRealMul ar br)
      | _, _ => return none
  return none

/-- Extract the Nat argument from a Nat-cast application. -/
private def natCastArg? (e : Lean.Expr) : Option Lean.Expr :=
  let fn := e.getAppFn
  let args := e.getAppArgs
  if args.size ≥ 1 && (fn.isConstOf ``Nat.cast || fn.isConstOf ``NatCast.natCast) then
    some args.back!
  else
    none

/-- Replace occurrences of `Nat.cast` applied to simple index expressions with
    a real expression in the fresh real variable. Also handles `Nat.cast (Fin.val k)`
    for Fin-indexed sums. -/
private partial def replaceNatCast (body : Lean.Expr) (kFVarId : FVarId)
    (replacement : Lean.Expr) : MetaM Lean.Expr := do
  if let some natArg := natCastArg? body then
    if let some realExpr ← reifyNatIndexExprAsReal? natArg kFVarId replacement then
      return realExpr
  match body with
  | .app f a =>
      return .app (← replaceNatCast f kFVarId replacement)
        (← replaceNatCast a kFVarId replacement)
  | .mdata d e =>
      return .mdata d (← replaceNatCast e kFVarId replacement)
  | .proj s i e =>
      return .proj s i (← replaceNatCast e kFVarId replacement)
  | .letE n t v b nondep =>
      return .letE n t (← replaceNatCast v kFVarId replacement)
        (← replaceNatCast b kFVarId replacement) nondep
  | .lam n t b bi =>
      return .lam n t (← replaceNatCast b kFVarId replacement) bi
  | .forallE n t b bi =>
      return .forallE n t (← replaceNatCast b kFVarId replacement) bi
  | _ => return body

/-- Pure fast path used by Fin-sum rewriting over `Fin n`. -/
private def replaceNatVarPure (body : Lean.Expr) (kFVarId : FVarId)
    (replacement : Lean.Expr) : Lean.Expr :=
  body.replace fun e =>
    let fn := e.getAppFn
    let args := e.getAppArgs
    if args.size ≥ 1 then
      let lastArg := args.back!
      if lastArg.isFVar && lastArg.fvarId! == kFVarId then
        if fn.isConstOf ``Fin.val || fn.isConstOf ``Fin.toNat then
          some replacement
        else none
      else none
    else none

/-- Reify a sum body lambda `(ℕ → ℝ)` to a `Core.Expr` AST.
    Replaces `Nat.cast k` with a real variable, then reifies. -/
private def reifyFinSumBody (bodyLambda : Lean.Expr) : MetaM Lean.Expr := do
  lambdaTelescope bodyLambda fun vars body => do
    if vars.size < 1 then
      throwError "finsum_bound: expected a lambda for the sum body"
    let k := vars[0]!
    let realTy := Lean.mkConst ``Real
    withLocalDeclD `_x realTy fun x => do
      -- Replace Nat.cast of simple index expressions, e.g. `↑k`, `↑(k+1)`,
      -- and `↑(2*k)`, with real expressions in x.
      let body' ← replaceNatCast body k.fvarId! x
      let realLambda ← mkLambdaFVars #[x] body'
      reify realLambda

/-! ## Tactic Kernel -/

/-- Core implementation of `finsum_bound` for Finset.Icc goals. -/
private def finSumBoundIccCore (fsGoal : FinSumGoal) (prec : Int) (taylorDepth : Nat) : TacticM Unit := do
  let goal ← getMainGoal
  let goalType ← goal.getType

  goal.withContext do
    -- Extract target as rational
    let some target ← Auto.extractRatFromReal fsGoal.targetExpr
      | throwError "finsum_bound: could not extract rational from bound `{← ppExpr fsGoal.targetExpr}`"
    let targetExpr := toExpr target

    -- Reify the sum body
    let ast ← reifyFinSumBody fsGoal.bodyLambda
    trace[finsum_bound] "Reified AST: {ast}"

    -- Build configuration
    let precExpr := toExpr prec
    let depthExpr := toExpr taylorDepth
    let cfgExpr ← mkAppM ``DyadicConfig.mk #[precExpr, depthExpr]

    -- Precision proof: prec ≤ 0
    let precLeZeroTy ← mkAppM ``LE.le #[precExpr, toExpr (0 : Int)]
    let precLeZeroProof ← mkDecideProof precLeZeroTy

    -- Build the combined certificate check expression (domain + bound in one check)
    let checkExpr ← if fsGoal.isUpper then
      mkAppM ``checkFinSumUpperBoundFull #[ast, fsGoal.aExpr, fsGoal.bExpr, targetExpr, cfgExpr]
    else
      mkAppM ``checkFinSumLowerBoundFull #[ast, fsGoal.aExpr, fsGoal.bExpr, targetExpr, cfgExpr]

    let checkEqTrue ← mkAppM ``Eq #[checkExpr, Lean.mkConst ``Bool.true]
    let checkMVar ← mkFreshExprMVar (some checkEqTrue) (kind := .syntheticOpaque)

    let bridgeThm := if fsGoal.isUpper then
      ``verify_finsum_upper_full_checked
    else
      ``verify_finsum_lower_full_checked

    -- Build bridge theorem proof (no domain proof needed — it's in the checker)
    let proof ← mkAppM bridgeThm
      #[ast, fsGoal.aExpr, fsGoal.bExpr, targetExpr, cfgExpr,
        precLeZeroProof, checkMVar]

    -- Apply bridge + native_decide (with converter fallback)
    closeBridgeWithNativeDecide goal goalType proof checkMVar "finsum_bound" #[
      do evalTactic (← `(tactic|
        intro h; norm_num [LeanCert.Core.Expr.eval, LeanCert.Engine.sumBodyRealEnv,
          div_eq_mul_inv, ← LeanCert.Core.Expr.sqrt_mul_self_eq_abs] at h ⊢; done)),
      do evalTactic (← `(tactic|
        intro h; simp only [LeanCert.Core.Expr.eval, LeanCert.Engine.sumBodyRealEnv,
          div_eq_mul_inv, ← LeanCert.Core.Expr.sqrt_mul_self_eq_abs] at h ⊢;
        norm_num at h ⊢; exact h)),
      do evalTactic (← `(tactic|
        intro h; simp only [LeanCert.Core.Expr.eval, LeanCert.Engine.sumBodyRealEnv,
          div_eq_mul_inv, ← LeanCert.Core.Expr.sqrt_mul_self_eq_abs] at h ⊢;
        push_cast at h ⊢; linarith))
    ]

/-- Core implementation of `finsum_bound` for arbitrary Finsets (list path). -/
private def finSumBoundListCore (fsGoal : FinSumGoalList) (prec : Int) (taylorDepth : Nat) : TacticM Unit := do
  let goal ← getMainGoal
  let goalType ← goal.getType

  goal.withContext do
    -- Extract target as rational
    let some target ← Auto.extractRatFromReal fsGoal.targetExpr
      | throwError "finsum_bound: could not extract rational from bound `{← ppExpr fsGoal.targetExpr}`"
    let targetExpr := toExpr target

    -- Reify the sum body
    let ast ← reifyFinSumBody fsGoal.bodyLambda
    trace[finsum_bound] "Reified AST (list path): {ast}"

    -- Build configuration
    let precExpr := toExpr prec
    let depthExpr := toExpr taylorDepth
    let cfgExpr ← mkAppM ``DyadicConfig.mk #[precExpr, depthExpr]

    -- Precision proof
    let precLeZeroTy ← mkAppM ``LE.le #[precExpr, toExpr (0 : Int)]
    let precLeZeroProof ← mkDecideProof precLeZeroTy

    -- Build the combined certificate check (S = indices.toFinset ∧ Nodup ∧ domain ∧ bound)
    let checkExpr ← if fsGoal.isUpper then
      mkAppM ``checkFinSumUpperBoundListFull
        #[ast, fsGoal.finsetExpr, fsGoal.indicesExpr, targetExpr, cfgExpr]
    else
      mkAppM ``checkFinSumLowerBoundListFull
        #[ast, fsGoal.finsetExpr, fsGoal.indicesExpr, targetExpr, cfgExpr]

    let checkEqTrue ← mkAppM ``Eq #[checkExpr, Lean.mkConst ``Bool.true]
    let checkMVar ← mkFreshExprMVar (some checkEqTrue) (kind := .syntheticOpaque)

    let bridgeThm := if fsGoal.isUpper then
      ``verify_finsum_upper_list_full_checked
    else
      ``verify_finsum_lower_list_full_checked

    -- Build bridge proof
    let proof ← mkAppM bridgeThm
      #[ast, fsGoal.finsetExpr, fsGoal.indicesExpr, targetExpr, cfgExpr,
        precLeZeroProof, checkMVar]

    -- Apply bridge + native_decide (with converter fallback)
    closeBridgeWithNativeDecide goal goalType proof checkMVar "finsum_bound" #[
      do evalTactic (← `(tactic|
        intro h; norm_num [LeanCert.Core.Expr.eval, LeanCert.Engine.sumBodyRealEnv,
          div_eq_mul_inv, ← LeanCert.Core.Expr.sqrt_mul_self_eq_abs] at h ⊢; done)),
      do evalTactic (← `(tactic|
        intro h; simp only [LeanCert.Core.Expr.eval, LeanCert.Engine.sumBodyRealEnv,
          div_eq_mul_inv, ← LeanCert.Core.Expr.sqrt_mul_self_eq_abs] at h ⊢;
        norm_num at h ⊢; exact h)),
      do evalTactic (← `(tactic|
        intro h; simp only [LeanCert.Core.Expr.eval, LeanCert.Engine.sumBodyRealEnv,
          div_eq_mul_inv, ← LeanCert.Core.Expr.sqrt_mul_self_eq_abs] at h ⊢;
        push_cast at h ⊢; linarith))
    ]

/-- Try to detect `Finset.sum Finset.univ f` where `univ` is over `Fin n` in the goal,
    and rewrite using `Fin.sum_univ_eq_sum_range f` to convert to a `Finset.range` sum.
    Unlike `simp only [Fin.sum_univ_eq_sum_range]`, this handles arbitrary bodies
    by explicitly providing the function argument `f`. -/
private def tryRewriteFinSum : TacticM Unit := do
  let goal ← getMainGoal
  let goalType ← goal.getType
  let_expr LE.le _ _ lhs rhs := goalType | return
  -- Check both sides for a Fin sum
  let findFinSum (e : Lean.Expr) : Option Lean.Expr := do
    let fn := e.getAppFn
    let args := e.getAppArgs
    if fn.isConstOf ``Finset.sum && args.size ≥ 5 then
      let s := args[3]!  -- the Finset
      let f := args[4]!  -- the body
      let sfn := s.getAppFn
      if sfn.isConstOf ``Finset.univ then
        let sargs := s.getAppArgs
        let typeArg := sargs[0]!  -- should be Fin n
        if typeArg.isAppOf ``Fin then
          return f
    none
  let bodyOpt := findFinSum lhs <|> findFinSum rhs
  let some body := bodyOpt | return
  -- body : Fin n → β. We need f : ℕ → β such that body i = f (Fin.val i).
  -- Extract by: lambdaTelescope body, replace Fin.val i with fresh ℕ var.
  let f ← lambdaTelescope body fun vars innerBody => do
    if vars.size < 1 then return body
    let finVar := vars[0]!
    let natTy := Lean.mkConst ``Nat
    withLocalDeclD `k natTy fun k => do
      -- Replace all occurrences of Fin.val finVar (and the composed Fin→ℕ coercion)
      -- with k
      let body' := replaceNatVarPure innerBody finVar.fvarId! k
      mkLambdaFVars #[k] body'
  -- Rewrite: rw [Fin.sum_univ_eq_sum_range f]
  let rwLemma ← mkAppM ``Fin.sum_univ_eq_sum_range #[f]
  let result ← goal.rewrite goalType rwLemma
  let newGoal ← goal.replaceTargetEq result.eNew result.eqProof
  replaceMainGoal (newGoal :: result.mvarIds)

/-- Main dispatch: try Icc path first, then list path. -/
def finSumBoundCore (prec : Int) (taylorDepth : Nat) : TacticM Unit := do
  let goal ← getMainGoal
  let goalType ← goal.getType
  -- Try Icc path first (faster, no Nodup check needed)
  if let some iccGoal := parseFinSumGoal goalType then
    finSumBoundIccCore iccGoal prec taylorDepth
    return
  -- Fall back to general list path
  if let some listGoal := ← parseFinSumGoalList goalType then
    finSumBoundListCore listGoal prec taylorDepth
    return
  throwError "finsum_bound: goal is not of the form \
    `∑ k ∈ S, f k ≤ target` or `target ≤ ∑ k ∈ S, f k` \
    where S is a recognized Finset (Icc, Ico, Ioc, Ioo, range, or explicit)"

/-- Whether `goalType` is a finite-sum bound understood by `finsum_bound`. -/
def isFinSumBoundGoal (goalType : Lean.Expr) : MetaM Bool := do
  if (parseFinSumGoal goalType).isSome then
    return true
  return (← parseFinSumGoalList goalType).isSome

/-! ## Main Tactic -/

/-- Prove bounds on finite sums with O(1) proof size.

    Handles goals:
    - `∑ k ∈ Finset.Icc a b, f k ≤ target` (and Ico, Ioc, Ioo, range, {a,b,c})
    - `∑ i : Fin n, f i ≤ target` (auto-rewrites to `Finset.range` via `tryRewriteFinSum`)
    - `target ≤ ∑ k ∈ S, f k`

    Usage:
    - `finsum_bound` — auto-reify, default 53-bit precision
    - `finsum_bound 80` — auto-reify, 80-bit precision
    - `finsum_bound using myEval (fun k _ _ => myProof k _)` — witness mode
    - `finsum_bound using myEval myProof 100` — witness mode, 100-bit precision
    - `finsum_bound auto myEval` — witness mode, auto-prove membership
    - `finsum_bound auto myEval 80` — auto-hmem, 80-bit precision -/
syntax (name := finSumBound) "finsum_bound" ("using" term:max term:max)? (num)? : tactic
syntax (name := finSumBoundAuto) "finsum_bound" "auto" term:max (num)? : tactic

elab_rules : tactic
  | `(tactic| finsum_bound using $evalTerm:term $hmem:term $[$prec:num]?) => do
    let precision : Int := match prec with
      | some n => -(n.getNat : Int)
      | none => -53
    -- Try rewriting Fin n sums to Finset.range before witness dispatch
    try tryRewriteFinSum catch _ => pure ()
    finSumWitnessCore evalTerm hmem precision
  | `(tactic| finsum_bound $[$prec:num]?) => do
    let precision : Int := match prec with
      | some n => -(n.getNat : Int)
      | none => -53
    -- Try rewriting Fin n sums to Finset.range before main dispatch
    try tryRewriteFinSum catch _ => pure ()
    finSumBoundCore precision 10
  | `(tactic| finsum_bound auto $evalTerm:term $[$prec:num]?) => do
    let precision : Int := match prec with
      | some n => -(n.getNat : Int)
      | none => -53
    try tryRewriteFinSum catch _ => pure ()
    finSumWitnessAutoCore evalTerm precision

end LeanCert.Tactic
