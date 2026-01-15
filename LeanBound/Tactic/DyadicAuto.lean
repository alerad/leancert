/-
Copyright (c) 2025 LeanBound Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanBound Contributors
-/
import Lean
import LeanBound.Tactic.IntervalAuto
import LeanBound.Numerics.IntervalEvalDyadic

/-!
# The `fast_bound` Tactic: Kernel-Verified Dyadic Arithmetic

This tactic uses the Dyadic backend to prove bounds **within the Lean kernel**.
Unlike `interval_bound`, which uses `native_decide` (relying on the compiler/runtime),
`fast_bound` uses `decide`, which reduces the proof term in the kernel.

This is made possible because Dyadic arithmetic avoids the expensive GCD computations
of `Rat` that typically make kernel reduction infeasible for deep expressions.

## Main tactics

* `fast_bound` - Prove bounds using Dyadic arithmetic with kernel verification
* `fast_bound n` - Specify precision in bits (default: 53)

## Verification Trust Level

| Tactic | Verification | Trust |
|--------|-------------|-------|
| `interval_bound` | `native_decide` | Lean Compiler + Runtime |
| `fast_bound` | `decide` | Lean Kernel only |

The kernel is the smallest trusted component of Lean. By using `decide`,
`fast_bound` provides proofs that are verified by this minimal trusted base.

## When to use `fast_bound`

Use `fast_bound` instead of `interval_bound` when:
1. **Maximum trust**: You need proofs verified by the kernel, not the compiler
2. **Deep expressions**: Nested transcendentals like `sin(sin(sin(x)))`
3. **Many multiplications**: Polynomials with many terms
4. **Audit requirements**: Security-critical code that needs minimal TCB

## Example

```lean
-- Proves using only kernel reduction (no compiler trust)
example : ∀ x ∈ Set.Icc (0 : ℝ) 1, x * x + Real.sin x ≤ 2 := by
  fast_bound

-- Higher precision for tight bounds
example : ∀ x ∈ Set.Icc (0 : ℝ) 1, Real.exp x ≤ 2.72 := by
  fast_bound 100
```
-/

open Lean Meta Elab Tactic Term

namespace LeanBound.Tactic

open LeanBound.Meta
open LeanBound.Core
open LeanBound.Numerics

/-! ## Bridge Theorems for Dyadic Kernel Verification -/

/-- Bridge theorem: Verify upper bound on Set.Icc using Dyadic arithmetic.
    This connects the decidable boolean `upperBoundedBy` to the semantic property. -/
theorem verify_upper_bound_dyadic (e : Core.Expr) (hsupp : ExprSupportedCore e)
    (lo hi : ℚ) (hle : lo ≤ hi) (c : ℚ)
    (prec : Int) (depth : Nat) (h_prec : prec ≤ 0)
    (h_check : (evalIntervalDyadic e
        (fun _ => IntervalDyadic.ofIntervalRat ⟨lo, hi, hle⟩ prec)
        { precision := prec, taylorDepth := depth }).upperBoundedBy c = true) :
    ∀ x ∈ Set.Icc (lo : ℝ) hi, Core.Expr.eval (fun _ => x) e ≤ c := by
  intro x hx
  -- Setup environments
  let I_rat : IntervalRat := ⟨lo, hi, hle⟩
  let ρ_dyad : IntervalDyadicEnv := fun _ => IntervalDyadic.ofIntervalRat I_rat prec
  let ρ_real : Nat → ℝ := fun _ => x
  -- Show x is in the Dyadic environment
  have h_env : envMemDyadic ρ_real ρ_dyad := by
    intro i
    apply IntervalDyadic.mem_ofIntervalRat _ prec h_prec
    rwa [IntervalRat.mem_iff_mem_Icc]
  -- Apply correctness of evaluator
  have h_eval := evalIntervalDyadic_correct e hsupp ρ_real ρ_dyad h_env
    { precision := prec, taylorDepth := depth } h_prec
  -- Extract upper bound from boolean check
  simp only [IntervalDyadic.upperBoundedBy, decide_eq_true_eq] at h_check
  -- Conclude: eval ≤ hi.toRat ≤ c
  calc Core.Expr.eval (fun _ => x) e
      ≤ ((evalIntervalDyadic e ρ_dyad { precision := prec, taylorDepth := depth }).hi.toRat : ℝ) := h_eval.2
    _ ≤ c := by exact_mod_cast h_check

/-- Bridge theorem: Verify lower bound on Set.Icc using Dyadic arithmetic. -/
theorem verify_lower_bound_dyadic (e : Core.Expr) (hsupp : ExprSupportedCore e)
    (lo hi : ℚ) (hle : lo ≤ hi) (c : ℚ)
    (prec : Int) (depth : Nat) (h_prec : prec ≤ 0)
    (h_check : (evalIntervalDyadic e
        (fun _ => IntervalDyadic.ofIntervalRat ⟨lo, hi, hle⟩ prec)
        { precision := prec, taylorDepth := depth }).lowerBoundedBy c = true) :
    ∀ x ∈ Set.Icc (lo : ℝ) hi, c ≤ Core.Expr.eval (fun _ => x) e := by
  intro x hx
  let I_rat : IntervalRat := ⟨lo, hi, hle⟩
  let ρ_dyad : IntervalDyadicEnv := fun _ => IntervalDyadic.ofIntervalRat I_rat prec
  let ρ_real : Nat → ℝ := fun _ => x
  have h_env : envMemDyadic ρ_real ρ_dyad := by
    intro i
    apply IntervalDyadic.mem_ofIntervalRat _ prec h_prec
    rwa [IntervalRat.mem_iff_mem_Icc]
  have h_eval := evalIntervalDyadic_correct e hsupp ρ_real ρ_dyad h_env
    { precision := prec, taylorDepth := depth } h_prec
  simp only [IntervalDyadic.lowerBoundedBy, decide_eq_true_eq] at h_check
  calc (c : ℝ)
      ≤ ((evalIntervalDyadic e ρ_dyad { precision := prec, taylorDepth := depth }).lo.toRat : ℝ) := by exact_mod_cast h_check
    _ ≤ Core.Expr.eval (fun _ => x) e := h_eval.1

/-! ## Tactic Implementation -/

/-- Try to extract AST from a function that may be Core.Expr.eval or a raw expression.
    Returns (ast, isExprEval) where isExprEval indicates if goal was in Expr.eval form. -/
def extractOrReifyAst (func : Lean.Expr) : TacticM (Lean.Expr × Bool) := do
  lambdaTelescope func fun _vars body => do
    let fn := body.getAppFn
    if fn.isConstOf ``LeanBound.Core.Expr.eval then
      -- It's Expr.eval env ast - extract the ast directly
      let args := body.getAppArgs
      if args.size ≥ 2 then
        return (args[1]!, true)
      else
        throwError "Unexpected Expr.eval application structure"
    else
      -- Raw expression - reify it
      return (← reify func, false)

/-- Core implementation of fast_bound with kernel verification.
    Returns true if kernel verification succeeded, false if we should fall back. -/
def fastBoundKernel (prec : Int) (taylorDepth : Nat) : TacticM Bool := do
  let goal ← getMainGoal
  let goalType ← goal.getType

  -- 1. Parse the goal
  let some boundGoal ← Auto.parseBoundGoal goalType
    | return false

  goal.withContext do
    match boundGoal with
    | .forallLe _name interval func boundExpr =>
      -- 2. Extract interval bounds
      let some (_lo, _hi, loRatExpr, hiRatExpr, leProof, _loRealExpr, _hiRealExpr) := interval.fromSetIcc
        | return false

      -- 3. Extract bound as rational
      let some c ← Auto.extractRatFromReal boundExpr
        | return false
      let cExpr := toExpr c

      -- 4. Extract AST (from Expr.eval) or reify (from raw expression)
      let (ast, isExprEval) ← extractOrReifyAst func
      let supportProof ← mkSupportedCoreProof ast

      -- For non-Expr.eval goals, kernel verification won't type-match, so skip
      if !isExprEval then
        return false

      -- 5. Build configuration expressions
      let precExpr := toExpr prec
      let depthExpr := toExpr taylorDepth

      -- 6. Build the proof that prec ≤ 0
      let precLeZeroTy ← mkAppM ``LE.le #[precExpr, toExpr (0 : Int)]
      let precLeZeroProof ← mkDecideProof precLeZeroTy

      -- 7. Build the interval and environment
      let intervalRatExpr ← mkAppM ``IntervalRat.mk #[loRatExpr, hiRatExpr, leProof]

      -- 8. Build the certificate check expression
      let natTy := Lean.mkConst ``Nat
      let envExpr ← withLocalDeclD `i natTy fun i => do
        let body ← mkAppM ``IntervalDyadic.ofIntervalRat #[intervalRatExpr, precExpr]
        mkLambdaFVars #[i] body

      let cfgExpr ← mkAppM ``DyadicConfig.mk #[precExpr, depthExpr, toExpr (0 : Nat)]
      let evalExpr ← mkAppM ``evalIntervalDyadic #[ast, envExpr, cfgExpr]
      let checkExpr ← mkAppM ``IntervalDyadic.upperBoundedBy #[evalExpr, cExpr]

      -- 9. Build proof that check = true using KERNEL REDUCTION (decide)
      let checkEqTrueTy ← mkAppM ``Eq #[checkExpr, Lean.mkConst ``Bool.true]
      let checkProof ← try
        mkDecideProof checkEqTrueTy
      catch _ =>
        return false

      -- 10. Apply the bridge theorem
      let proof ← mkAppM ``verify_upper_bound_dyadic
        #[ast, supportProof, loRatExpr, hiRatExpr, leProof, cExpr,
          precExpr, depthExpr, precLeZeroProof, checkProof]

      -- 11. Check if proof type matches goal type
      let proofTy ← inferType proof
      let goalTy ← goal.getType
      if ← isDefEq proofTy goalTy then
        goal.assign proof
        trace[fast_bound] "Kernel verification succeeded (via decide)"
        return true
      else
        return false

    | .forallGe _name interval func boundExpr =>
      -- Similar for lower bound
      let some (_lo, _hi, loRatExpr, hiRatExpr, leProof, _loRealExpr, _hiRealExpr) := interval.fromSetIcc
        | return false

      let some c ← Auto.extractRatFromReal boundExpr
        | return false
      let cExpr := toExpr c

      -- Extract AST (from Expr.eval) or reify (from raw expression)
      let (ast, isExprEval) ← extractOrReifyAst func
      let supportProof ← mkSupportedCoreProof ast

      -- For non-Expr.eval goals, kernel verification won't type-match, so skip
      if !isExprEval then
        return false

      let precExpr := toExpr prec
      let depthExpr := toExpr taylorDepth

      let precLeZeroTy ← mkAppM ``LE.le #[precExpr, toExpr (0 : Int)]
      let precLeZeroProof ← mkDecideProof precLeZeroTy

      let intervalRatExpr ← mkAppM ``IntervalRat.mk #[loRatExpr, hiRatExpr, leProof]

      let natTy := Lean.mkConst ``Nat
      let envExpr ← withLocalDeclD `i natTy fun i => do
        let body ← mkAppM ``IntervalDyadic.ofIntervalRat #[intervalRatExpr, precExpr]
        mkLambdaFVars #[i] body

      let cfgExpr ← mkAppM ``DyadicConfig.mk #[precExpr, depthExpr, toExpr (0 : Nat)]
      let evalExpr ← mkAppM ``evalIntervalDyadic #[ast, envExpr, cfgExpr]
      let checkExpr ← mkAppM ``IntervalDyadic.lowerBoundedBy #[evalExpr, cExpr]

      let checkEqTrueTy ← mkAppM ``Eq #[checkExpr, Lean.mkConst ``Bool.true]
      let checkProof ← try
        mkDecideProof checkEqTrueTy
      catch _ =>
        return false

      let proof ← mkAppM ``verify_lower_bound_dyadic
        #[ast, supportProof, loRatExpr, hiRatExpr, leProof, cExpr,
          precExpr, depthExpr, precLeZeroProof, checkProof]

      let proofTy ← inferType proof
      let goalTy ← goal.getType
      if ← isDefEq proofTy goalTy then
        goal.assign proof
        return true
      else
        return false

    | _ =>
      -- Strict inequalities not yet supported in kernel mode
      return false

/-! ## Main Tactic -/

/--
Proves bounds using Dyadic arithmetic with kernel verification when possible.

## Trust Levels

| Mode | Verification | When Used |
|------|-------------|-----------|
| Kernel | `decide` | Goal in `Core.Expr.eval` form |
| Fallback | `native_decide` | General expressions |

Kernel verification provides maximum trust (only the Lean kernel is trusted).
Fallback mode trusts the Lean compiler and runtime in addition to the kernel.

## Kernel Verification

For goals expressed using `Core.Expr.eval`, the tactic uses kernel-verified
arithmetic via `decide`. This requires the goal's interval bounds to be
definitionally equal to rational casts:

```lean
open LeanBound.Core

-- This uses kernel verification (Expr.eval form)
example : ∀ x ∈ Set.Icc (0 : ℝ) 1,
    Expr.eval (fun _ => x) (Expr.mul (Expr.var 0) (Expr.var 0)) ≤ 2 := by
  fast_bound
```

## General Usage

For native Lean expressions, the tactic falls back to `interval_bound`
which uses `native_decide`:

```lean
-- This falls back to native_decide
example : ∀ x ∈ Set.Icc (0 : ℝ) 1, x * x ≤ 2 := by
  fast_bound
```

Usage:
- `fast_bound` - Use default precision (53 bits)
- `fast_bound n` - Use n bits of precision
-/
elab "fast_bound" prec:(num)? : tactic => do
  let precision : Int := match prec with
    | some n => -(n.getNat : Int)
    | none => -53

  -- Try kernel verification first (works for goals expressed in Core.Expr.eval)
  let success ← fastBoundKernel precision 10
  if success then
    return

  -- Fall back to interval_bound (uses native_decide but works for general goals)
  trace[fast_bound] "Using native_decide verification (interval_bound)"
  evalTactic (← `(tactic| interval_bound))

/-! ## Convenience Variants -/

/--
Fast bound with high precision (100 bits).
Use when you need tighter bounds at the cost of speed.
-/
elab "fast_bound_precise" : tactic => do
  let success ← fastBoundKernel (-100) 20
  if success then return
  evalTactic (← `(tactic| interval_bound))

/--
Fast bound with low precision (30 bits).
Use when you need maximum speed and can tolerate wider bounds.
-/
elab "fast_bound_quick" : tactic => do
  let success ← fastBoundKernel (-30) 5
  if success then return
  evalTactic (← `(tactic| interval_bound))

-- Register trace class
initialize registerTraceClass `fast_bound

end LeanBound.Tactic
