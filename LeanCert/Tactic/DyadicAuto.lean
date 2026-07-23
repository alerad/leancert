/-
Copyright (c) 2025 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import Lean
import LeanCert.Tactic.IntervalAuto
import LeanCert.Engine.IntervalEvalDyadic

/-!
# Kernel-Verified Dyadic Bound Tactics

This tactic uses the Dyadic backend to prove bounds **within the Lean kernel**.
Unlike `certify_bound`, which uses `native_decide` (relying on the compiler/runtime),
`certify_kernel` uses `decide`, which reduces the proof term in the kernel.

This is made possible because Dyadic arithmetic avoids the expensive GCD computations
of `Rat` that typically make kernel reduction infeasible for deep expressions.

## Main tactics

* `certify_kernel` - Prove bounds using Dyadic arithmetic with kernel verification
* `certify_kernel n` - Specify precision in bits (default: 53)
* `certify_kernel_fallback` - Opt in to falling back to `certify_bound`

## Verification Trust Level

| Tactic | Verification | Trust |
|--------|-------------|-------|
| `certify_bound` | `native_decide` | Lean Compiler + Runtime |
| `certify_kernel` | `decide` | Lean Kernel only |
| `certify_kernel_fallback` | `decide`, then `native_decide` | Lean Kernel + compiler/runtime on fallback |

The kernel is the smallest trusted component of Lean. By using `decide`,
`certify_kernel` provides proofs that are verified by this minimal trusted base.

## When to use `certify_kernel`

Use `certify_kernel` instead of `certify_bound` when:
1. **Maximum trust**: You need proofs verified by the kernel, not the compiler
2. **Deep expressions**: Nested transcendentals like `sin(sin(sin(x)))`
3. **Many multiplications**: Polynomials with many terms
4. **Audit requirements**: Security-critical code that needs minimal TCB

## Example

```lean
-- Proves using only kernel reduction (no compiler trust)
example : ∀ x ∈ Set.Icc (0 : ℝ) 1, x * x + Real.sin x ≤ 2 := by
  certify_kernel

-- Higher precision for tight bounds
example : ∀ x ∈ Set.Icc (0 : ℝ) 1, Real.exp x ≤ 2.72 := by
  certify_kernel 100
```
-/

open Lean Meta Elab Tactic Term

namespace LeanCert.Tactic

open LeanCert.Meta
open LeanCert.Core
open LeanCert.Engine

/-! ## Bridge Theorems for Dyadic Kernel Verification -/

/-- Bridge theorem: Verify upper bound on Set.Icc using Dyadic arithmetic.
    This connects the decidable boolean `upperBoundedBy` to the semantic property. -/
theorem verify_upper_bound_dyadic (e : Core.Expr) (hsupp : ExprSupportedCore e)
    (lo hi : ℚ) (hle : lo ≤ hi) (c : ℚ)
    (prec : Int) (depth : Nat) (h_prec : prec ≤ 0)
    (hdom : evalDomainValidDyadic e (fun _ => IntervalDyadic.ofIntervalRat ⟨lo, hi, hle⟩ prec)
        { precision := prec, taylorDepth := depth })
    (h_check : (LeanCert.Internal.Dyadic.evalUnchecked e
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
    { precision := prec, taylorDepth := depth } h_prec hdom
  -- Extract upper bound from boolean check
  simp only [IntervalDyadic.upperBoundedBy, decide_eq_true_eq] at h_check
  -- Conclude: eval ≤ hi.toRat ≤ c
  calc Core.Expr.eval (fun _ => x) e
      ≤ ((LeanCert.Internal.Dyadic.evalUnchecked e ρ_dyad { precision := prec, taylorDepth := depth }).hi.toRat : ℝ) := h_eval.2
    _ ≤ c := by exact_mod_cast h_check

/-- Bridge theorem: Verify lower bound on Set.Icc using Dyadic arithmetic. -/
theorem verify_lower_bound_dyadic (e : Core.Expr) (hsupp : ExprSupportedCore e)
    (lo hi : ℚ) (hle : lo ≤ hi) (c : ℚ)
    (prec : Int) (depth : Nat) (h_prec : prec ≤ 0)
    (hdom : evalDomainValidDyadic e (fun _ => IntervalDyadic.ofIntervalRat ⟨lo, hi, hle⟩ prec)
        { precision := prec, taylorDepth := depth })
    (h_check : (LeanCert.Internal.Dyadic.evalUnchecked e
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
    { precision := prec, taylorDepth := depth } h_prec hdom
  simp only [IntervalDyadic.lowerBoundedBy, decide_eq_true_eq] at h_check
  calc (c : ℝ)
      ≤ ((LeanCert.Internal.Dyadic.evalUnchecked e ρ_dyad { precision := prec, taylorDepth := depth }).lo.toRat : ℝ) := by exact_mod_cast h_check
    _ ≤ Core.Expr.eval (fun _ => x) e := h_eval.1

/-! ## Tactic Implementation -/

/-- Reasons why kernel verification might not be used. -/
inductive KernelVerifyResult
  | success : KernelVerifyResult
  | nativeExpression : KernelVerifyResult  -- Goal uses native Lean expression, not Expr.eval
  | boundsNotDefeq : KernelVerifyResult    -- Interval bounds aren't definitionally equal
  | boundCheckFailed : KernelVerifyResult  -- Computed bound doesn't satisfy goal
  | parseError : KernelVerifyResult        -- Couldn't parse goal structure
  | unsupportedGoal : KernelVerifyResult   -- Goal type not supported (e.g., strict inequality)
  deriving DecidableEq

/-- Try to extract AST from a function that may be Core.Expr.eval or a raw expression.
    Returns (ast, isExprEval) where isExprEval indicates if goal was in Expr.eval form. -/
def extractOrReifyAst (func : Lean.Expr) : TacticM (Lean.Expr × Bool) := do
  lambdaTelescope func fun _vars body => do
    let fn := body.getAppFn
    if fn.isConstOf ``LeanCert.Core.Expr.eval then
      -- It's Expr.eval env ast - extract the ast directly
      let args := body.getAppArgs
      if args.size ≥ 2 then
        return (args[1]!, true)
      else
        throwError "Unexpected Expr.eval application structure"
    else
      -- Raw expression - reify it
      return ((← reifyWithReport func).expr, false)

/-- Core implementation of certify_kernel_fallback with kernel verification.
    Returns a result indicating success or reason for fallback. -/
def kernelBoundCore (prec : Int) (taylorDepth : Nat) : TacticM KernelVerifyResult := do
  let goal ← getMainGoal
  let goalType ← goal.getType

  -- 1. Parse the goal
  let some boundGoal ← Auto.parseBoundGoal goalType
    | return .parseError

  goal.withContext do
    match boundGoal with
    | .forallLe _name interval func boundExpr =>
      -- 2. Extract interval bounds
      let some (_lo, _hi, loRatExpr, hiRatExpr, leProof, _loRealExpr, _hiRealExpr) := interval.fromSetIcc
        | return .parseError

      -- 3. Extract bound as rational
      let some c ← Auto.extractRatFromReal boundExpr
        | return .parseError
      let cExpr := toExpr c

      -- 4. Extract AST (from Expr.eval) or reify (from raw expression)
      let (ast, isExprEval) ← extractOrReifyAst func
      let supportProof ← mkSupportedCoreProof ast

      -- For non-Expr.eval goals, kernel verification won't type-match, so skip
      if !isExprEval then
        return .nativeExpression

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

      let cfgExpr ← mkAppM ``DyadicConfig.mk #[precExpr, depthExpr]
      let evalExpr ← mkAppM ``LeanCert.Internal.Dyadic.evalUnchecked #[ast, envExpr, cfgExpr]
      let checkExpr ← mkAppM ``IntervalDyadic.upperBoundedBy #[evalExpr, cExpr]

      -- 9. Build proof that check = true using KERNEL REDUCTION (decide)
      let checkEqTrueTy ← mkAppM ``Eq #[checkExpr, Lean.mkConst ``Bool.true]
      let checkProof ← try
        mkDecideProof checkEqTrueTy
      catch _ =>
        return .boundCheckFailed

      -- 9b. Build domain validity proof (trivial for expressions without log)
      let domTy ← mkAppM ``evalDomainValidDyadic #[ast, envExpr, cfgExpr]
      let domProof ← try
        mkDecideProof domTy  -- Works because evalDomainValidDyadic is decidable (True for non-log)
      catch _ =>
        return .boundCheckFailed  -- Log expressions not supported in kernel mode

      -- 10. Apply the bridge theorem
      let proof ← mkAppM ``verify_upper_bound_dyadic
        #[ast, supportProof, loRatExpr, hiRatExpr, leProof, cExpr,
          precExpr, depthExpr, precLeZeroProof, domProof, checkProof]

      -- 11. Check if proof type matches goal type
      let proofTy ← inferType proof
      let goalTy ← goal.getType
      if ← isDefEq proofTy goalTy then
        goal.assign proof
        trace[certify_kernel_fallback] "Kernel verification succeeded (via decide)"
        return .success
      else
        return .boundsNotDefeq

    | .forallGe _name interval func boundExpr =>
      -- Similar for lower bound
      let some (_lo, _hi, loRatExpr, hiRatExpr, leProof, _loRealExpr, _hiRealExpr) := interval.fromSetIcc
        | return .parseError

      let some c ← Auto.extractRatFromReal boundExpr
        | return .parseError
      let cExpr := toExpr c

      -- Extract AST (from Expr.eval) or reify (from raw expression)
      let (ast, isExprEval) ← extractOrReifyAst func
      let supportProof ← mkSupportedCoreProof ast

      -- For non-Expr.eval goals, kernel verification won't type-match, so skip
      if !isExprEval then
        return .nativeExpression

      let precExpr := toExpr prec
      let depthExpr := toExpr taylorDepth

      let precLeZeroTy ← mkAppM ``LE.le #[precExpr, toExpr (0 : Int)]
      let precLeZeroProof ← mkDecideProof precLeZeroTy

      let intervalRatExpr ← mkAppM ``IntervalRat.mk #[loRatExpr, hiRatExpr, leProof]

      let natTy := Lean.mkConst ``Nat
      let envExpr ← withLocalDeclD `i natTy fun i => do
        let body ← mkAppM ``IntervalDyadic.ofIntervalRat #[intervalRatExpr, precExpr]
        mkLambdaFVars #[i] body

      let cfgExpr ← mkAppM ``DyadicConfig.mk #[precExpr, depthExpr]
      let evalExpr ← mkAppM ``LeanCert.Internal.Dyadic.evalUnchecked #[ast, envExpr, cfgExpr]
      let checkExpr ← mkAppM ``IntervalDyadic.lowerBoundedBy #[evalExpr, cExpr]

      let checkEqTrueTy ← mkAppM ``Eq #[checkExpr, Lean.mkConst ``Bool.true]
      let checkProof ← try
        mkDecideProof checkEqTrueTy
      catch _ =>
        return .boundCheckFailed

      -- Build domain validity proof (trivial for expressions without log)
      let domTy ← mkAppM ``evalDomainValidDyadic #[ast, envExpr, cfgExpr]
      let domProof ← try
        mkDecideProof domTy
      catch _ =>
        return .boundCheckFailed

      let proof ← mkAppM ``verify_lower_bound_dyadic
        #[ast, supportProof, loRatExpr, hiRatExpr, leProof, cExpr,
          precExpr, depthExpr, precLeZeroProof, domProof, checkProof]

      let proofTy ← inferType proof
      let goalTy ← goal.getType
      if ← isDefEq proofTy goalTy then
        goal.assign proof
        trace[certify_kernel_fallback] "Kernel verification succeeded (via decide)"
        return .success
      else
        return .boundsNotDefeq

    | _ =>
      -- Strict inequalities not yet supported in kernel mode
      return .unsupportedGoal

/-! ## Main Tactics -/

def KernelVerifyResult.message : KernelVerifyResult → MessageData
  | .success => "kernel verification succeeded"
  | .nativeExpression =>
      "goal uses native Lean expressions, not `Core.Expr.eval`; express the goal with `Expr.eval` for kernel-only verification"
  | .boundsNotDefeq =>
      "interval bounds are not definitionally equal to rational casts"
  | .boundCheckFailed =>
      "kernel bound check failed; try increasing precision"
  | .parseError =>
      "could not parse goal structure"
  | .unsupportedGoal =>
      "goal form is not supported by kernel mode"

def evalCertifyBoundFallback (precSyntax : Option (TSyntax `num)) : TacticM Unit := do
  match precSyntax with
  | some n => evalTactic (← `(tactic| certify_bound $n))
  | none => evalTactic (← `(tactic| certify_bound))

/--
The certify_kernel tactic. Proves bounds using Dyadic arithmetic with kernel
verification when possible.

## Trust Levels

| Mode | Verification | When Used |
|------|-------------|-----------|
| Kernel | `decide` | Goal in `Core.Expr.eval` form |
`certify_kernel` is strict: if kernel verification cannot close the goal, it
fails with a diagnostic.  Use `certify_kernel_fallback` to explicitly allow the
native `certify_bound` path.

## Kernel Verification

For goals expressed using `Core.Expr.eval`, the tactic uses kernel-verified
arithmetic via `decide`. This requires the goal's interval bounds to be
definitionally equal to rational casts:

```lean
open LeanCert.Core

-- This uses kernel verification (Expr.eval form)
example : ∀ x ∈ Set.Icc (0 : ℝ) 1,
    Expr.eval (fun _ => x) (Expr.mul (Expr.var 0) (Expr.var 0)) ≤ 2 := by
  certify_kernel
```

## General Usage

For native Lean expressions, use the explicit fallback tactic:

```lean
-- This may fall back to native_decide
example : ∀ x ∈ Set.Icc (0 : ℝ) 1, x * x ≤ 2 := by
  certify_kernel_fallback
```

Usage:
- `certify_kernel` - Use default precision (53 bits)
- `certify_kernel n` - Use n bits of precision

-/
elab "certify_kernel" prec:(num)? : tactic => do
  let precision : Int := match prec with
    | some n => -(n.getNat : Int)
    | none => -53

  -- Try kernel verification first (works for goals expressed in Core.Expr.eval)
  let result ← kernelBoundCore precision 10

  match result with
  | .success =>
    return  -- Kernel verification succeeded
  | other =>
    throwError "certify_kernel: kernel verification failed: {other.message}\n\
      This tactic no longer silently falls back to native verification.\n\
      Use `certify_kernel_fallback` if the compiler/runtime fallback is acceptable."

/-- Explicit opt-in wrapper: try kernel verification, then use `certify_bound`. -/
elab "certify_kernel_fallback" prec:(num)? : tactic => do
  let precision : Int := match prec with
    | some n => -(n.getNat : Int)
    | none => -53
  let result ← kernelBoundCore precision 10
  match result with
  | .success => return
  | other =>
    logWarning m!"certify_kernel_fallback: using native fallback because kernel verification failed: {other.message}"
    evalCertifyBoundFallback prec

/-! ## Convenience Variants -/

/--
certify_kernel with high precision (100 bits).
Use when you need tighter bounds at the cost of speed.
-/
elab "certify_kernel_precise" : tactic => do
  let result ← kernelBoundCore (-100) 20
  if result == .success then return
  throwError "certify_kernel_precise: kernel verification failed: {result.message}\n\
    Use `certify_kernel_precise_fallback` if native verification is acceptable."

elab "certify_kernel_precise_fallback" : tactic => do
  let result ← kernelBoundCore (-100) 20
  if result == .success then return
  logWarning m!"certify_kernel_precise_fallback: using native fallback because kernel verification failed: {result.message}"
  evalTactic (← `(tactic| certify_bound 100))

/--
certify_kernel with low precision (30 bits).
Use when you need maximum speed and can tolerate wider bounds.
-/
elab "certify_kernel_quick" : tactic => do
  let result ← kernelBoundCore (-30) 5
  if result == .success then return
  throwError "certify_kernel_quick: kernel verification failed: {result.message}\n\
    Use `certify_kernel_quick_fallback` if native verification is acceptable."

elab "certify_kernel_quick_fallback" : tactic => do
  let result ← kernelBoundCore (-30) 5
  if result == .success then return
  logWarning m!"certify_kernel_quick_fallback: using native fallback because kernel verification failed: {result.message}"
  evalTactic (← `(tactic| certify_bound 30))

-- Register trace classes
initialize registerTraceClass `certify_kernel

end LeanCert.Tactic
