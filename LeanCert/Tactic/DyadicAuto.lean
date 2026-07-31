/-
Copyright (c) 2025 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import Lean
import LeanCert.Tactic.IntervalAuto
import LeanCert.Engine.IntervalEvalDyadic

/-!
# Legacy Dyadic Bound Tactic Names

This module retains the historical `certify_kernel*` spellings for source
compatibility and contains the dyadic bridge theorems they originally used.
New code should use the shared trust-aware entry point:

```lean
example : ∀ x ∈ Set.Icc (0 : ℝ) 1, x * x + Real.sin x ≤ 2 := by
  certify_bound (trust := kernel)
```

Verification route is independent of arithmetic backend. Use
`(trust := native)`, `(trust := kernel)`, or `(trust := auto)` per invocation,
or set `leancert.trust` for a scope. The deprecated aliases and their exact
replacements are documented below.
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

/-! ## Deprecated tactics

The original `certify_kernel` family predates the trust choke point
(`LeanCert.Tactic.closeCertificateGoalTyped`) and its strict kernel path had
rotted: it required a `Decidable` instance for `evalDomainValidDyadic` that
no longer exists, so every invocation failed. The spellings below are kept
as deprecated aliases over `certify_bound`'s trust modes, which subsume them:

| Old | Use instead |
|-----|-------------|
| `certify_kernel [prec]` | `certify_bound (trust := kernel)` |
| `certify_kernel_fallback [prec]` | `certify_bound (trust := auto)` |
| `certify_kernel_precise[_fallback]` | same, with an explicit depth |
| `certify_kernel_quick[_fallback]` | same, with an explicit depth |

The old precision argument (dyadic bits) is accepted but ignored: the
certificate route selects precision internally and the depth search is
adaptive. Kernel mode never silently falls back; auto reports fallbacks. -/

private def deprecatedCertifyKernel (repl : String)
    (mode : VerificationMode) (depth : Option Nat) : TacticM Unit := do
  logWarning m!"this tactic is deprecated: use `{repl}` \
    (the old precision argument, if any, is ignored)"
  withTrustMode (some mode) do
    Auto.certifyBoundWithDepth depth

/-- Deprecated: use `certify_bound (trust := kernel)`. -/
elab "certify_kernel" (num)? : tactic =>
  deprecatedCertifyKernel "certify_bound (trust := kernel)" .kernel none

/-- Deprecated: use `certify_bound (trust := auto)`. -/
elab "certify_kernel_fallback" (num)? : tactic =>
  deprecatedCertifyKernel "certify_bound (trust := auto)" .auto none

/-- Deprecated: use `certify_bound 20 (trust := kernel)`. -/
elab "certify_kernel_precise" : tactic =>
  deprecatedCertifyKernel "certify_bound 20 (trust := kernel)" .kernel (some 20)

/-- Deprecated: use `certify_bound 20 (trust := auto)`. -/
elab "certify_kernel_precise_fallback" : tactic =>
  deprecatedCertifyKernel "certify_bound 20 (trust := auto)" .auto (some 20)

/-- Deprecated: use `certify_bound 5 (trust := kernel)`. -/
elab "certify_kernel_quick" : tactic =>
  deprecatedCertifyKernel "certify_bound 5 (trust := kernel)" .kernel (some 5)

/-- Deprecated: use `certify_bound 5 (trust := auto)`. -/
elab "certify_kernel_quick_fallback" : tactic =>
  deprecatedCertifyKernel "certify_bound 5 (trust := auto)" .auto (some 5)

end LeanCert.Tactic
