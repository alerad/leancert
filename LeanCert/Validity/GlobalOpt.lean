/-
Copyright (c) 2024 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Engine.Optimization.Global

/-!
# Global Optimization Certificates

These checkers and theorems extend the certificate pattern to multivariate
global optimization over n-dimensional boxes.

## Main definitions

### Boolean Checkers
* `checkGlobalLowerBound` - Check if `c` is a lower bound for `e` over box `B`
* `checkGlobalUpperBound` - Check if `c` is an upper bound for `e` over box `B`
* `checkGlobalBounds` - Check both lower and upper bounds

### Golden Theorems
* `verify_global_lower_bound` - Converts boolean check to semantic proof
* `verify_global_upper_bound` - Converts boolean check to semantic proof
* `verify_global_bounds` - Two-sided bound verification
-/

namespace LeanCert.Validity.GlobalOpt

open LeanCert.Core
open LeanCert.Engine
open LeanCert.Engine.Optimization

/-! ### Boolean Checkers for Global Optimization -/

/-- Check if `c` is a lower bound for `e` over box `B`.
    Returns `true` iff `globalMinimizeCore(e, B, cfg).bound.lo ≥ c`. -/
def checkGlobalLowerBound (e : Expr) (B : Box) (c : ℚ) (cfg : GlobalOptConfig) : Bool :=
  checkDomainValid e B.toEnv { taylorDepth := cfg.taylorDepth } &&
  decide (c ≤ (globalMinimizeCore e B cfg).bound.lo)

/-- Check if `c` is an upper bound for `e` over box `B`.
    Returns `true` iff `globalMaximizeCore(e, B, cfg).bound.hi ≤ c`.
    (i.e., the upper bound on max(e) is ≤ c, which proves ∀ρ, e(ρ) ≤ c)

    Note: bound.hi = -globalMinimizeCore(-e).bound.lo, and by correctness
    globalMinimizeCore(-e).bound.lo ≤ -e(ρ) for all ρ, so e(ρ) ≤ bound.hi. -/
def checkGlobalUpperBound (e : Expr) (B : Box) (c : ℚ) (cfg : GlobalOptConfig) : Bool :=
  checkDomainValid e B.toEnv { taylorDepth := cfg.taylorDepth } &&
  decide ((globalMaximizeCore e B cfg).bound.hi ≤ c)

/-- Check both lower and upper bounds for global optimization -/
def checkGlobalBounds (e : Expr) (B : Box) (lo hi : ℚ) (cfg : GlobalOptConfig) : Bool :=
  checkGlobalLowerBound e B lo cfg && checkGlobalUpperBound e B hi cfg

/-! ### Golden Theorems for Global Optimization -/

/-- **Golden Theorem for Global Lower Bounds**

    If `checkGlobalLowerBound e B c cfg = true`, then `∀ ρ ∈ B, c ≤ Expr.eval ρ e`.

    This converts the boolean certificate into a semantic proof about all points
    in the box.

    Note: This uses ExprSupported (no log) which guarantees domain validity automatically.
    For expressions with log, use the Core version with explicit domain validity proofs. -/
theorem verify_global_lower_bound (e : Expr) (hsupp : ExprSupported e)
    (B : Box) (c : ℚ) (cfg : GlobalOptConfig)
    (h_cert : checkGlobalLowerBound e B c cfg = true) :
    ∀ (ρ : Nat → ℝ), Box.envMem ρ B → (∀ i, i ≥ B.length → ρ i = 0) →
      c ≤ Expr.eval ρ e := by
  simp only [checkGlobalLowerBound, Bool.and_eq_true, decide_eq_true_eq] at h_cert
  intro ρ hρ hzero
  -- Domain validity is automatic for ExprSupported expressions
  have hdom : ∀ (B' : Box), B'.length = B.length → evalDomainValid e B'.toEnv { taylorDepth := cfg.taylorDepth } := by
    intro B' _
    exact ExprSupported.domainValid hsupp B'.toEnv { taylorDepth := cfg.taylorDepth }
  have hlo := globalMinimizeCore_lo_correct e hsupp.toCore B cfg hdom ρ hρ hzero
  calc (c : ℝ) ≤ (globalMinimizeCore e B cfg).bound.lo := by exact_mod_cast h_cert.2
    _ ≤ Expr.eval ρ e := hlo

/-- **Golden Theorem for Global Upper Bounds**

    If `checkGlobalUpperBound e B c cfg = true`, then `∀ ρ ∈ B, Expr.eval ρ e ≤ c`.

    The maximization problem is reduced to minimization of -e.

    Note: This uses ExprSupported (no log) which guarantees domain validity automatically.
    For expressions with log, use the Core version with explicit domain validity proofs. -/
theorem verify_global_upper_bound (e : Expr) (hsupp : ExprSupported e)
    (B : Box) (c : ℚ) (cfg : GlobalOptConfig)
    (h_cert : checkGlobalUpperBound e B c cfg = true) :
    ∀ (ρ : Nat → ℝ), Box.envMem ρ B → (∀ i, i ≥ B.length → ρ i = 0) →
      Expr.eval ρ e ≤ c := by
  simp only [checkGlobalUpperBound, Bool.and_eq_true, decide_eq_true_eq] at h_cert
  intro ρ hρ hzero
  -- Domain validity is automatic for ExprSupported expressions
  have hneg_supp : ExprSupportedCore (Expr.neg e) := ExprSupportedCore.neg hsupp.toCore
  have hneg_dom : ∀ (B' : Box), B'.length = B.length → evalDomainValid (Expr.neg e) B'.toEnv { taylorDepth := cfg.taylorDepth } := by
    intro B' _
    simp only [evalDomainValid]
    exact ExprSupported.domainValid hsupp B'.toEnv { taylorDepth := cfg.taylorDepth }
  have hlo_neg := globalMinimizeCore_lo_correct (Expr.neg e) hneg_supp B cfg hneg_dom ρ hρ hzero
  simp only [Expr.eval_neg] at hlo_neg
  have heval_bound : Expr.eval ρ e ≤ -((globalMinimizeCore (Expr.neg e) B cfg).bound.lo : ℝ) := by
    linarith
  have hhi_eq : ((globalMaximizeCore e B cfg).bound.hi : ℝ) =
                -((globalMinimizeCore (Expr.neg e) B cfg).bound.lo : ℝ) := by
    simp only [globalMaximizeCore]
    push_cast
    ring
  calc Expr.eval ρ e
      ≤ -((globalMinimizeCore (Expr.neg e) B cfg).bound.lo : ℝ) := heval_bound
    _ = ((globalMaximizeCore e B cfg).bound.hi : ℝ) := hhi_eq.symm
    _ ≤ c := by exact_mod_cast h_cert.2

/-- Two-sided global bound verification -/
theorem verify_global_bounds (e : Expr) (hsupp : ExprSupported e)
    (B : Box) (lo hi : ℚ) (cfg : GlobalOptConfig)
    (h_cert : checkGlobalBounds e B lo hi cfg = true) :
    ∀ (ρ : Nat → ℝ), Box.envMem ρ B → (∀ i, i ≥ B.length → ρ i = 0) →
      lo ≤ Expr.eval ρ e ∧ Expr.eval ρ e ≤ hi := by
  simp only [checkGlobalBounds, Bool.and_eq_true] at h_cert
  intro ρ hρ hzero
  exact ⟨verify_global_lower_bound e hsupp B lo cfg h_cert.1 ρ hρ hzero,
         verify_global_upper_bound e hsupp B hi cfg h_cert.2 ρ hρ hzero⟩

end LeanCert.Validity.GlobalOpt
