/-
Copyright (c) 2024 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Engine.IntervalEval
import LeanCert.Engine.IntervalEvalReal

/-!
# Interval Arithmetic Tactics

This file provides tactics for proving bounds on expressions using
interval arithmetic.

## Main tactics

* `interval_le`, `interval_ge`, `interval_lt`, `interval_gt` - Prove bounds using `native_decide`

## Design notes

We provide two sets of lemmas:

### Core (computable) - uses `evalIntervalCore1`
For expressions in `ExprSupportedCore` (const, var, add, mul, neg, sin, cos),
the bound checking is fully computable and works with `native_decide`.

### Extended (noncomputable) - uses `evalInterval1`
For expressions in `ExprSupported` (core + exp), the bound checking requires
noncomputable evaluation due to `Real.exp`. These cannot use `native_decide`.

The tactics use the core evaluator to enable `native_decide`.
-/

namespace LeanCert.Tactic

open LeanCert.Core
open LeanCert.Engine

/-! ### Helper lemmas for decidable bounds (core, computable) -/

/-- Decidable version of hi ≤ c for core rational bounds -/
theorem intervalCore_hi_le_decide (e : Expr) (I : IntervalRat) (c : ℚ) (cfg : EvalConfig := {}) :
    (evalIntervalCore1 e I cfg).hi ≤ c ↔ decide ((evalIntervalCore1 e I cfg).hi ≤ c) = true := by
  simp only [decide_eq_true_eq]

/-- Decidable version of c ≤ lo for core rational bounds -/
theorem intervalCore_lo_ge_decide (e : Expr) (I : IntervalRat) (c : ℚ) (cfg : EvalConfig := {}) :
    c ≤ (evalIntervalCore1 e I cfg).lo ↔ decide (c ≤ (evalIntervalCore1 e I cfg).lo) = true := by
  simp only [decide_eq_true_eq]

/-- Decidable version of hi < c for core rational bounds -/
theorem intervalCore_hi_lt_decide (e : Expr) (I : IntervalRat) (c : ℚ) (cfg : EvalConfig := {}) :
    (evalIntervalCore1 e I cfg).hi < c ↔ decide ((evalIntervalCore1 e I cfg).hi < c) = true := by
  simp only [decide_eq_true_eq]

/-- Decidable version of c < lo for core rational bounds -/
theorem intervalCore_lo_gt_decide (e : Expr) (I : IntervalRat) (c : ℚ) (cfg : EvalConfig := {}) :
    c < (evalIntervalCore1 e I cfg).lo ↔ decide (c < (evalIntervalCore1 e I cfg).lo) = true := by
  simp only [decide_eq_true_eq]

/-! ### Combined lemmas for tactic use (core, computable) -/

/-- Prove f(x) ≤ c by core interval arithmetic with decidable check.
    This combines the correctness theorem with decidability and works with native_decide.
    Requires domain validity (e.g., log arguments must be positive). -/
theorem proveCore_le_by_interval (e : Expr) (hsupp : ExprSupportedCore e)
    (I : IntervalRat) (c : ℚ) (cfg : EvalConfig := {}) (x : ℝ) (hx : x ∈ I)
    (hdom : evalDomainValid1 e I cfg)
    (hdec : decide ((evalIntervalCore1 e I cfg).hi ≤ c) = true) :
    Expr.eval (fun _ => x) e ≤ c := by
  have hhi := (intervalCore_hi_le_decide e I c cfg).mpr hdec
  exact exprCore_le_of_interval_hi e hsupp I c cfg hdom hhi x hx

/-- Prove c ≤ f(x) by core interval arithmetic with decidable check.
    Requires domain validity (e.g., log arguments must be positive). -/
theorem proveCore_ge_by_interval (e : Expr) (hsupp : ExprSupportedCore e)
    (I : IntervalRat) (c : ℚ) (cfg : EvalConfig := {}) (x : ℝ) (hx : x ∈ I)
    (hdom : evalDomainValid1 e I cfg)
    (hdec : decide (c ≤ (evalIntervalCore1 e I cfg).lo) = true) :
    c ≤ Expr.eval (fun _ => x) e := by
  have hlo := (intervalCore_lo_ge_decide e I c cfg).mpr hdec
  exact exprCore_ge_of_interval_lo e hsupp I c cfg hdom hlo x hx

/-- Prove f(x) < c by core interval arithmetic with decidable check.
    Requires domain validity (e.g., log arguments must be positive). -/
theorem proveCore_lt_by_interval (e : Expr) (hsupp : ExprSupportedCore e)
    (I : IntervalRat) (c : ℚ) (cfg : EvalConfig := {}) (x : ℝ) (hx : x ∈ I)
    (hdom : evalDomainValid1 e I cfg)
    (hdec : decide ((evalIntervalCore1 e I cfg).hi < c) = true) :
    Expr.eval (fun _ => x) e < c := by
  have hhi := (intervalCore_hi_lt_decide e I c cfg).mpr hdec
  exact exprCore_lt_of_interval_hi_lt e hsupp I c cfg hdom hhi x hx

/-- Prove c < f(x) by core interval arithmetic with decidable check.
    Requires domain validity (e.g., log arguments must be positive). -/
theorem proveCore_gt_by_interval (e : Expr) (hsupp : ExprSupportedCore e)
    (I : IntervalRat) (c : ℚ) (cfg : EvalConfig := {}) (x : ℝ) (hx : x ∈ I)
    (hdom : evalDomainValid1 e I cfg)
    (hdec : decide (c < (evalIntervalCore1 e I cfg).lo) = true) :
    c < Expr.eval (fun _ => x) e := by
  have hlo := (intervalCore_lo_gt_decide e I c cfg).mpr hdec
  exact exprCore_gt_of_interval_lo_gt e hsupp I c cfg hdom hlo x hx

/-! ### Universal quantifier versions (core, computable) -/

/-- Prove ∀ x ∈ I, f(x) ≤ c by core interval arithmetic.
    Works with native_decide for expressions in ExprSupportedCore.
    Requires domain validity (e.g., log arguments must be positive). -/
theorem proveCore_forall_le_by_interval (e : Expr) (hsupp : ExprSupportedCore e)
    (I : IntervalRat) (c : ℚ) (cfg : EvalConfig := {})
    (hdom : evalDomainValid1 e I cfg)
    (hdec : decide ((evalIntervalCore1 e I cfg).hi ≤ c) = true) :
    ∀ x ∈ I, Expr.eval (fun _ => x) e ≤ c := by
  intro x hx
  exact proveCore_le_by_interval e hsupp I c cfg x hx hdom hdec

/-- Prove ∀ x ∈ I, c ≤ f(x) by core interval arithmetic.
    Requires domain validity (e.g., log arguments must be positive). -/
theorem proveCore_forall_ge_by_interval (e : Expr) (hsupp : ExprSupportedCore e)
    (I : IntervalRat) (c : ℚ) (cfg : EvalConfig := {})
    (hdom : evalDomainValid1 e I cfg)
    (hdec : decide (c ≤ (evalIntervalCore1 e I cfg).lo) = true) :
    ∀ x ∈ I, c ≤ Expr.eval (fun _ => x) e := by
  intro x hx
  exact proveCore_ge_by_interval e hsupp I c cfg x hx hdom hdec

/-- Prove ∀ x ∈ I, f(x) < c by core interval arithmetic.
    Requires domain validity (e.g., log arguments must be positive). -/
theorem proveCore_forall_lt_by_interval (e : Expr) (hsupp : ExprSupportedCore e)
    (I : IntervalRat) (c : ℚ) (cfg : EvalConfig := {})
    (hdom : evalDomainValid1 e I cfg)
    (hdec : decide ((evalIntervalCore1 e I cfg).hi < c) = true) :
    ∀ x ∈ I, Expr.eval (fun _ => x) e < c := by
  intro x hx
  exact proveCore_lt_by_interval e hsupp I c cfg x hx hdom hdec

/-- Prove ∀ x ∈ I, c < f(x) by core interval arithmetic.
    Requires domain validity (e.g., log arguments must be positive). -/
theorem proveCore_forall_gt_by_interval (e : Expr) (hsupp : ExprSupportedCore e)
    (I : IntervalRat) (c : ℚ) (cfg : EvalConfig := {})
    (hdom : evalDomainValid1 e I cfg)
    (hdec : decide (c < (evalIntervalCore1 e I cfg).lo) = true) :
    ∀ x ∈ I, c < Expr.eval (fun _ => x) e := by
  intro x hx
  exact proveCore_gt_by_interval e hsupp I c cfg x hx hdom hdec

/-! ### Extended versions (noncomputable, for reference) -/

/-- Prove f(x) ≤ c by extended interval arithmetic.
    NOTE: Cannot use native_decide due to noncomputability of exp. -/
theorem prove_le_by_interval (e : Expr) (hsupp : ExprSupported e)
    (I : IntervalRat) (c : ℚ) (x : ℝ) (hx : x ∈ I)
    (hhi : (evalInterval1 e I).hi ≤ c) :
    Expr.eval (fun _ => x) e ≤ c :=
  expr_le_of_mem_interval e hsupp I c x hx hhi

/-- Prove c ≤ f(x) by extended interval arithmetic. -/
theorem prove_ge_by_interval (e : Expr) (hsupp : ExprSupported e)
    (I : IntervalRat) (c : ℚ) (x : ℝ) (hx : x ∈ I)
    (hlo : c ≤ (evalInterval1 e I).lo) :
    c ≤ Expr.eval (fun _ => x) e :=
  expr_ge_of_mem_interval e hsupp I c x hx hlo

/-! ### Tactic Macros

These macros provide an ergonomic interface for proving bounds.
They use the CORE (computable) evaluator, so `native_decide` works.

## Usage

```lean
example : ∀ x ∈ I01, Expr.eval (fun _ => x) exprXSq ≤ 1 := by
  interval_le exprXSq exprXSq_supp I01 1
```

Note: For expressions containing `exp`, use manual proofs with `expr_le_of_interval_hi`
and explicit bound computation, as `native_decide` won't work.
-/

/-- Prove `∀ x ∈ I, f(x) ≤ c` using core interval arithmetic.
    Usage: `interval_le e supp I c`
    Requires `ExprSupportedCore e` for native_decide to work. -/
macro "interval_le" e:term "," supp:term "," I:term "," c:term : tactic =>
  `(tactic| apply proveCore_forall_le_by_interval $e $supp $I $c <;> native_decide)

/-- Prove `∀ x ∈ I, c ≤ f(x)` using core interval arithmetic.
    Usage: `interval_ge e supp I c` -/
macro "interval_ge" e:term "," supp:term "," I:term "," c:term : tactic =>
  `(tactic| apply proveCore_forall_ge_by_interval $e $supp $I $c <;> native_decide)

/-- Prove `∀ x ∈ I, f(x) < c` using core interval arithmetic.
    Usage: `interval_lt e supp I c` -/
macro "interval_lt" e:term "," supp:term "," I:term "," c:term : tactic =>
  `(tactic| apply proveCore_forall_lt_by_interval $e $supp $I $c <;> native_decide)

/-- Prove `∀ x ∈ I, c < f(x)` using core interval arithmetic.
    Usage: `interval_gt e supp I c` -/
macro "interval_gt" e:term "," supp:term "," I:term "," c:term : tactic =>
  `(tactic| apply proveCore_forall_gt_by_interval $e $supp $I $c <;> native_decide)

/-- Prove a pointwise bound `f(x) ≤ c` given `x ∈ I`.
    Usage: `interval_le_pt e supp I c x hx` -/
macro "interval_le_pt" e:term "," supp:term "," I:term "," c:term "," x:term "," hx:term : tactic =>
  `(tactic| apply proveCore_le_by_interval $e $supp $I $c $x $hx <;> native_decide)

/-- Prove a pointwise bound `c ≤ f(x)` given `x ∈ I`.
    Usage: `interval_ge_pt e supp I c x hx` -/
macro "interval_ge_pt" e:term "," supp:term "," I:term "," c:term "," x:term "," hx:term : tactic =>
  `(tactic| apply proveCore_ge_by_interval $e $supp $I $c $x $hx <;> native_decide)

/-! ### Extended interval tactics (noncomputable, for exp-containing expressions)

These tactics work with `ExprSupported` (which includes exp) but cannot use
`native_decide`. They reduce the goal to an interval inequality that must be
proved by other means (linarith, norm_num, or manual computation).

## Usage

```lean
-- Reduces to goal: (evalInterval1 exprExp I01).hi ≤ 3
theorem exp_le_three_on_01 :
    ∀ x ∈ I01, Expr.eval (fun _ => x) exprExp ≤ (3 : ℚ) := by
  interval_ext_le exprExp, exprExp_supp, I01, 3
  -- Then prove the interval bound manually
  sorry
```
-/

/-- Extended interval tactic for ≤ (supports exp).
    Reduces `∀ x ∈ I, f(x) ≤ c` to `(evalInterval1 e I).hi ≤ c`.
    Usage: `interval_ext_le e, supp, I, c` -/
macro "interval_ext_le" e:term "," supp:term "," I:term "," c:term : tactic =>
  `(tactic| apply expr_le_of_interval_hi $e $supp $I $c)

/-- Extended interval tactic for ≥ (supports exp).
    Reduces `∀ x ∈ I, c ≤ f(x)` to `c ≤ (evalInterval1 e I).lo`.
    Usage: `interval_ext_ge e, supp, I, c` -/
macro "interval_ext_ge" e:term "," supp:term "," I:term "," c:term : tactic =>
  `(tactic| apply expr_ge_of_interval_lo $e $supp $I $c)

/-- Extended interval tactic for < (supports exp).
    Reduces `∀ x ∈ I, f(x) < c` to `(evalInterval1 e I).hi < c`.
    Usage: `interval_ext_lt e, supp, I, c` -/
macro "interval_ext_lt" e:term "," supp:term "," I:term "," c:term : tactic =>
  `(tactic| apply expr_lt_of_interval_hi_lt $e $supp $I $c)

/-- Extended interval tactic for > (supports exp).
    Reduces `∀ x ∈ I, c < f(x)` to `c < (evalInterval1 e I).lo`.
    Usage: `interval_ext_gt e, supp, I, c` -/
macro "interval_ext_gt" e:term "," supp:term "," I:term "," c:term : tactic =>
  `(tactic| apply expr_gt_of_interval_lo_gt $e $supp $I $c)

/-- Extended pointwise tactic for ≤ (supports exp).
    Reduces `f(x) ≤ c` (given x ∈ I) to `(evalInterval1 e I).hi ≤ c`.
    Usage: `interval_ext_le_pt e, supp, I, c, x, hx` -/
macro "interval_ext_le_pt" e:term "," supp:term "," I:term "," c:term "," x:term "," hx:term : tactic =>
  `(tactic| apply expr_le_of_mem_interval $e $supp $I $c $x $hx)

/-- Extended pointwise tactic for ≥ (supports exp).
    Reduces `c ≤ f(x)` (given x ∈ I) to `c ≤ (evalInterval1 e I).lo`.
    Usage: `interval_ext_ge_pt e, supp, I, c, x, hx` -/
macro "interval_ext_ge_pt" e:term "," supp:term "," I:term "," c:term "," x:term "," hx:term : tactic =>
  `(tactic| apply expr_ge_of_mem_interval $e $supp $I $c $x $hx)

end LeanCert.Tactic
