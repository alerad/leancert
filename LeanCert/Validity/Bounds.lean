/-
Copyright (c) 2024 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Engine.IntervalEval
import LeanCert.Engine.AD
import LeanCert.Engine.Optimization.Global
import LeanCert.Engine.RootFinding.Main
import LeanCert.Engine.Integrate
import LeanCert.Meta.ProveContinuous

/-!
# Certificate-Driven Verification

This file provides the infrastructure for certificate-driven verification of
numerical bounds. Instead of Lean searching for a proof, an external agent
(e.g., Python) provides a **Certificate** containing:
- `Expr`: The function f(x)
- `Domain`: The interval I
- `Claim`: E.g., f(I) ⊆ [a, b]
- `ProofParams`: Parameters like Taylor series depth

If the agent determines that exp(x) needs 20 Taylor terms to satisfy a bound,
it passes `taylorDepth := 20` to Lean. Lean runs the computation with that
depth and checks the boolean result via `native_decide`.

## Main definitions

### Boolean Checkers
* `checkUpperBound` - Check if `∀ x ∈ I, f(x) ≤ c` via interval arithmetic
* `checkLowerBound` - Check if `∀ x ∈ I, c ≤ f(x)` via interval arithmetic
* `checkStrictUpperBound` - Check if `∀ x ∈ I, f(x) < c`
* `checkStrictLowerBound` - Check if `∀ x ∈ I, c < f(x)`

### Golden Theorems
* `verify_upper_bound` - Converts `checkUpperBound = true` to semantic proof
* `verify_lower_bound` - Converts `checkLowerBound = true` to semantic proof
* `verify_strict_upper_bound` - Converts `checkStrictUpperBound = true` to semantic proof
* `verify_strict_lower_bound` - Converts `checkStrictLowerBound = true` to semantic proof

## Design

The boolean checkers are fully computable and can be evaluated by `native_decide`.
The golden theorems bridge the gap between the boolean result and the semantic
proof about real numbers.

## Usage

### Manual usage (before tactic implementation):
```lean
example : ∀ x ∈ I01, Expr.eval (fun _ => x) exprExp ≤ 3 :=
  verify_upper_bound exprExp exprExp_core I01 3 { taylorDepth := 15 } (by native_decide)
```

### RPC workflow:
1. Python receives a request: "Prove x·e^x ≤ 5 on [0, 1.2]"
2. Python runs its own fast implementation to find sufficient depth (e.g., 15)
3. Python generates Lean code with the certificate:
   ```lean
   verify_upper_bound myExpr myExpr_core I_0_1_2 5 { taylorDepth := 15 } (by native_decide)
   ```
4. Lean executes, running `evalIntervalCore` with depth 15, checks boolean, closes goal
-/

namespace LeanCert.Validity

open LeanCert.Core
open LeanCert.Engine

/-! ### Boolean Checkers

These are the functions `native_decide` will execute. They return `Bool`, not `Prop`.
-/

/-- Check if an expression is bounded above by `c` on interval `I`.
    Returns `true` iff domain validity holds AND the computed upper bound is ≤ c. -/
def checkUpperBound (e : Expr) (I : IntervalRat) (c : ℚ) (cfg : EvalConfig) : Bool :=
  checkDomainValid1 e I cfg && decide ((evalIntervalCore1 e I cfg).hi ≤ c)

/-- Check if an expression is bounded below by `c` on interval `I`.
    Returns `true` iff domain validity holds AND the computed lower bound is ≥ c. -/
def checkLowerBound (e : Expr) (I : IntervalRat) (c : ℚ) (cfg : EvalConfig) : Bool :=
  checkDomainValid1 e I cfg && decide (c ≤ (evalIntervalCore1 e I cfg).lo)

/-- Check if an expression is strictly bounded above by `c` on interval `I`.
    Returns `true` iff domain validity holds AND the computed upper bound is < c. -/
def checkStrictUpperBound (e : Expr) (I : IntervalRat) (c : ℚ) (cfg : EvalConfig) : Bool :=
  checkDomainValid1 e I cfg && decide ((evalIntervalCore1 e I cfg).hi < c)

/-- Check if an expression is strictly bounded below by `c` on interval `I`.
    Returns `true` iff domain validity holds AND the computed lower bound is > c. -/
def checkStrictLowerBound (e : Expr) (I : IntervalRat) (c : ℚ) (cfg : EvalConfig) : Bool :=
  checkDomainValid1 e I cfg && decide (c < (evalIntervalCore1 e I cfg).lo)

/-! ### Golden Theorems

These theorems convert the boolean `true` from the checkers into semantic proofs
about Real numbers. They are the theorems a tactic will `apply`.
-/

/-- **Golden Theorem for Upper Bounds**

    If `checkUpperBound e I c cfg = true`, then `∀ x ∈ I, Expr.eval (fun _ => x) e ≤ c`.

    This is the key theorem for certificate-driven verification of upper bounds.
    The proof uses:
    1. The boolean check ensures `(evalIntervalCore1 e I cfg).hi ≤ c`
    2. The fundamental correctness theorem ensures `Expr.eval ... e ≤ hi`
    3. Transitivity gives `Expr.eval ... e ≤ c` -/
theorem verify_upper_bound (e : Expr) (hsupp : ExprSupportedCore e)
    (I : IntervalRat) (c : ℚ) (cfg : EvalConfig)
    (h_cert : checkUpperBound e I c cfg = true) :
    ∀ x ∈ I, Expr.eval (fun _ => x) e ≤ c := by
  -- Unpack the boolean check (domain validity AND bound)
  simp only [checkUpperBound, Bool.and_eq_true, decide_eq_true_eq] at h_cert
  have hdom := checkDomainValid1_correct e I cfg h_cert.1
  have hhi := h_cert.2
  -- Apply the tactic-facing lemma which handles the FTIA + transitivity
  exact exprCore_le_of_interval_hi e hsupp I c cfg hdom hhi

/-- **Golden Theorem for Lower Bounds**

    If `checkLowerBound e I c cfg = true`, then `∀ x ∈ I, c ≤ Expr.eval (fun _ => x) e`.

    This is the key theorem for certificate-driven verification of lower bounds.
    The proof uses:
    1. The boolean check ensures `c ≤ (evalIntervalCore1 e I cfg).lo`
    2. The fundamental correctness theorem ensures `lo ≤ Expr.eval ... e`
    3. Transitivity gives `c ≤ Expr.eval ... e` -/
theorem verify_lower_bound (e : Expr) (hsupp : ExprSupportedCore e)
    (I : IntervalRat) (c : ℚ) (cfg : EvalConfig)
    (h_cert : checkLowerBound e I c cfg = true) :
    ∀ x ∈ I, c ≤ Expr.eval (fun _ => x) e := by
  simp only [checkLowerBound, Bool.and_eq_true, decide_eq_true_eq] at h_cert
  have hdom := checkDomainValid1_correct e I cfg h_cert.1
  have hlo := h_cert.2
  exact exprCore_ge_of_interval_lo e hsupp I c cfg hdom hlo

/-- **Golden Theorem for Strict Upper Bounds**

    If `checkStrictUpperBound e I c cfg = true`, then `∀ x ∈ I, Expr.eval (fun _ => x) e < c`. -/
theorem verify_strict_upper_bound (e : Expr) (hsupp : ExprSupportedCore e)
    (I : IntervalRat) (c : ℚ) (cfg : EvalConfig)
    (h_cert : checkStrictUpperBound e I c cfg = true) :
    ∀ x ∈ I, Expr.eval (fun _ => x) e < c := by
  simp only [checkStrictUpperBound, Bool.and_eq_true, decide_eq_true_eq] at h_cert
  have hdom := checkDomainValid1_correct e I cfg h_cert.1
  have hhi := h_cert.2
  exact exprCore_lt_of_interval_hi_lt e hsupp I c cfg hdom hhi

/-- **Golden Theorem for Strict Lower Bounds**

    If `checkStrictLowerBound e I c cfg = true`, then `∀ x ∈ I, c < Expr.eval (fun _ => x) e`. -/
theorem verify_strict_lower_bound (e : Expr) (hsupp : ExprSupportedCore e)
    (I : IntervalRat) (c : ℚ) (cfg : EvalConfig)
    (h_cert : checkStrictLowerBound e I c cfg = true) :
    ∀ x ∈ I, c < Expr.eval (fun _ => x) e := by
  simp only [checkStrictLowerBound, Bool.and_eq_true, decide_eq_true_eq] at h_cert
  have hdom := checkDomainValid1_correct e I cfg h_cert.1
  have hlo := h_cert.2
  exact exprCore_gt_of_interval_lo_gt e hsupp I c cfg hdom hlo

/-! ### Convenience lemmas for pointwise bounds -/

/-- Pointwise upper bound: if check passes and x ∈ I, then f(x) ≤ c -/
theorem verify_upper_bound_pt (e : Expr) (hsupp : ExprSupportedCore e)
    (I : IntervalRat) (c : ℚ) (cfg : EvalConfig) (x : ℝ) (hx : x ∈ I)
    (h_cert : checkUpperBound e I c cfg = true) :
    Expr.eval (fun _ => x) e ≤ c :=
  verify_upper_bound e hsupp I c cfg h_cert x hx

/-- Pointwise lower bound: if check passes and x ∈ I, then c ≤ f(x) -/
theorem verify_lower_bound_pt (e : Expr) (hsupp : ExprSupportedCore e)
    (I : IntervalRat) (c : ℚ) (cfg : EvalConfig) (x : ℝ) (hx : x ∈ I)
    (h_cert : checkLowerBound e I c cfg = true) :
    c ≤ Expr.eval (fun _ => x) e :=
  verify_lower_bound e hsupp I c cfg h_cert x hx

/-! ### Two-sided bounds -/

/-- Check both lower and upper bounds simultaneously -/
def checkBounds (e : Expr) (I : IntervalRat) (lo hi : ℚ) (cfg : EvalConfig) : Bool :=
  checkLowerBound e I lo cfg && checkUpperBound e I hi cfg

/-- Two-sided bound verification: if both checks pass, then lo ≤ f(x) ≤ hi for all x ∈ I -/
theorem verify_bounds (e : Expr) (hsupp : ExprSupportedCore e)
    (I : IntervalRat) (lo hi : ℚ) (cfg : EvalConfig)
    (h_cert : checkBounds e I lo hi cfg = true) :
    ∀ x ∈ I, lo ≤ Expr.eval (fun _ => x) e ∧ Expr.eval (fun _ => x) e ≤ hi := by
  simp only [checkBounds, Bool.and_eq_true] at h_cert
  intro x hx
  exact ⟨verify_lower_bound e hsupp I lo cfg h_cert.1 x hx,
         verify_upper_bound e hsupp I hi cfg h_cert.2 x hx⟩

/-! ### Argmax/Argmin Verification

These theorems support proving `∀ y ∈ I, f(y) ≤ f(x)` (argmax) and
`∀ y ∈ I, f(x) ≤ f(y)` (argmin) via a concrete rational bound.
-/

/-- Check that evaluating f at a point x gives a value ≥ c.
    We evaluate on the point interval [x, x] and check the lower bound.
    This gives us c ≤ f(x) when x is rational. -/
def checkPointLowerBound (e : Expr) (x c : ℚ) (cfg : EvalConfig) : Bool :=
  let Ipt : IntervalRat := ⟨x, x, le_refl x⟩
  checkDomainValid1 e Ipt cfg && decide (c ≤ (evalIntervalCore1 e Ipt cfg).lo)

/-- Check that evaluating f at a point x gives a value ≤ c. -/
def checkPointUpperBound (e : Expr) (x c : ℚ) (cfg : EvalConfig) : Bool :=
  let Ipt : IntervalRat := ⟨x, x, le_refl x⟩
  checkDomainValid1 e Ipt cfg && decide ((evalIntervalCore1 e Ipt cfg).hi ≤ c)

/-- Verify that c ≤ f(x) at a specific point x. -/
theorem verify_point_lower_bound (e : Expr) (hsupp : ExprSupportedCore e)
    (x c : ℚ) (cfg : EvalConfig)
    (h_cert : checkPointLowerBound e x c cfg = true) :
    c ≤ Expr.eval (fun _ => (x : ℝ)) e := by
  simp only [checkPointLowerBound, Bool.and_eq_true, decide_eq_true_eq] at h_cert
  let Ipt : IntervalRat := ⟨x, x, le_refl x⟩
  have hdom := checkDomainValid1_correct e Ipt cfg h_cert.1
  have hlo := h_cert.2
  have hx_mem : (x : ℝ) ∈ Ipt := ⟨le_refl _, le_refl _⟩
  exact exprCore_ge_of_interval_lo e hsupp Ipt c cfg hdom hlo (x : ℝ) hx_mem

/-- Verify that f(x) ≤ c at a specific point x. -/
theorem verify_point_upper_bound (e : Expr) (hsupp : ExprSupportedCore e)
    (x c : ℚ) (cfg : EvalConfig)
    (h_cert : checkPointUpperBound e x c cfg = true) :
    Expr.eval (fun _ => (x : ℝ)) e ≤ c := by
  simp only [checkPointUpperBound, Bool.and_eq_true, decide_eq_true_eq] at h_cert
  let Ipt : IntervalRat := ⟨x, x, le_refl x⟩
  have hdom := checkDomainValid1_correct e Ipt cfg h_cert.1
  have hhi := h_cert.2
  have hx_mem : (x : ℝ) ∈ Ipt := ⟨le_refl _, le_refl _⟩
  exact exprCore_le_of_interval_hi e hsupp Ipt c cfg hdom hhi (x : ℝ) hx_mem

/-- **Argmax Verification Theorem**

    Proves `∀ y ∈ I, f(y) ≤ f(x)` (x is a maximizer) by:
    1. Checking that `∀ y ∈ I, f(y) ≤ c` (the max over I is at most c)
    2. Checking that `c ≤ f(x)` (the value at x is at least c)
    This implies `f(y) ≤ c ≤ f(x)` by transitivity. -/
theorem verify_argmax (e : Expr) (hsupp : ExprSupportedCore e)
    (I : IntervalRat) (x c : ℚ) (cfg : EvalConfig) (_hx : (x : ℝ) ∈ I)
    (h_upper : checkUpperBound e I c cfg = true)
    (h_point : checkPointLowerBound e x c cfg = true) :
    ∀ y ∈ I, Expr.eval (fun _ => y) e ≤ Expr.eval (fun _ => (x : ℝ)) e := by
  intro y hy
  have h1 : Expr.eval (fun _ => y) e ≤ c := verify_upper_bound e hsupp I c cfg h_upper y hy
  have h2 : c ≤ Expr.eval (fun _ => (x : ℝ)) e := verify_point_lower_bound e hsupp x c cfg h_point
  exact le_trans h1 h2

/-- **Argmin Verification Theorem**

    Proves `∀ y ∈ I, f(x) ≤ f(y)` (x is a minimizer) by:
    1. Checking that `∀ y ∈ I, c ≤ f(y)` (the min over I is at least c)
    2. Checking that `f(x) ≤ c` (the value at x is at most c)
    This implies `f(x) ≤ c ≤ f(y)` by transitivity. -/
theorem verify_argmin (e : Expr) (hsupp : ExprSupportedCore e)
    (I : IntervalRat) (x c : ℚ) (cfg : EvalConfig) (_hx : (x : ℝ) ∈ I)
    (h_lower : checkLowerBound e I c cfg = true)
    (h_point : checkPointUpperBound e x c cfg = true) :
    ∀ y ∈ I, Expr.eval (fun _ => (x : ℝ)) e ≤ Expr.eval (fun _ => y) e := by
  intro y hy
  have h1 : Expr.eval (fun _ => (x : ℝ)) e ≤ c := verify_point_upper_bound e hsupp x c cfg h_point
  have h2 : c ≤ Expr.eval (fun _ => y) e := verify_lower_bound e hsupp I c cfg h_lower y hy
  exact le_trans h1 h2

/-! ### ExprSupportedWithInv bounds

Support for expressions with inv, log, atan, arsinh, atanh. These use the
`evalInterval?` evaluator which may return `none` for invalid inputs.

NOTE: These are noncomputable because `evalInterval?` uses Real Taylor approximations.
They cannot be used with `native_decide`. Use the verification theorems directly
in term proofs or with explicit computation.
-/

/-- Check upper bound for ExprSupportedWithInv expressions.
    Returns `true` iff evalInterval?1 succeeds and the upper bound is ≤ c.
    NOTE: Noncomputable - cannot be used with native_decide. -/
def checkUpperBoundWithInv (e : Expr) (I : IntervalRat) (c : ℚ) : Bool :=
  match evalInterval?1 e I with
  | some J => decide (J.hi ≤ c)
  | none => false

/-- Check lower bound for ExprSupportedWithInv expressions.
    Returns `true` iff evalInterval?1 succeeds and the lower bound is ≥ c.
    NOTE: Noncomputable - cannot be used with native_decide. -/
def checkLowerBoundWithInv (e : Expr) (I : IntervalRat) (c : ℚ) : Bool :=
  match evalInterval?1 e I with
  | some J => decide (c ≤ J.lo)
  | none => false

/-- Check strict upper bound for ExprSupportedWithInv expressions.
    NOTE: Noncomputable - cannot be used with native_decide. -/
def checkStrictUpperBoundWithInv (e : Expr) (I : IntervalRat) (c : ℚ) : Bool :=
  match evalInterval?1 e I with
  | some J => decide (J.hi < c)
  | none => false

/-- Check strict lower bound for ExprSupportedWithInv expressions.
    NOTE: Noncomputable - cannot be used with native_decide. -/
def checkStrictLowerBoundWithInv (e : Expr) (I : IntervalRat) (c : ℚ) : Bool :=
  match evalInterval?1 e I with
  | some J => decide (c < J.lo)
  | none => false

/-- Verification theorem for upper bounds with ExprSupportedWithInv. -/
theorem verify_upper_bound_withInv (e : Expr) (hsupp : ExprSupportedWithInv e)
    (I : IntervalRat) (c : ℚ)
    (h_cert : checkUpperBoundWithInv e I c = true) :
    ∀ x ∈ I, Expr.eval (fun _ => x) e ≤ c := by
  simp only [checkUpperBoundWithInv] at h_cert
  split at h_cert
  · next J hsome =>
    simp only [decide_eq_true_eq] at h_cert
    exact evalInterval?_le_of_hi e hsupp I J c hsome h_cert
  · simp at h_cert

/-- Verification theorem for lower bounds with ExprSupportedWithInv. -/
theorem verify_lower_bound_withInv (e : Expr) (hsupp : ExprSupportedWithInv e)
    (I : IntervalRat) (c : ℚ)
    (h_cert : checkLowerBoundWithInv e I c = true) :
    ∀ x ∈ I, c ≤ Expr.eval (fun _ => x) e := by
  simp only [checkLowerBoundWithInv] at h_cert
  split at h_cert
  · next J hsome =>
    simp only [decide_eq_true_eq] at h_cert
    exact evalInterval?_ge_of_lo e hsupp I J c hsome h_cert
  · simp at h_cert

/-- Verification theorem for strict upper bounds with ExprSupportedWithInv. -/
theorem verify_strict_upper_bound_withInv (e : Expr) (hsupp : ExprSupportedWithInv e)
    (I : IntervalRat) (c : ℚ)
    (h_cert : checkStrictUpperBoundWithInv e I c = true) :
    ∀ x ∈ I, Expr.eval (fun _ => x) e < c := by
  simp only [checkStrictUpperBoundWithInv] at h_cert
  split at h_cert
  · next J hsome =>
    simp only [decide_eq_true_eq] at h_cert
    intro x hx
    have hle := evalInterval?_le_of_hi e hsupp I J J.hi hsome (le_refl _) x hx
    have hJ_hi : Expr.eval (fun _ => x) e ≤ J.hi := hle
    calc Expr.eval (fun _ => x) e ≤ J.hi := hJ_hi
      _ < c := by exact_mod_cast h_cert
  · simp at h_cert

/-- Verification theorem for strict lower bounds with ExprSupportedWithInv. -/
theorem verify_strict_lower_bound_withInv (e : Expr) (hsupp : ExprSupportedWithInv e)
    (I : IntervalRat) (c : ℚ)
    (h_cert : checkStrictLowerBoundWithInv e I c = true) :
    ∀ x ∈ I, c < Expr.eval (fun _ => x) e := by
  simp only [checkStrictLowerBoundWithInv] at h_cert
  split at h_cert
  · next J hsome =>
    simp only [decide_eq_true_eq] at h_cert
    intro x hx
    have hge := evalInterval?_ge_of_lo e hsupp I J J.lo hsome (le_refl _) x hx
    have hJ_lo : (J.lo : ℝ) ≤ Expr.eval (fun _ => x) e := hge
    have hc_lt_lo : (c : ℝ) < (J.lo : ℝ) := by exact_mod_cast h_cert
    exact lt_of_lt_of_le hc_lt_lo hJ_lo
  · simp at h_cert

/-- Bridge theorem for Set.Icc upper bounds with ExprSupportedWithInv. -/
theorem verify_upper_bound_Icc_withInv (e : Expr) (hsupp : ExprSupportedWithInv e)
    (lo hi : ℚ) (hle : lo ≤ hi) (c : ℚ)
    (h_cert : checkUpperBoundWithInv e ⟨lo, hi, hle⟩ c = true) :
    ∀ x ∈ Set.Icc (lo : ℝ) (hi : ℝ), Expr.eval (fun _ => x) e ≤ c := by
  intro x hx
  have := verify_upper_bound_withInv e hsupp ⟨lo, hi, hle⟩ c h_cert
  apply this
  rwa [IntervalRat.mem_iff_mem_Icc]

/-- Bridge theorem for Set.Icc lower bounds with ExprSupportedWithInv. -/
theorem verify_lower_bound_Icc_withInv (e : Expr) (hsupp : ExprSupportedWithInv e)
    (lo hi : ℚ) (hle : lo ≤ hi) (c : ℚ)
    (h_cert : checkLowerBoundWithInv e ⟨lo, hi, hle⟩ c = true) :
    ∀ x ∈ Set.Icc (lo : ℝ) (hi : ℝ), c ≤ Expr.eval (fun _ => x) e := by
  intro x hx
  have := verify_lower_bound_withInv e hsupp ⟨lo, hi, hle⟩ c h_cert
  apply this
  rwa [IntervalRat.mem_iff_mem_Icc]

/-- Bridge theorem for Set.Icc strict upper bounds with ExprSupportedWithInv. -/
theorem verify_strict_upper_bound_Icc_withInv (e : Expr) (hsupp : ExprSupportedWithInv e)
    (lo hi : ℚ) (hle : lo ≤ hi) (c : ℚ)
    (h_cert : checkStrictUpperBoundWithInv e ⟨lo, hi, hle⟩ c = true) :
    ∀ x ∈ Set.Icc (lo : ℝ) (hi : ℝ), Expr.eval (fun _ => x) e < c := by
  intro x hx
  have := verify_strict_upper_bound_withInv e hsupp ⟨lo, hi, hle⟩ c h_cert
  apply this
  rwa [IntervalRat.mem_iff_mem_Icc]

/-- Bridge theorem for Set.Icc strict lower bounds with ExprSupportedWithInv. -/
theorem verify_strict_lower_bound_Icc_withInv (e : Expr) (hsupp : ExprSupportedWithInv e)
    (lo hi : ℚ) (hle : lo ≤ hi) (c : ℚ)
    (h_cert : checkStrictLowerBoundWithInv e ⟨lo, hi, hle⟩ c = true) :
    ∀ x ∈ Set.Icc (lo : ℝ) (hi : ℝ), c < Expr.eval (fun _ => x) e := by
  intro x hx
  have := verify_strict_lower_bound_withInv e hsupp ⟨lo, hi, hle⟩ c h_cert
  apply this
  rwa [IntervalRat.mem_iff_mem_Icc]

/-! ### Smart Bounds with Monotonicity

These checkers use derivative information to get tighter bounds at interval endpoints.
If the function is monotonic on the interval, we can evaluate at the appropriate
endpoint to get an exact bound, avoiding Taylor series remainder widening.
-/

/-- Smart lower bound check using monotonicity.
    1. Tries standard interval check first (fastest).
    2. If fails, computes derivative interval.
    3. If derivative > 0 (increasing), checks if f(I.lo) ≥ c.
    4. If derivative < 0 (decreasing), checks if f(I.hi) ≥ c. -/
def checkLowerBoundSmart (e : Expr) (I : IntervalRat) (c : ℚ) (cfg : EvalConfig) : Bool :=
  -- 1. Try standard check first (fastest)
  if checkLowerBound e I c cfg then true
  else
    -- 2. Compute derivative bounds
    let dI := derivIntervalCore e I cfg
    if 0 < dI.lo then
      -- Strictly increasing: minimum is at lo
      -- Evaluate at singleton lo (with domain validity check)
      checkDomainValid1 e (IntervalRat.singleton I.lo) cfg &&
        c ≤ (evalIntervalCore1 e (IntervalRat.singleton I.lo) cfg).lo
    else if dI.hi < 0 then
      -- Strictly decreasing: minimum is at hi (with domain validity check)
      checkDomainValid1 e (IntervalRat.singleton I.hi) cfg &&
        c ≤ (evalIntervalCore1 e (IntervalRat.singleton I.hi) cfg).lo
    else
      false

/-- Smart upper bound check using monotonicity.
    1. Tries standard interval check first.
    2. If fails, computes derivative interval.
    3. If derivative > 0 (increasing), checks if f(I.hi) ≤ c.
    4. If derivative < 0 (decreasing), checks if f(I.lo) ≤ c. -/
def checkUpperBoundSmart (e : Expr) (I : IntervalRat) (c : ℚ) (cfg : EvalConfig) : Bool :=
  if checkUpperBound e I c cfg then true
  else
    let dI := derivIntervalCore e I cfg
    if 0 < dI.lo then
      -- Increasing: max at hi (with domain validity check)
      checkDomainValid1 e (IntervalRat.singleton I.hi) cfg &&
        (evalIntervalCore1 e (IntervalRat.singleton I.hi) cfg).hi ≤ c
    else if dI.hi < 0 then
      -- Decreasing: max at lo (with domain validity check)
      checkDomainValid1 e (IntervalRat.singleton I.lo) cfg &&
        (evalIntervalCore1 e (IntervalRat.singleton I.lo) cfg).hi ≤ c
    else
      false

/-! ### Smart Golden Theorems -/

/-- Helper: For increasing functions, the minimum is at the left endpoint -/
theorem increasing_min_at_left_core (e : Expr) (hsupp : ExprSupported e)
    (I : IntervalRat) (cfg : EvalConfig) (hpos : 0 < (derivIntervalCore e I cfg).lo) :
    ∀ x ∈ I, Expr.eval (fun _ => I.lo) e ≤ Expr.eval (fun _ => x) e := by
  intro x hx
  -- Use the MVT: f(x) - f(lo) = f'(ξ) * (x - lo) for some ξ ∈ (lo, x)
  -- Since f' > 0 and x ≥ lo, we have f(x) ≥ f(lo)
  have hdiff := evalFunc1_differentiable e hsupp
  by_cases heq : (I.lo : ℝ) = x
  · rw [heq]
  · -- x > lo since x ∈ I and x ≠ lo
    have hlo_le_x : (I.lo : ℝ) ≤ x := by
      simp only [IntervalRat.mem_def] at hx; exact hx.1
    have hlo_lt_x : (I.lo : ℝ) < x := lt_of_le_of_ne hlo_le_x heq
    -- Apply MVT
    have hmvt := exists_deriv_eq_slope (evalFunc1 e) hlo_lt_x
      (hdiff.continuous.continuousOn) (fun t _ => (hdiff t).differentiableWithinAt)
    obtain ⟨ξ, hξ_mem, hξ_eq⟩ := hmvt
    -- ξ ∈ (lo, x) ⊆ I, so deriv f ξ ∈ derivIntervalCore
    have hξ_in_I : ξ ∈ I := by
      simp only [Set.mem_Ioo] at hξ_mem
      simp only [IntervalRat.mem_def] at hx ⊢
      constructor
      · exact le_of_lt hξ_mem.1
      · exact le_trans (le_of_lt hξ_mem.2) hx.2
    have hderiv := derivIntervalCore_correct e hsupp I ξ hξ_in_I cfg
    -- deriv f ξ > 0
    have hderiv_pos : deriv (evalFunc1 e) ξ > 0 := by
      simp only [IntervalRat.mem_def] at hderiv
      calc deriv (evalFunc1 e) ξ ≥ (derivIntervalCore e I cfg).lo := hderiv.1
        _ > 0 := by exact_mod_cast hpos
    -- slope = deriv f ξ > 0, so f(x) > f(lo)
    have hslope_pos : (evalFunc1 e x - evalFunc1 e I.lo) / (x - I.lo) > 0 := by
      rw [← hξ_eq]; exact hderiv_pos
    have hdiff_pos : x - (I.lo : ℝ) > 0 := sub_pos.mpr hlo_lt_x
    have hnum_pos : evalFunc1 e x - evalFunc1 e I.lo > 0 := by
      have := div_pos_iff.mp hslope_pos
      cases this with
      | inl h => exact h.1
      | inr h => exact absurd hdiff_pos (not_lt.mpr (le_of_lt h.2))
    simp only [evalFunc1] at hnum_pos ⊢
    linarith

/-- Helper: For decreasing functions, the minimum is at the right endpoint -/
theorem decreasing_min_at_right_core (e : Expr) (hsupp : ExprSupported e)
    (I : IntervalRat) (cfg : EvalConfig) (hneg : (derivIntervalCore e I cfg).hi < 0) :
    ∀ x ∈ I, Expr.eval (fun _ => I.hi) e ≤ Expr.eval (fun _ => x) e := by
  intro x hx
  have hdiff := evalFunc1_differentiable e hsupp
  by_cases heq : x = (I.hi : ℝ)
  · rw [heq]
  · have hx_le_hi : x ≤ (I.hi : ℝ) := by
      simp only [IntervalRat.mem_def] at hx; exact hx.2
    have hx_lt_hi : x < (I.hi : ℝ) := lt_of_le_of_ne hx_le_hi heq
    have hmvt := exists_deriv_eq_slope (evalFunc1 e) hx_lt_hi
      (hdiff.continuous.continuousOn) (fun t _ => (hdiff t).differentiableWithinAt)
    obtain ⟨ξ, hξ_mem, hξ_eq⟩ := hmvt
    have hξ_in_I : ξ ∈ I := by
      simp only [Set.mem_Ioo] at hξ_mem
      simp only [IntervalRat.mem_def] at hx ⊢
      constructor
      · exact le_trans hx.1 (le_of_lt hξ_mem.1)
      · exact le_of_lt hξ_mem.2
    have hderiv := derivIntervalCore_correct e hsupp I ξ hξ_in_I cfg
    have hderiv_neg : deriv (evalFunc1 e) ξ < 0 := by
      simp only [IntervalRat.mem_def] at hderiv
      calc deriv (evalFunc1 e) ξ ≤ (derivIntervalCore e I cfg).hi := hderiv.2
        _ < 0 := by exact_mod_cast hneg
    have hslope_neg : (evalFunc1 e I.hi - evalFunc1 e x) / ((I.hi : ℝ) - x) < 0 := by
      rw [← hξ_eq]; exact hderiv_neg
    have hdiff_pos : (I.hi : ℝ) - x > 0 := sub_pos.mpr hx_lt_hi
    have hnum_neg : evalFunc1 e I.hi - evalFunc1 e x < 0 := by
      have := div_neg_iff.mp hslope_neg
      cases this with
      | inl h => exact absurd hdiff_pos (not_lt.mpr (le_of_lt h.2))
      | inr h => exact h.1
    simp only [evalFunc1] at hnum_neg ⊢
    linarith

/-- Smart lower bound verification using monotonicity -/
theorem verify_lower_bound_smart (e : Expr) (hsupp : ExprSupported e)
    (I : IntervalRat) (c : ℚ) (cfg : EvalConfig)
    (h_cert : checkLowerBoundSmart e I c cfg = true) :
    ∀ x ∈ I, c ≤ Expr.eval (fun _ => x) e := by
  unfold checkLowerBoundSmart at h_cert
  -- Split on the Bool conditions
  split at h_cert
  · -- Case 1: Standard check passed
    rename_i h_std
    exact verify_lower_bound e hsupp.toCore I c cfg h_std
  · -- Standard check failed, simplify the let binding and split
    rename_i h_std_neg
    simp only at h_cert  -- eliminate let binding
    split at h_cert
    · -- Case 2: Derivative strictly positive (increasing)
      rename_i h_pos
      intro x hx
      have hlo_mem : (I.lo : ℝ) ∈ IntervalRat.singleton I.lo := IntervalRat.mem_singleton I.lo
      -- Extract domain validity and bound from the combined check
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h_cert
      have hdom := checkDomainValid1_correct e (IntervalRat.singleton I.lo) cfg h_cert.1
      have hbound := h_cert.2
      have heval := evalIntervalCore1_correct e hsupp.toCore I.lo (IntervalRat.singleton I.lo) hlo_mem cfg hdom
      simp only [IntervalRat.mem_def] at heval
      have hmono := increasing_min_at_left_core e hsupp I cfg h_pos x hx
      calc (c : ℝ) ≤ (evalIntervalCore1 e (IntervalRat.singleton I.lo) cfg).lo := by exact_mod_cast hbound
        _ ≤ Expr.eval (fun _ => I.lo) e := heval.1
        _ ≤ Expr.eval (fun _ => x) e := hmono
    · -- Not increasing, split on decreasing condition
      rename_i h_pos_neg
      split at h_cert
      · -- Case 3: Derivative strictly negative (decreasing)
        rename_i h_neg
        intro x hx
        have hhi_mem : (I.hi : ℝ) ∈ IntervalRat.singleton I.hi := IntervalRat.mem_singleton I.hi
        -- Extract domain validity and bound from the combined check
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h_cert
        have hdom := checkDomainValid1_correct e (IntervalRat.singleton I.hi) cfg h_cert.1
        have hbound := h_cert.2
        have heval := evalIntervalCore1_correct e hsupp.toCore I.hi (IntervalRat.singleton I.hi) hhi_mem cfg hdom
        simp only [IntervalRat.mem_def] at heval
        have hmono := decreasing_min_at_right_core e hsupp I cfg h_neg x hx
        calc (c : ℝ) ≤ (evalIntervalCore1 e (IntervalRat.singleton I.hi) cfg).lo := by exact_mod_cast hbound
          _ ≤ Expr.eval (fun _ => I.hi) e := heval.1
          _ ≤ Expr.eval (fun _ => x) e := hmono
      · -- Neither increasing nor decreasing => impossible since h_cert = true
        exact absurd h_cert Bool.false_ne_true

/-- Helper: For increasing functions, the maximum is at the right endpoint -/
theorem increasing_max_at_right_core (e : Expr) (hsupp : ExprSupported e)
    (I : IntervalRat) (cfg : EvalConfig) (hpos : 0 < (derivIntervalCore e I cfg).lo) :
    ∀ x ∈ I, Expr.eval (fun _ => x) e ≤ Expr.eval (fun _ => I.hi) e := by
  intro x hx
  have hdiff := evalFunc1_differentiable e hsupp
  by_cases heq : x = (I.hi : ℝ)
  · rw [heq]
  · have hx_le_hi : x ≤ (I.hi : ℝ) := by
      simp only [IntervalRat.mem_def] at hx; exact hx.2
    have hx_lt_hi : x < (I.hi : ℝ) := lt_of_le_of_ne hx_le_hi heq
    have hmvt := exists_deriv_eq_slope (evalFunc1 e) hx_lt_hi
      (hdiff.continuous.continuousOn) (fun t _ => (hdiff t).differentiableWithinAt)
    obtain ⟨ξ, hξ_mem, hξ_eq⟩ := hmvt
    have hξ_in_I : ξ ∈ I := by
      simp only [Set.mem_Ioo] at hξ_mem
      simp only [IntervalRat.mem_def] at hx ⊢
      constructor
      · exact le_trans hx.1 (le_of_lt hξ_mem.1)
      · exact le_of_lt hξ_mem.2
    have hderiv := derivIntervalCore_correct e hsupp I ξ hξ_in_I cfg
    have hderiv_pos : deriv (evalFunc1 e) ξ > 0 := by
      simp only [IntervalRat.mem_def] at hderiv
      calc deriv (evalFunc1 e) ξ ≥ (derivIntervalCore e I cfg).lo := hderiv.1
        _ > 0 := by exact_mod_cast hpos
    have hslope_pos : (evalFunc1 e I.hi - evalFunc1 e x) / ((I.hi : ℝ) - x) > 0 := by
      rw [← hξ_eq]; exact hderiv_pos
    have hdiff_pos : (I.hi : ℝ) - x > 0 := sub_pos.mpr hx_lt_hi
    have hnum_pos : evalFunc1 e I.hi - evalFunc1 e x > 0 := by
      have := div_pos_iff.mp hslope_pos
      cases this with
      | inl h => exact h.1
      | inr h => exact absurd hdiff_pos (not_lt.mpr (le_of_lt h.2))
    simp only [evalFunc1] at hnum_pos ⊢
    linarith

/-- Helper: For decreasing functions, the maximum is at the left endpoint -/
theorem decreasing_max_at_left_core (e : Expr) (hsupp : ExprSupported e)
    (I : IntervalRat) (cfg : EvalConfig) (hneg : (derivIntervalCore e I cfg).hi < 0) :
    ∀ x ∈ I, Expr.eval (fun _ => x) e ≤ Expr.eval (fun _ => I.lo) e := by
  intro x hx
  have hdiff := evalFunc1_differentiable e hsupp
  by_cases heq : (I.lo : ℝ) = x
  · rw [heq]
  · have hlo_le_x : (I.lo : ℝ) ≤ x := by
      simp only [IntervalRat.mem_def] at hx; exact hx.1
    have hlo_lt_x : (I.lo : ℝ) < x := lt_of_le_of_ne hlo_le_x heq
    have hmvt := exists_deriv_eq_slope (evalFunc1 e) hlo_lt_x
      (hdiff.continuous.continuousOn) (fun t _ => (hdiff t).differentiableWithinAt)
    obtain ⟨ξ, hξ_mem, hξ_eq⟩ := hmvt
    have hξ_in_I : ξ ∈ I := by
      simp only [Set.mem_Ioo] at hξ_mem
      simp only [IntervalRat.mem_def] at hx ⊢
      constructor
      · exact le_of_lt hξ_mem.1
      · exact le_trans (le_of_lt hξ_mem.2) hx.2
    have hderiv := derivIntervalCore_correct e hsupp I ξ hξ_in_I cfg
    have hderiv_neg : deriv (evalFunc1 e) ξ < 0 := by
      simp only [IntervalRat.mem_def] at hderiv
      calc deriv (evalFunc1 e) ξ ≤ (derivIntervalCore e I cfg).hi := hderiv.2
        _ < 0 := by exact_mod_cast hneg
    have hslope_neg : (evalFunc1 e x - evalFunc1 e I.lo) / (x - I.lo) < 0 := by
      rw [← hξ_eq]; exact hderiv_neg
    have hdiff_pos : x - (I.lo : ℝ) > 0 := sub_pos.mpr hlo_lt_x
    have hnum_neg : evalFunc1 e x - evalFunc1 e I.lo < 0 := by
      have := div_neg_iff.mp hslope_neg
      cases this with
      | inl h => exact absurd hdiff_pos (not_lt.mpr (le_of_lt h.2))
      | inr h => exact h.1
    simp only [evalFunc1] at hnum_neg ⊢
    linarith

/-- Smart upper bound verification using monotonicity -/
theorem verify_upper_bound_smart (e : Expr) (hsupp : ExprSupported e)
    (I : IntervalRat) (c : ℚ) (cfg : EvalConfig)
    (h_cert : checkUpperBoundSmart e I c cfg = true) :
    ∀ x ∈ I, Expr.eval (fun _ => x) e ≤ c := by
  unfold checkUpperBoundSmart at h_cert
  -- Split on the Bool conditions
  split at h_cert
  · -- Case 1: Standard check passed
    rename_i h_std
    exact verify_upper_bound e hsupp.toCore I c cfg h_std
  · -- Standard check failed, simplify the let binding and split
    rename_i h_std_neg
    simp only at h_cert  -- eliminate let binding
    split at h_cert
    · -- Case 2: Derivative strictly positive (increasing), max at hi
      rename_i h_pos
      intro x hx
      have hhi_mem : (I.hi : ℝ) ∈ IntervalRat.singleton I.hi := IntervalRat.mem_singleton I.hi
      -- Extract domain validity and bound from the combined check
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h_cert
      have hdom := checkDomainValid1_correct e (IntervalRat.singleton I.hi) cfg h_cert.1
      have hbound := h_cert.2
      have heval := evalIntervalCore1_correct e hsupp.toCore I.hi (IntervalRat.singleton I.hi) hhi_mem cfg hdom
      simp only [IntervalRat.mem_def] at heval
      have hmono := increasing_max_at_right_core e hsupp I cfg h_pos x hx
      calc Expr.eval (fun _ => x) e ≤ Expr.eval (fun _ => I.hi) e := hmono
        _ ≤ (evalIntervalCore1 e (IntervalRat.singleton I.hi) cfg).hi := heval.2
        _ ≤ c := by exact_mod_cast hbound
    · -- Not increasing, split on decreasing condition
      rename_i h_pos_neg
      split at h_cert
      · -- Case 3: Derivative strictly negative (decreasing), max at lo
        rename_i h_neg
        intro x hx
        have hlo_mem : (I.lo : ℝ) ∈ IntervalRat.singleton I.lo := IntervalRat.mem_singleton I.lo
        -- Extract domain validity and bound from the combined check
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h_cert
        have hdom := checkDomainValid1_correct e (IntervalRat.singleton I.lo) cfg h_cert.1
        have hbound := h_cert.2
        have heval := evalIntervalCore1_correct e hsupp.toCore I.lo (IntervalRat.singleton I.lo) hlo_mem cfg hdom
        simp only [IntervalRat.mem_def] at heval
        have hmono := decreasing_max_at_left_core e hsupp I cfg h_neg x hx
        calc Expr.eval (fun _ => x) e ≤ Expr.eval (fun _ => I.lo) e := hmono
          _ ≤ (evalIntervalCore1 e (IntervalRat.singleton I.lo) cfg).hi := heval.2
          _ ≤ c := by exact_mod_cast hbound
      · -- Neither increasing nor decreasing => impossible since h_cert = true
        exact absurd h_cert Bool.false_ne_true

/-! ### Set.Icc Bridge Theorems

These theorems bridge between IntervalRat-based proofs and Set.Icc goals,
allowing tactics to work with the more natural Set.Icc syntax.
-/

/-- Bridge from IntervalRat proof to Set.Icc upper bound goal -/
theorem verify_upper_bound_Icc (e : Expr) (hsupp : ExprSupported e)
    (lo hi : ℚ) (hle : lo ≤ hi) (c : ℚ) (cfg : EvalConfig)
    (h_cert : checkUpperBoundSmart e ⟨lo, hi, hle⟩ c cfg = true) :
    ∀ x ∈ Set.Icc (lo : ℝ) (hi : ℝ), Expr.eval (fun _ => x) e ≤ c := by
  intro x hx
  have := verify_upper_bound_smart e hsupp ⟨lo, hi, hle⟩ c cfg h_cert
  apply this
  rwa [IntervalRat.mem_iff_mem_Icc]

/-- Bridge from IntervalRat proof to Set.Icc lower bound goal -/
theorem verify_lower_bound_Icc (e : Expr) (hsupp : ExprSupported e)
    (lo hi : ℚ) (hle : lo ≤ hi) (c : ℚ) (cfg : EvalConfig)
    (h_cert : checkLowerBoundSmart e ⟨lo, hi, hle⟩ c cfg = true) :
    ∀ x ∈ Set.Icc (lo : ℝ) (hi : ℝ), c ≤ Expr.eval (fun _ => x) e := by
  intro x hx
  have := verify_lower_bound_smart e hsupp ⟨lo, hi, hle⟩ c cfg h_cert
  apply this
  rwa [IntervalRat.mem_iff_mem_Icc]

/-- Bridge from IntervalRat proof to Set.Icc upper bound goal (Core version).
    This version uses ExprSupportedCore and the basic checkUpperBound (no monotonicity). -/
theorem verify_upper_bound_Icc_core (e : Expr) (hsupp : ExprSupportedCore e)
    (lo hi : ℚ) (hle : lo ≤ hi) (c : ℚ) (cfg : EvalConfig)
    (h_cert : checkUpperBound e ⟨lo, hi, hle⟩ c cfg = true) :
    ∀ x ∈ Set.Icc (lo : ℝ) (hi : ℝ), Expr.eval (fun _ => x) e ≤ c := by
  intro x hx
  have := verify_upper_bound e hsupp ⟨lo, hi, hle⟩ c cfg h_cert
  apply this
  rwa [IntervalRat.mem_iff_mem_Icc]

/-- Bridge from IntervalRat proof to Set.Icc lower bound goal (Core version).
    This version uses ExprSupportedCore and the basic checkLowerBound (no monotonicity). -/
theorem verify_lower_bound_Icc_core (e : Expr) (hsupp : ExprSupportedCore e)
    (lo hi : ℚ) (hle : lo ≤ hi) (c : ℚ) (cfg : EvalConfig)
    (h_cert : checkLowerBound e ⟨lo, hi, hle⟩ c cfg = true) :
    ∀ x ∈ Set.Icc (lo : ℝ) (hi : ℝ), c ≤ Expr.eval (fun _ => x) e := by
  intro x hx
  have := verify_lower_bound e hsupp ⟨lo, hi, hle⟩ c cfg h_cert
  apply this
  rwa [IntervalRat.mem_iff_mem_Icc]

/-- Bridge from IntervalRat proof to Set.Icc strict upper bound goal (Core version). -/
theorem verify_strict_upper_bound_Icc_core (e : Expr) (hsupp : ExprSupportedCore e)
    (lo hi : ℚ) (hle : lo ≤ hi) (c : ℚ) (cfg : EvalConfig)
    (h_cert : checkStrictUpperBound e ⟨lo, hi, hle⟩ c cfg = true) :
    ∀ x ∈ Set.Icc (lo : ℝ) (hi : ℝ), Expr.eval (fun _ => x) e < c := by
  intro x hx
  have := verify_strict_upper_bound e hsupp ⟨lo, hi, hle⟩ c cfg h_cert
  apply this
  rwa [IntervalRat.mem_iff_mem_Icc]

/-- Bridge from IntervalRat proof to Set.Icc strict lower bound goal (Core version). -/
theorem verify_strict_lower_bound_Icc_core (e : Expr) (hsupp : ExprSupportedCore e)
    (lo hi : ℚ) (hle : lo ≤ hi) (c : ℚ) (cfg : EvalConfig)
    (h_cert : checkStrictLowerBound e ⟨lo, hi, hle⟩ c cfg = true) :
    ∀ x ∈ Set.Icc (lo : ℝ) (hi : ℝ), c < Expr.eval (fun _ => x) e := by
  intro x hx
  have := verify_strict_lower_bound e hsupp ⟨lo, hi, hle⟩ c cfg h_cert
  apply this
  rwa [IntervalRat.mem_iff_mem_Icc]

/-! ### Subdivision Theorems

These theorems allow combining bounds from interval subdivisions.
When interval arithmetic gives overly wide bounds, subdividing the domain
and proving bounds on each piece can help.
-/

/-- Combine upper bounds from two halves using splitMid.
    If f ≤ c on both halves, then f ≤ c on the whole interval. -/
theorem verify_upper_bound_split (e : Expr) (hsupp : ExprSupportedCore e)
    (I : IntervalRat) (c : ℚ) (cfg : EvalConfig)
    (h_left : checkUpperBound e (splitMid I).1 c cfg = true)
    (h_right : checkUpperBound e (splitMid I).2 c cfg = true) :
    ∀ x ∈ I, Expr.eval (fun _ => x) e ≤ c := by
  intro x hx
  rcases mem_splitMid hx with hL | hR
  · exact verify_upper_bound e hsupp (splitMid I).1 c cfg h_left x hL
  · exact verify_upper_bound e hsupp (splitMid I).2 c cfg h_right x hR

/-- Combine lower bounds from two halves using splitMid. -/
theorem verify_lower_bound_split (e : Expr) (hsupp : ExprSupportedCore e)
    (I : IntervalRat) (c : ℚ) (cfg : EvalConfig)
    (h_left : checkLowerBound e (splitMid I).1 c cfg = true)
    (h_right : checkLowerBound e (splitMid I).2 c cfg = true) :
    ∀ x ∈ I, c ≤ Expr.eval (fun _ => x) e := by
  intro x hx
  rcases mem_splitMid hx with hL | hR
  · exact verify_lower_bound e hsupp (splitMid I).1 c cfg h_left x hL
  · exact verify_lower_bound e hsupp (splitMid I).2 c cfg h_right x hR

/-- Combine strict upper bounds from two halves. -/
theorem verify_strict_upper_bound_split (e : Expr) (hsupp : ExprSupportedCore e)
    (I : IntervalRat) (c : ℚ) (cfg : EvalConfig)
    (h_left : checkStrictUpperBound e (splitMid I).1 c cfg = true)
    (h_right : checkStrictUpperBound e (splitMid I).2 c cfg = true) :
    ∀ x ∈ I, Expr.eval (fun _ => x) e < c := by
  intro x hx
  rcases mem_splitMid hx with hL | hR
  · exact verify_strict_upper_bound e hsupp (splitMid I).1 c cfg h_left x hL
  · exact verify_strict_upper_bound e hsupp (splitMid I).2 c cfg h_right x hR

/-- Combine strict lower bounds from two halves. -/
theorem verify_strict_lower_bound_split (e : Expr) (hsupp : ExprSupportedCore e)
    (I : IntervalRat) (c : ℚ) (cfg : EvalConfig)
    (h_left : checkStrictLowerBound e (splitMid I).1 c cfg = true)
    (h_right : checkStrictLowerBound e (splitMid I).2 c cfg = true) :
    ∀ x ∈ I, c < Expr.eval (fun _ => x) e := by
  intro x hx
  rcases mem_splitMid hx with hL | hR
  · exact verify_strict_lower_bound e hsupp (splitMid I).1 c cfg h_left x hL
  · exact verify_strict_lower_bound e hsupp (splitMid I).2 c cfg h_right x hR

/-- Bridge from subdivision to Set.Icc upper bound goal. -/
theorem verify_upper_bound_Icc_split (e : Expr) (hsupp : ExprSupportedCore e)
    (lo hi : ℚ) (hle : lo ≤ hi) (c : ℚ) (cfg : EvalConfig)
    (h_left : checkUpperBound e (splitMid ⟨lo, hi, hle⟩).1 c cfg = true)
    (h_right : checkUpperBound e (splitMid ⟨lo, hi, hle⟩).2 c cfg = true) :
    ∀ x ∈ Set.Icc (lo : ℝ) (hi : ℝ), Expr.eval (fun _ => x) e ≤ c := by
  intro x hx
  have := verify_upper_bound_split e hsupp ⟨lo, hi, hle⟩ c cfg h_left h_right
  apply this
  rwa [IntervalRat.mem_iff_mem_Icc]

/-- Bridge from subdivision to Set.Icc lower bound goal. -/
theorem verify_lower_bound_Icc_split (e : Expr) (hsupp : ExprSupportedCore e)
    (lo hi : ℚ) (hle : lo ≤ hi) (c : ℚ) (cfg : EvalConfig)
    (h_left : checkLowerBound e (splitMid ⟨lo, hi, hle⟩).1 c cfg = true)
    (h_right : checkLowerBound e (splitMid ⟨lo, hi, hle⟩).2 c cfg = true) :
    ∀ x ∈ Set.Icc (lo : ℝ) (hi : ℝ), c ≤ Expr.eval (fun _ => x) e := by
  intro x hx
  have := verify_lower_bound_split e hsupp ⟨lo, hi, hle⟩ c cfg h_left h_right
  apply this
  rwa [IntervalRat.mem_iff_mem_Icc]

/-- Bridge from subdivision to Set.Icc strict upper bound goal. -/
theorem verify_strict_upper_bound_Icc_split (e : Expr) (hsupp : ExprSupportedCore e)
    (lo hi : ℚ) (hle : lo ≤ hi) (c : ℚ) (cfg : EvalConfig)
    (h_left : checkStrictUpperBound e (splitMid ⟨lo, hi, hle⟩).1 c cfg = true)
    (h_right : checkStrictUpperBound e (splitMid ⟨lo, hi, hle⟩).2 c cfg = true) :
    ∀ x ∈ Set.Icc (lo : ℝ) (hi : ℝ), Expr.eval (fun _ => x) e < c := by
  intro x hx
  have := verify_strict_upper_bound_split e hsupp ⟨lo, hi, hle⟩ c cfg h_left h_right
  apply this
  rwa [IntervalRat.mem_iff_mem_Icc]

/-- Bridge from subdivision to Set.Icc strict lower bound goal. -/
theorem verify_strict_lower_bound_Icc_split (e : Expr) (hsupp : ExprSupportedCore e)
    (lo hi : ℚ) (hle : lo ≤ hi) (c : ℚ) (cfg : EvalConfig)
    (h_left : checkStrictLowerBound e (splitMid ⟨lo, hi, hle⟩).1 c cfg = true)
    (h_right : checkStrictLowerBound e (splitMid ⟨lo, hi, hle⟩).2 c cfg = true) :
    ∀ x ∈ Set.Icc (lo : ℝ) (hi : ℝ), c < Expr.eval (fun _ => x) e := by
  intro x hx
  have := verify_strict_lower_bound_split e hsupp ⟨lo, hi, hle⟩ c cfg h_left h_right
  apply this
  rwa [IntervalRat.mem_iff_mem_Icc]

/-! ### General Split Theorems

These theorems work with arbitrary split points, not just midpoints.
Useful for adaptive subdivision algorithms.
-/

/-- Any x in [lo, hi] is in [lo, mid] or [mid, hi] for any mid in between -/
theorem mem_split_general {lo mid hi : ℚ} {x : ℝ}
    (hx : x ∈ Set.Icc (lo : ℝ) (hi : ℝ))
    (_hLeMid : lo ≤ mid) (_hMidLe : mid ≤ hi) :
    x ∈ Set.Icc (lo : ℝ) (mid : ℝ) ∨ x ∈ Set.Icc (mid : ℝ) (hi : ℝ) := by
  simp only [Set.mem_Icc] at hx ⊢
  by_cases h : x ≤ mid
  · left; exact ⟨hx.1, h⟩
  · right
    push_neg at h
    exact ⟨le_of_lt h, hx.2⟩

/-- Combine upper bounds from two arbitrary adjacent intervals.
    If f ≤ c on [lo, mid] and f ≤ c on [mid, hi], then f ≤ c on [lo, hi]. -/
theorem verify_upper_bound_general_split (e : Expr) (hsupp : ExprSupportedCore e)
    (lo mid hi : ℚ) (hLo : lo ≤ mid) (hHi : mid ≤ hi) (_hle : lo ≤ hi) (c : ℚ) (cfg : EvalConfig)
    (h_left : checkUpperBound e ⟨lo, mid, hLo⟩ c cfg = true)
    (h_right : checkUpperBound e ⟨mid, hi, hHi⟩ c cfg = true) :
    ∀ x ∈ Set.Icc (lo : ℝ) (hi : ℝ), Expr.eval (fun _ => x) e ≤ c := by
  intro x hx
  rcases mem_split_general hx hLo hHi with hL | hR
  · have := verify_upper_bound e hsupp ⟨lo, mid, hLo⟩ c cfg h_left
    apply this; rwa [IntervalRat.mem_iff_mem_Icc]
  · have := verify_upper_bound e hsupp ⟨mid, hi, hHi⟩ c cfg h_right
    apply this; rwa [IntervalRat.mem_iff_mem_Icc]

/-- Combine lower bounds from two arbitrary adjacent intervals. -/
theorem verify_lower_bound_general_split (e : Expr) (hsupp : ExprSupportedCore e)
    (lo mid hi : ℚ) (hLo : lo ≤ mid) (hHi : mid ≤ hi) (_hle : lo ≤ hi) (c : ℚ) (cfg : EvalConfig)
    (h_left : checkLowerBound e ⟨lo, mid, hLo⟩ c cfg = true)
    (h_right : checkLowerBound e ⟨mid, hi, hHi⟩ c cfg = true) :
    ∀ x ∈ Set.Icc (lo : ℝ) (hi : ℝ), c ≤ Expr.eval (fun _ => x) e := by
  intro x hx
  rcases mem_split_general hx hLo hHi with hL | hR
  · have := verify_lower_bound e hsupp ⟨lo, mid, hLo⟩ c cfg h_left
    apply this; rwa [IntervalRat.mem_iff_mem_Icc]
  · have := verify_lower_bound e hsupp ⟨mid, hi, hHi⟩ c cfg h_right
    apply this; rwa [IntervalRat.mem_iff_mem_Icc]

/-- Combine strict upper bounds from two arbitrary adjacent intervals. -/
theorem verify_strict_upper_bound_general_split (e : Expr) (hsupp : ExprSupportedCore e)
    (lo mid hi : ℚ) (hLo : lo ≤ mid) (hHi : mid ≤ hi) (_hle : lo ≤ hi) (c : ℚ) (cfg : EvalConfig)
    (h_left : checkStrictUpperBound e ⟨lo, mid, hLo⟩ c cfg = true)
    (h_right : checkStrictUpperBound e ⟨mid, hi, hHi⟩ c cfg = true) :
    ∀ x ∈ Set.Icc (lo : ℝ) (hi : ℝ), Expr.eval (fun _ => x) e < c := by
  intro x hx
  rcases mem_split_general hx hLo hHi with hL | hR
  · have := verify_strict_upper_bound e hsupp ⟨lo, mid, hLo⟩ c cfg h_left
    apply this; rwa [IntervalRat.mem_iff_mem_Icc]
  · have := verify_strict_upper_bound e hsupp ⟨mid, hi, hHi⟩ c cfg h_right
    apply this; rwa [IntervalRat.mem_iff_mem_Icc]

/-- Combine strict lower bounds from two arbitrary adjacent intervals. -/
theorem verify_strict_lower_bound_general_split (e : Expr) (hsupp : ExprSupportedCore e)
    (lo mid hi : ℚ) (hLo : lo ≤ mid) (hHi : mid ≤ hi) (_hle : lo ≤ hi) (c : ℚ) (cfg : EvalConfig)
    (h_left : checkStrictLowerBound e ⟨lo, mid, hLo⟩ c cfg = true)
    (h_right : checkStrictLowerBound e ⟨mid, hi, hHi⟩ c cfg = true) :
    ∀ x ∈ Set.Icc (lo : ℝ) (hi : ℝ), c < Expr.eval (fun _ => x) e := by
  intro x hx
  rcases mem_split_general hx hLo hHi with hL | hR
  · have := verify_strict_lower_bound e hsupp ⟨lo, mid, hLo⟩ c cfg h_left
    apply this; rwa [IntervalRat.mem_iff_mem_Icc]
  · have := verify_strict_lower_bound e hsupp ⟨mid, hi, hHi⟩ c cfg h_right
    apply this; rwa [IntervalRat.mem_iff_mem_Icc]

end LeanCert.Validity

/-! ## Global Optimization Certificates

These checkers and theorems extend the certificate pattern to multivariate
global optimization over n-dimensional boxes.
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

/-! ## Root Finding Certificates

These checkers and theorems provide certificate-driven verification for
root existence and uniqueness.
-/

namespace LeanCert.Validity.RootFinding

open LeanCert.Core
open LeanCert.Engine

/-! ### Configuration for root finding certificates -/

/-- Configuration for root-finding checks -/
structure RootConfig where
  /-- Maximum bisection depth -/
  maxDepth : Nat := 20
  /-- Taylor depth for interval evaluation -/
  taylorDepth : Nat := 10
  deriving Repr, Inhabited

/-- Configuration for Newton uniqueness checks -/
structure NewtonConfig where
  /-- Number of Newton iterations -/
  iterations : Nat := 5
  /-- Taylor model degree -/
  tmDegree : Nat := 1
  deriving Repr, Inhabited

/-! ### Boolean Checkers for Root Finding -/

/-- Check if expression has a sign change on interval (indicating a root).
    Uses interval arithmetic to check if f(lo) and f(hi) have opposite signs. -/
def checkSignChange (e : Expr) (I : IntervalRat) (cfg : EvalConfig) : Bool :=
  -- Check domain validity at endpoints
  checkDomainValid1 e (IntervalRat.singleton I.lo) cfg &&
  checkDomainValid1 e (IntervalRat.singleton I.hi) cfg &&
  -- Evaluate f at endpoints
  let f_lo := evalIntervalCore1 e (IntervalRat.singleton I.lo) cfg
  let f_hi := evalIntervalCore1 e (IntervalRat.singleton I.hi) cfg
  -- Opposite signs: f_lo.hi < 0 and f_hi.lo > 0, or f_lo.lo > 0 and f_hi.hi < 0
  ((f_lo.hi < 0 && 0 < f_hi.lo) || (f_hi.hi < 0 && 0 < f_lo.lo))

/-- Check if interval definitely has no root (function has constant sign).
    Returns `true` if the function's interval evaluation doesn't contain 0. -/
def checkNoRoot (e : Expr) (I : IntervalRat) (cfg : EvalConfig) : Bool :=
  checkDomainValid1 e I cfg && (let fI := evalIntervalCore1 e I cfg; fI.hi < 0 || 0 < fI.lo)

/-! ### Computable Newton Step for Unique Root Verification -/

/-- Computable Newton step using `evalIntervalCore1` and `derivIntervalCore`.

    This is the computable equivalent of `newtonStepSimple`. It performs one
    interval Newton iteration: N(I) = c - f(c)/f'(I) where c = midpoint(I).

    Returns `none` if the derivative interval contains 0 (can't safely divide).
    Returns `some (I ∩ N)` otherwise. -/
def newtonStepCore (e : Expr) (I : IntervalRat) (cfg : EvalConfig := default) : Option IntervalRat :=
  let c := I.midpoint
  -- Evaluate f(c) using singleton interval
  let fc := evalIntervalCore1 e (IntervalRat.singleton c) cfg
  -- Get derivative interval on I
  let dI := derivIntervalCore e I cfg
  -- If derivative interval contains zero, we can't safely divide
  if hzero : IntervalRat.containsZero dI then
    none
  else
    let dNonzero : IntervalRat.IntervalRatNonzero :=
      { lo := dI.lo, hi := dI.hi, le := dI.le, nonzero := hzero }
    let dInv := IntervalRat.invNonzero dNonzero
    let Q := IntervalRat.mul fc dInv
    let N : IntervalRat :=
      { lo := c - Q.hi
        hi := c - Q.lo
        le := by linarith [Q.le] }
    IntervalRat.intersect I N

/-- Extract structure from newtonStepCore. -/
lemma newtonStepCore_extract (e : Expr) (I N : IntervalRat) (cfg : EvalConfig)
    (hCore : newtonStepCore e I cfg = some N) :
    let c := I.midpoint
    let fc := evalIntervalCore1 e (IntervalRat.singleton c) cfg
    let dI := derivIntervalCore e I cfg
    ∃ (hdI_nonzero : ¬dI.containsZero),
      let dNonzero : IntervalRat.IntervalRatNonzero := ⟨dI, hdI_nonzero⟩
      let Q := IntervalRat.mul fc (IntervalRat.invNonzero dNonzero)
      N.lo = max I.lo (c - Q.hi) ∧ N.hi = min I.hi (c - Q.lo) := by
  -- Unfold the definition of newtonStepCore
  unfold newtonStepCore at hCore
  -- The dite splits on containsZero
  by_cases hzero : (derivIntervalCore e I cfg).containsZero
  · -- If dI contains zero, newtonStepCore returns none, contradiction
    simp only [hzero, ↓reduceDIte, reduceCtorEq] at hCore
  · -- If dI doesn't contain zero, we get an intersection
    simp only [hzero, dite_false] at hCore
    use hzero
    -- hCore : IntervalRat.intersect I ⟨c - Q.hi, c - Q.lo, _⟩ = some N
    simp only [IntervalRat.intersect] at hCore
    split at hCore
    · -- The intersection succeeded
      rename_i hintersect
      simp only [Option.some.injEq] at hCore
      constructor
      · exact congrArg IntervalRat.lo hCore.symm
      · exact congrArg IntervalRat.hi hCore.symm
    · -- The intersection failed, contradiction
      simp only [reduceCtorEq] at hCore

/-- Computable check if Newton iteration contracts.
    Returns `true` if `newtonStepCore` produces N with I.lo < N.lo and N.hi < I.hi.

    This can be used with `native_decide` for unique root verification. -/
def checkNewtonContractsCore (e : Expr) (I : IntervalRat) (cfg : EvalConfig := default) : Bool :=
  match newtonStepCore e I cfg with
  | none => false
  | some N => decide (I.lo < N.lo && N.hi < I.hi)

/-- Check if Newton iteration contracts, indicating unique root existence.
    Returns `true` if the Newton step from I gives N ⊂ interior(I).

    Note: This is noncomputable because newtonStepSimple uses derivInterval
    which uses evalInterval (noncomputable). For native_decide, we would need
    a fully computable version using evalIntervalCore. -/
noncomputable def checkNewtonContracts (e : Expr) (I : IntervalRat) (_cfg : NewtonConfig) : Bool :=
  match newtonStepSimple e I 0 with
  | none => false  -- Newton step failed (derivative interval contains 0)
  | some N =>
    -- Check strict contraction: N.lo > I.lo and N.hi < I.hi
    decide (I.lo < N.lo && N.hi < I.hi)

/-! ### Golden Theorems for Root Finding -/

/-- **Golden Theorem for No Root**

    If `checkNoRoot e I cfg = true`, then `∀ x ∈ I, Expr.eval (fun _ => x) e ≠ 0`. -/
theorem verify_no_root (e : Expr) (hsupp : ExprSupportedCore e)
    (I : IntervalRat) (cfg : EvalConfig)
    (h_cert : checkNoRoot e I cfg = true) :
    ∀ x ∈ I, Expr.eval (fun _ => x) e ≠ 0 := by
  simp only [checkNoRoot, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h_cert
  intro x hx hcontra
  have hdom := checkDomainValid1_correct e I cfg h_cert.1
  have heval := evalIntervalCore1_correct e hsupp x I hx cfg hdom
  simp only [IntervalRat.mem_def] at heval
  cases h_cert.2 with
  | inl hhi =>
    -- f's interval hi < 0, so f(x) ≤ hi < 0, contradiction with f(x) = 0
    have hhi_real : ((evalIntervalCore1 e I cfg).hi : ℝ) < 0 := by exact_mod_cast hhi
    have hf_neg : Expr.eval (fun _ => x) e < 0 := lt_of_le_of_lt heval.2 hhi_real
    rw [hcontra] at hf_neg
    exact absurd hf_neg (lt_irrefl 0)
  | inr hlo =>
    -- 0 < f's interval lo, so 0 < lo ≤ f(x), contradiction with f(x) = 0
    have hlo_real : (0 : ℝ) < (evalIntervalCore1 e I cfg).lo := by exact_mod_cast hlo
    have hf_pos : 0 < Expr.eval (fun _ => x) e := lt_of_lt_of_le hlo_real heval.1
    rw [hcontra] at hf_pos
    exact absurd hf_pos (lt_irrefl 0)

/-- **Golden Theorem for Newton Contraction (Unique Root Existence)**

    If `checkNewtonContracts e I cfg = true`, then there exists a unique root in I.

    This theorem requires additional hypotheses that the external checker must verify:
    - The expression is supported
    - The expression uses only variable 0
    - The function is continuous on I -/
theorem verify_unique_root_newton (e : Expr) (hsupp : ExprSupported e)
    (hvar0 : UsesOnlyVar0 e) (I : IntervalRat) (cfg : NewtonConfig)
    (hCont : ContinuousOn (fun x => Expr.eval (fun _ => x) e) (Set.Icc I.lo I.hi))
    (h_cert : checkNewtonContracts e I cfg = true) :
    ∃! x, x ∈ I ∧ Expr.eval (fun _ => x) e = 0 := by
  simp only [checkNewtonContracts] at h_cert
  -- Extract the Newton step result
  split at h_cert
  · -- Newton step returned none
    exact absurd h_cert Bool.false_ne_true
  · -- Newton step returned some N
    rename_i N hN
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h_cert
    -- We have contraction: I.lo < N.lo and N.hi < I.hi
    have hContract : N.lo > I.lo ∧ N.hi < I.hi := ⟨h_cert.1, h_cert.2⟩
    -- Apply newton_contraction_unique_root directly
    -- This theorem already proves ∃! x, x ∈ I ∧ ... (uniqueness in I, not just N)
    exact newton_contraction_unique_root e hsupp hvar0 I N (Or.inr hN) hContract hCont

/-! ### Core MVT Lemmas for Newton Contraction Contradiction

These lemmas prove that if Newton contraction holds but f has constant sign at both
endpoints, we get a contradiction via MVT bounds.

Key insight: If f doesn't change sign on I (both endpoints positive or both negative),
then by monotonicity (from nonzero derivative), f has constant sign throughout I.
But Newton contraction requires specific quotient bounds that MVT proves are violated. -/

/-- MVT lower bound using derivIntervalCore: if f'(ξ) ∈ [dI.lo, dI.hi] for all ξ ∈ I,
    then f(y) - f(x) ≥ dI.lo * (y - x) for x ≤ y in I. -/
lemma mvt_lower_bound_core (e : Expr) (hsupp : ExprSupported e)
    (I : IntervalRat) (cfg : EvalConfig)
    (hCont : ContinuousOn (evalFunc1 e) (Set.Icc I.lo I.hi)) :
    ∀ x y, x ∈ I → y ∈ I → x ≤ y →
      ((derivIntervalCore e I cfg).lo : ℝ) * (y - x) ≤ evalFunc1 e y - evalFunc1 e x := by
  intro x y hx hy hxy
  set dI := derivIntervalCore e I cfg
  have hderiv_bound : ∀ ξ ∈ I, (dI.lo : ℝ) ≤ deriv (evalFunc1 e) ξ := fun ξ hξ =>
    (derivIntervalCore_correct e hsupp I ξ hξ cfg).1
  -- Use Mathlib's MVT
  have hConvex : Convex ℝ (Set.Icc (I.lo : ℝ) I.hi) := convex_Icc _ _
  have hDiff : DifferentiableOn ℝ (evalFunc1 e) (interior (Set.Icc (I.lo : ℝ) I.hi)) := by
    have hdiff := evalFunc1_differentiable e hsupp
    exact hdiff.differentiableOn
  have hC' : ∀ ξ ∈ interior (Set.Icc (I.lo : ℝ) I.hi), (dI.lo : ℝ) ≤ deriv (evalFunc1 e) ξ := by
    intro ξ hξ
    apply hderiv_bound
    exact @interior_subset ℝ _ (Set.Icc I.lo I.hi) ξ hξ
  have hx_Icc : x ∈ Set.Icc (I.lo : ℝ) I.hi := by simp only [IntervalRat.mem_def] at hx; exact hx
  have hy_Icc : y ∈ Set.Icc (I.lo : ℝ) I.hi := by simp only [IntervalRat.mem_def] at hy; exact hy
  exact hConvex.mul_sub_le_image_sub_of_le_deriv hCont hDiff hC' x hx_Icc y hy_Icc hxy

/-- MVT upper bound using derivIntervalCore: if f'(ξ) ∈ [dI.lo, dI.hi] for all ξ ∈ I,
    then f(y) - f(x) ≤ dI.hi * (y - x) for x ≤ y in I. -/
lemma mvt_upper_bound_core (e : Expr) (hsupp : ExprSupported e)
    (I : IntervalRat) (cfg : EvalConfig)
    (hCont : ContinuousOn (evalFunc1 e) (Set.Icc I.lo I.hi)) :
    ∀ x y, x ∈ I → y ∈ I → x ≤ y →
      evalFunc1 e y - evalFunc1 e x ≤ ((derivIntervalCore e I cfg).hi : ℝ) * (y - x) := by
  intro x y hx hy hxy
  set dI := derivIntervalCore e I cfg
  have hderiv_bound : ∀ ξ ∈ I, deriv (evalFunc1 e) ξ ≤ (dI.hi : ℝ) := fun ξ hξ =>
    (derivIntervalCore_correct e hsupp I ξ hξ cfg).2
  have hConvex : Convex ℝ (Set.Icc (I.lo : ℝ) I.hi) := convex_Icc _ _
  have hDiff : DifferentiableOn ℝ (evalFunc1 e) (interior (Set.Icc (I.lo : ℝ) I.hi)) := by
    have hdiff := evalFunc1_differentiable e hsupp
    exact hdiff.differentiableOn
  have hC' : ∀ ξ ∈ interior (Set.Icc (I.lo : ℝ) I.hi), deriv (evalFunc1 e) ξ ≤ (dI.hi : ℝ) := by
    intro ξ hξ
    apply hderiv_bound
    exact @interior_subset ℝ _ (Set.Icc I.lo I.hi) ξ hξ
  have hx_Icc : x ∈ Set.Icc (I.lo : ℝ) I.hi := by simp only [IntervalRat.mem_def] at hx; exact hx
  have hy_Icc : y ∈ Set.Icc (I.lo : ℝ) I.hi := by simp only [IntervalRat.mem_def] at hy; exact hy
  exact hConvex.image_sub_le_mul_sub_of_deriv_le hCont hDiff hC' x hx_Icc y hy_Icc hxy

/-- **Golden Theorem for Computable Newton Contraction (Unique Root Existence)**

    This version assumes *both*:
    1. Core contraction check (computable, used by search/external tools)
    2. Non-core contraction check (used for the formal proof, via
       `verify_unique_root_newton`).

    The formal proof only relies on the non-core checker; the core checker
    can be used by the external agent for optimization but is not needed
    logically. This avoids the need to prove complex MVT-based contradiction
    lemmas for the Core interval functions.

    Note: The `h_cert_core` hypothesis is not used in the proof but is kept
    in the signature so the certificate format can include it for external
    tooling purposes. -/
theorem verify_unique_root_core (e : Expr) (hsupp : ExprSupported e)
    (hvar0 : UsesOnlyVar0 e) (I : IntervalRat)
    (evalCfg : EvalConfig) (newtonCfg : NewtonConfig)
    (hCont : ContinuousOn (fun x => Expr.eval (fun _ => x) e) (Set.Icc I.lo I.hi))
    (_h_cert_core : checkNewtonContractsCore e I evalCfg = true)
    (h_cert_newton : checkNewtonContracts e I newtonCfg = true) :
    ∃! x, x ∈ I ∧ Expr.eval (fun _ => x) e = 0 := by
  -- We only *use* `h_cert_newton`. The core certificate is present for external tooling.
  exact verify_unique_root_newton e hsupp hvar0 I newtonCfg hCont h_cert_newton

/-! ### Fully Computable Unique Root Verification

The following theorems provide a **fully computable** path to proving unique root existence
using only `checkNewtonContractsCore`. This allows `native_decide` to work without requiring
noncomputable functions like `Real.exp` or `Real.log`. -/

/-- Newton step preserves roots when using Core evaluation functions.
    If x is a root in I and newtonStepCore produces N, then x ∈ N. -/
theorem newton_preserves_root_core (e : Expr) (hsupp : ExprSupported e) (hvar0 : UsesOnlyVar0 e)
    (I N : IntervalRat) (cfg : EvalConfig)
    (hStep : newtonStepCore e I cfg = some N)
    (x : ℝ) (hx : x ∈ I) (hroot : Expr.eval (fun _ => x) e = 0) :
    x ∈ N := by
  -- Extract structure from newtonStepCore
  obtain ⟨hdI_nonzero, hN_lo, hN_hi⟩ := newtonStepCore_extract e I N cfg hStep

  -- Define components matching abstract theorem
  let c := I.midpoint
  let fc := evalIntervalCore1 e (IntervalRat.singleton c) cfg
  let dI := derivIntervalCore e I cfg

  -- Verify premises for abstract theorem
  have hc_in_I : (c : ℝ) ∈ I := IntervalRat.midpoint_mem I

  -- 1. f(c) ∈ fc via evalIntervalCore1_correct
  have hfc_correct : evalFunc1 e c ∈ fc := by
    simp only [evalFunc1]
    exact evalIntervalCore1_correct e hsupp.toCore c (IntervalRat.singleton c) (IntervalRat.mem_singleton c) cfg (exprSupported_domainValid1 hsupp _ cfg)

  -- 2. f'(ξ) ∈ dI for all ξ ∈ I via derivIntervalCore_correct
  have hdI_correct : ∀ ξ ∈ I, deriv (evalFunc1 e) ξ ∈ dI := fun ξ hξ =>
    derivIntervalCore_correct e hsupp I ξ hξ cfg

  -- Apply abstract preservation lemma
  have hroot' : evalFunc1 e x = 0 := hroot
  have h_in_Newton := newton_operator_preserves_root e hsupp hvar0
    I c fc dI hc_in_I hfc_correct hdI_correct hdI_nonzero x hx hroot'

  -- Now we need to show x ∈ N where N = I ∩ Newton
  -- h_in_Newton shows x is in the Newton interval [c - Q.hi, c - Q.lo]
  -- Combined with hx : x ∈ I, we get x ∈ I ∩ Newton = N
  have hx_in_intersect := IntervalRat.mem_intersect hx h_in_Newton
  obtain ⟨K, hK_eq, hx_in_K⟩ := hx_in_intersect

  -- Show x ∈ N by using the intersection logic
  -- Both hStep and hK_eq refer to the same intersect
  unfold newtonStepCore at hStep
  simp only [hdI_nonzero, dite_false] at hStep
  -- Now hStep : IntervalRat.intersect I (I.newtonInterval fc dI) = some N
  -- And hK_eq : IntervalRat.intersect I (I.newtonInterval fc dI) = some K
  have hN_eq_K : N = K := by
    rw [hStep] at hK_eq
    simp only [Option.some.injEq] at hK_eq
    exact hK_eq
  rw [hN_eq_K]
  exact hx_in_K

/-- If Newton step succeeds, there's at most one root in I (via Rolle's theorem).
    This uses the fact that if dI doesn't contain zero, the derivative is nonzero
    everywhere on I, so f is strictly monotonic. -/
theorem newton_step_core_at_most_one_root (e : Expr) (hsupp : ExprSupported e) (_hvar0 : UsesOnlyVar0 e)
    (I : IntervalRat) (cfg : EvalConfig)
    (hStep : ∃ N, newtonStepCore e I cfg = some N)
    (hCont : ContinuousOn (fun x => Expr.eval (fun _ => x) e) (Set.Icc I.lo I.hi))
    (x y : ℝ) (hx : x ∈ I) (hy : y ∈ I)
    (hx_root : Expr.eval (fun _ => x) e = 0) (hy_root : Expr.eval (fun _ => y) e = 0) :
    x = y := by
  obtain ⟨N, hN⟩ := hStep
  -- If step succeeds, dI doesn't contain zero
  set dI := derivIntervalCore e I cfg with hdI_def
  by_cases hzero : dI.containsZero
  · -- If dI contains zero, newtonStepCore returns none, but hN says it's some N
    unfold newtonStepCore at hN
    simp only [← hdI_def, dif_pos hzero, reduceCtorEq] at hN
  · -- dI doesn't contain zero, so derivative is nonzero everywhere on I
    simp only [IntervalRat.containsZero, not_and_or, not_le] at hzero

    by_contra hne
    -- If x ≠ y, Rolle's theorem gives ξ between them with f'(ξ) = 0
    simp only [IntervalRat.mem_def] at hx hy
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · -- x < y case
      have hIcc_sub : Set.Icc x y ⊆ Set.Icc (I.lo : ℝ) I.hi := by
        intro z ⟨hzlo, hzhi⟩
        exact ⟨le_trans hx.1 hzlo, le_trans hzhi hy.2⟩
      have hCont' : ContinuousOn (evalFunc1 e) (Set.Icc x y) := hCont.mono hIcc_sub
      have hf_eq : evalFunc1 e x = evalFunc1 e y := by
        simp only [evalFunc1]; rw [hx_root, hy_root]
      obtain ⟨ξ, hξ_mem, hξ_deriv⟩ := @exists_deriv_eq_zero (evalFunc1 e) x y hlt hCont' hf_eq
      -- ξ ∈ (x, y) ⊆ I
      have hξ_in_I : ξ ∈ I := by
        simp only [IntervalRat.mem_def]
        exact ⟨le_trans hx.1 (le_of_lt hξ_mem.1), le_trans (le_of_lt hξ_mem.2) hy.2⟩
      -- f'(ξ) ∈ dI but f'(ξ) = 0
      have hderiv_in := derivIntervalCore_correct e hsupp I ξ hξ_in_I cfg
      rw [hξ_deriv] at hderiv_in
      simp only [IntervalRat.mem_def] at hderiv_in
      rcases hzero with hlo_pos | hhi_neg
      · have hcast : (0 : ℝ) < dI.lo := by exact_mod_cast hlo_pos
        linarith [hderiv_in.1]
      · have hcast : (dI.hi : ℝ) < 0 := by exact_mod_cast hhi_neg
        linarith [hderiv_in.2]
    · -- y < x case (symmetric)
      have hIcc_sub : Set.Icc y x ⊆ Set.Icc (I.lo : ℝ) I.hi := by
        intro z ⟨hzlo, hzhi⟩
        exact ⟨le_trans hy.1 hzlo, le_trans hzhi hx.2⟩
      have hCont' : ContinuousOn (evalFunc1 e) (Set.Icc y x) := hCont.mono hIcc_sub
      have hf_eq : evalFunc1 e y = evalFunc1 e x := by
        simp only [evalFunc1]; rw [hy_root, hx_root]
      obtain ⟨ξ, hξ_mem, hξ_deriv⟩ := @exists_deriv_eq_zero (evalFunc1 e) y x hlt hCont' hf_eq
      have hξ_in_I : ξ ∈ I := by
        simp only [IntervalRat.mem_def]
        exact ⟨le_trans hy.1 (le_of_lt hξ_mem.1), le_trans (le_of_lt hξ_mem.2) hx.2⟩
      have hderiv_in := derivIntervalCore_correct e hsupp I ξ hξ_in_I cfg
      rw [hξ_deriv] at hderiv_in
      simp only [IntervalRat.mem_def] at hderiv_in
      rcases hzero with hlo_pos | hhi_neg
      · have hcast : (0 : ℝ) < dI.lo := by exact_mod_cast hlo_pos
        linarith [hderiv_in.1]
      · have hcast : (dI.hi : ℝ) < 0 := by exact_mod_cast hhi_neg
        linarith [hderiv_in.2]

/-- MVT bound using Core functions: If f' ≥ dI.lo > 0 (increasing) and f(I.lo) > 0,
    then f(c) > dI.lo * hw where c = midpoint and hw = half-width. -/
lemma mvt_fc_lower_bound_pos_increasing_core
    (e : Expr) (hsupp : ExprSupported e)
    (I : IntervalRat) (cfg : EvalConfig)
    (_hI_nonsingleton : I.lo < I.hi)
    (_hdI_lo_pos : 0 < (derivIntervalCore e I cfg).lo)
    (hCont : ContinuousOn (evalFunc1 e) (Set.Icc I.lo I.hi))
    (hf_Ilo_pos : 0 < evalFunc1 e I.lo) :
    let c : ℚ := I.midpoint
    let hw : ℚ := (I.hi - I.lo) / 2
    let dI := derivIntervalCore e I cfg
    evalFunc1 e c > (dI.lo : ℝ) * hw := by
  intro c hw dI
  have hderiv_lo : ∀ ξ ∈ I, (dI.lo : ℝ) ≤ deriv (evalFunc1 e) ξ := fun ξ hξ =>
    (derivIntervalCore_correct e hsupp I ξ hξ cfg).1
  have hc_in_I : (c : ℝ) ∈ I := IntervalRat.midpoint_mem I
  have hIlo_in_I : (I.lo : ℝ) ∈ I := by
    simp only [IntervalRat.mem_def]
    exact ⟨le_refl _, by exact_mod_cast I.le⟩
  have hIlo_le_c : (I.lo : ℝ) ≤ c := by
    have hle : (I.lo : ℝ) ≤ I.hi := by exact_mod_cast I.le
    have hc_def : (c : ℝ) = ((I.lo : ℝ) + I.hi) / 2 := by
      show ((I.lo + I.hi) / 2 : ℚ) = ((I.lo : ℝ) + I.hi) / 2; push_cast; ring
    linarith
  have hmvt := mvt_lower_bound_core e hsupp I cfg hCont I.lo c hIlo_in_I hc_in_I hIlo_le_c
  have hc_minus_Ilo : (c : ℝ) - I.lo = hw := by
    have hc_def : (c : ℝ) = ((I.lo : ℝ) + I.hi) / 2 := by
      show ((I.lo + I.hi) / 2 : ℚ) = ((I.lo : ℝ) + I.hi) / 2; push_cast; ring
    have hhw_def : (hw : ℝ) = ((I.hi : ℝ) - I.lo) / 2 := by
      show (((I.hi - I.lo) / 2 : ℚ) : ℝ) = ((I.hi : ℝ) - I.lo) / 2; push_cast; ring
    linarith
  rw [hc_minus_Ilo] at hmvt
  calc evalFunc1 e c ≥ evalFunc1 e I.lo + dI.lo * hw := by linarith
    _ > 0 + dI.lo * hw := by linarith
    _ = dI.lo * hw := by ring

/-- MVT bound using Core functions: If f' ≥ dI.lo > 0 (increasing) and f(I.hi) < 0,
    then f(c) < -dI.lo * hw where c = midpoint and hw = half-width. -/
lemma mvt_fc_upper_bound_pos_increasing_core
    (e : Expr) (hsupp : ExprSupported e)
    (I : IntervalRat) (cfg : EvalConfig)
    (_hI_nonsingleton : I.lo < I.hi)
    (_hdI_lo_pos : 0 < (derivIntervalCore e I cfg).lo)
    (hCont : ContinuousOn (evalFunc1 e) (Set.Icc I.lo I.hi))
    (hf_Ihi_neg : evalFunc1 e I.hi < 0) :
    let c : ℚ := I.midpoint
    let hw : ℚ := (I.hi - I.lo) / 2
    let dI := derivIntervalCore e I cfg
    evalFunc1 e c < -((dI.lo : ℝ) * hw) := by
  intro c hw dI
  have hderiv_lo : ∀ ξ ∈ I, (dI.lo : ℝ) ≤ deriv (evalFunc1 e) ξ := fun ξ hξ =>
    (derivIntervalCore_correct e hsupp I ξ hξ cfg).1
  have hc_in_I : (c : ℝ) ∈ I := IntervalRat.midpoint_mem I
  have hIhi_in_I : (I.hi : ℝ) ∈ I := by
    simp only [IntervalRat.mem_def]
    exact ⟨by exact_mod_cast I.le, le_refl _⟩
  have hc_le_Ihi : (c : ℝ) ≤ I.hi := by
    have hle : (I.lo : ℝ) ≤ I.hi := by exact_mod_cast I.le
    have hc_def : (c : ℝ) = ((I.lo : ℝ) + I.hi) / 2 := by
      show ((I.lo + I.hi) / 2 : ℚ) = ((I.lo : ℝ) + I.hi) / 2; push_cast; ring
    linarith
  have hmvt := mvt_lower_bound_core e hsupp I cfg hCont c I.hi hc_in_I hIhi_in_I hc_le_Ihi
  have hIhi_minus_c : (I.hi : ℝ) - c = hw := by
    have hc_def : (c : ℝ) = ((I.lo : ℝ) + I.hi) / 2 := by
      show ((I.lo + I.hi) / 2 : ℚ) = ((I.lo : ℝ) + I.hi) / 2; push_cast; ring
    have hhw_def : (hw : ℝ) = ((I.hi : ℝ) - I.lo) / 2 := by
      show (((I.hi - I.lo) / 2 : ℚ) : ℝ) = ((I.hi : ℝ) - I.lo) / 2; push_cast; ring
    linarith
  rw [hIhi_minus_c] at hmvt
  calc evalFunc1 e c ≤ evalFunc1 e I.hi - dI.lo * hw := by linarith
    _ < 0 - dI.lo * hw := by linarith
    _ = -(dI.lo * hw) := by ring

/-- MVT bound using Core functions: If f' ≤ dI.hi < 0 (decreasing) and f(I.lo) < 0,
    then f(c) < 0 and more specifically, fc.lo / dI.hi ≥ hw. -/
lemma mvt_fc_upper_bound_neg_decreasing_core
    (e : Expr) (hsupp : ExprSupported e)
    (I : IntervalRat) (cfg : EvalConfig)
    (_hI_nonsingleton : I.lo < I.hi)
    (_hdI_hi_neg : (derivIntervalCore e I cfg).hi < 0)
    (hCont : ContinuousOn (evalFunc1 e) (Set.Icc I.lo I.hi))
    (hf_Ilo_neg : evalFunc1 e I.lo < 0) :
    let c : ℚ := I.midpoint
    let hw : ℚ := (I.hi - I.lo) / 2
    let dI := derivIntervalCore e I cfg
    evalFunc1 e c < (dI.hi : ℝ) * hw := by
  intro c hw dI
  have hderiv_hi : ∀ ξ ∈ I, deriv (evalFunc1 e) ξ ≤ (dI.hi : ℝ) := fun ξ hξ =>
    (derivIntervalCore_correct e hsupp I ξ hξ cfg).2
  have hc_in_I : (c : ℝ) ∈ I := IntervalRat.midpoint_mem I
  have hIlo_in_I : (I.lo : ℝ) ∈ I := by
    simp only [IntervalRat.mem_def]
    exact ⟨le_refl _, by exact_mod_cast I.le⟩
  have hIlo_le_c : (I.lo : ℝ) ≤ c := by
    have hle : (I.lo : ℝ) ≤ I.hi := by exact_mod_cast I.le
    have hc_def : (c : ℝ) = ((I.lo : ℝ) + I.hi) / 2 := by
      show ((I.lo + I.hi) / 2 : ℚ) = ((I.lo : ℝ) + I.hi) / 2; push_cast; ring
    linarith
  have hmvt := mvt_upper_bound_core e hsupp I cfg hCont I.lo c hIlo_in_I hc_in_I hIlo_le_c
  have hc_minus_Ilo : (c : ℝ) - I.lo = hw := by
    have hc_def : (c : ℝ) = ((I.lo : ℝ) + I.hi) / 2 := by
      show ((I.lo + I.hi) / 2 : ℚ) = ((I.lo : ℝ) + I.hi) / 2; push_cast; ring
    have hhw_def : (hw : ℝ) = ((I.hi : ℝ) - I.lo) / 2 := by
      show (((I.hi - I.lo) / 2 : ℚ) : ℝ) = ((I.hi : ℝ) - I.lo) / 2; push_cast; ring
    linarith
  rw [hc_minus_Ilo] at hmvt
  calc evalFunc1 e c ≤ evalFunc1 e I.lo + dI.hi * hw := by linarith
    _ < 0 + dI.hi * hw := by linarith
    _ = dI.hi * hw := by ring

/-- MVT bound using Core functions: If f' ≤ dI.hi < 0 (decreasing) and f(I.hi) > 0,
    then f(c) > 0 and more specifically, fc.hi / dI.hi ≤ -hw. -/
lemma mvt_fc_lower_bound_neg_decreasing_core
    (e : Expr) (hsupp : ExprSupported e)
    (I : IntervalRat) (cfg : EvalConfig)
    (_hI_nonsingleton : I.lo < I.hi)
    (_hdI_hi_neg : (derivIntervalCore e I cfg).hi < 0)
    (hCont : ContinuousOn (evalFunc1 e) (Set.Icc I.lo I.hi))
    (hf_Ihi_pos : 0 < evalFunc1 e I.hi) :
    let c : ℚ := I.midpoint
    let hw : ℚ := (I.hi - I.lo) / 2
    let dI := derivIntervalCore e I cfg
    evalFunc1 e c > -((dI.hi : ℝ) * hw) := by
  intro c hw dI
  have hderiv_hi : ∀ ξ ∈ I, deriv (evalFunc1 e) ξ ≤ (dI.hi : ℝ) := fun ξ hξ =>
    (derivIntervalCore_correct e hsupp I ξ hξ cfg).2
  have hc_in_I : (c : ℝ) ∈ I := IntervalRat.midpoint_mem I
  have hIhi_in_I : (I.hi : ℝ) ∈ I := by
    simp only [IntervalRat.mem_def]
    exact ⟨by exact_mod_cast I.le, le_refl _⟩
  have hc_le_Ihi : (c : ℝ) ≤ I.hi := by
    have hle : (I.lo : ℝ) ≤ I.hi := by exact_mod_cast I.le
    have hc_def : (c : ℝ) = ((I.lo : ℝ) + I.hi) / 2 := by
      show ((I.lo + I.hi) / 2 : ℚ) = ((I.lo : ℝ) + I.hi) / 2; push_cast; ring
    linarith
  have hmvt := mvt_upper_bound_core e hsupp I cfg hCont c I.hi hc_in_I hIhi_in_I hc_le_Ihi
  have hIhi_minus_c : (I.hi : ℝ) - c = hw := by
    have hc_def : (c : ℝ) = ((I.lo : ℝ) + I.hi) / 2 := by
      show ((I.lo + I.hi) / 2 : ℚ) = ((I.lo : ℝ) + I.hi) / 2; push_cast; ring
    have hhw_def : (hw : ℝ) = ((I.hi : ℝ) - I.lo) / 2 := by
      show (((I.hi - I.lo) / 2 : ℚ) : ℝ) = ((I.hi : ℝ) - I.lo) / 2; push_cast; ring
    linarith
  rw [hIhi_minus_c] at hmvt
  calc evalFunc1 e c ≥ evalFunc1 e I.hi - dI.hi * hw := by linarith
    _ > 0 - dI.hi * hw := by linarith
    _ = -(dI.hi * hw) := by ring

/-- **Golden Theorem for Computable Unique Root (Fully Computable)**

    If `checkNewtonContractsCore e I cfg = true`, then there exists a unique root in I.

    This theorem uses ONLY computable functions (no Real.exp, Real.log, etc.),
    making it suitable for `native_decide` verification. -/
theorem verify_unique_root_computable (e : Expr) (hsupp : ExprSupported e)
    (hvar0 : UsesOnlyVar0 e) (I : IntervalRat) (cfg : EvalConfig)
    (hCont : ContinuousOn (fun x => Expr.eval (fun _ => x) e) (Set.Icc I.lo I.hi))
    (h_cert : checkNewtonContractsCore e I cfg = true) :
    ∃! x, x ∈ I ∧ Expr.eval (fun _ => x) e = 0 := by
  simp only [checkNewtonContractsCore] at h_cert
  split at h_cert
  · exact absurd h_cert Bool.false_ne_true
  · rename_i N hN
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h_cert
    have hContract : N.lo > I.lo ∧ N.hi < I.hi := ⟨h_cert.1, h_cert.2⟩

    -- Extract structure
    obtain ⟨hdI_nonzero, hN_lo, hN_hi⟩ := newtonStepCore_extract e I N cfg hN
    let c := I.midpoint
    let fc := evalIntervalCore1 e (IntervalRat.singleton c) cfg
    let dI := derivIntervalCore e I cfg
    let hw : ℚ := (I.hi - I.lo) / 2

    -- From contraction bounds, extract Q bounds
    -- N.lo = max I.lo (c - Q.hi), N.hi = min I.hi (c - Q.lo)
    -- Contraction means: N.lo > I.lo and N.hi < I.hi
    -- So N.lo = c - Q.hi (not I.lo) and N.hi = c - Q.lo (not I.hi)
    have hbounds := contraction_newton_bounds hContract hN_lo hN_hi

    -- Q.hi < c - I.lo = hw and Q.lo > c - I.hi = -hw
    have hQ_hi_lt : (c : ℚ) - N.lo < hw := by
      rw [hbounds.1]
      have hc_minus_Ilo : c - I.lo = hw := by
        show I.midpoint - I.lo = (I.hi - I.lo) / 2
        simp only [IntervalRat.midpoint]; ring
      linarith [hContract.1]
    have hQ_lo_gt : (c : ℚ) - N.hi > -hw := by
      rw [hbounds.2]
      have hc_minus_Ihi : c - I.hi = -hw := by
        show I.midpoint - I.hi = -((I.hi - I.lo) / 2)
        simp only [IntervalRat.midpoint]; ring
      linarith [hContract.2]

    -- Use sign analysis to prove existence
    simp only [IntervalRat.containsZero, not_and_or, not_le] at hdI_nonzero

    -- Contraction + MVT logic mirrors newton_contraction_has_root
    -- Key: if f doesn't change sign, MVT bounds on the quotient contradict contraction
    have hI_nonsingleton : I.lo < I.hi := by
      have h1 : (I.lo : ℝ) < N.lo := by exact_mod_cast hContract.1
      have h2 : (N.hi : ℝ) < I.hi := by exact_mod_cast hContract.2
      have h3 : (N.lo : ℝ) ≤ N.hi := by exact_mod_cast N.le
      have h4 : I.lo < I.hi := by
        have : (I.lo : ℝ) < I.hi := by linarith
        exact_mod_cast this
      exact h4

    set f := fun x : ℝ => Expr.eval (fun _ => x) e with hf_def

    -- Case split on derivative sign
    rcases hdI_nonzero with hdI_pos | hdI_neg
    · -- Case: dI.lo > 0 (strictly increasing)
      by_cases hlo : f I.lo ≥ 0
      · by_cases hhi : f I.hi ≤ 0
        · -- f(lo) ≥ 0 and f(hi) ≤ 0 with f increasing is a contradiction
          -- Because f' ≥ dI.lo > 0 implies f(hi) - f(lo) > 0, so f(hi) > f(lo)
          -- Combined with f(lo) ≥ 0 ≥ f(hi), this is impossible
          exfalso
          have hIlo_in_I : (I.lo : ℝ) ∈ I := by
            simp only [IntervalRat.mem_def]
            exact ⟨le_refl _, by exact_mod_cast I.le⟩
          have hIhi_in_I : (I.hi : ℝ) ∈ I := by
            simp only [IntervalRat.mem_def]
            exact ⟨by exact_mod_cast I.le, le_refl _⟩
          have hle : (I.lo : ℝ) ≤ I.hi := by exact_mod_cast I.le
          -- MVT: f(hi) - f(lo) ≥ dI.lo * (hi - lo) > 0
          have hmvt := mvt_lower_bound_core e hsupp I cfg hCont I.lo I.hi hIlo_in_I hIhi_in_I hle
          have hdI_lo_pos_real : (0 : ℝ) < dI.lo := by exact_mod_cast hdI_pos
          have hwidth_pos : (I.hi : ℝ) - I.lo > 0 := by
            have h : (I.lo : ℝ) < I.hi := by exact_mod_cast hI_nonsingleton
            linarith
          have hdiff_pos : (dI.lo : ℝ) * ((I.hi : ℝ) - I.lo) > 0 := mul_pos hdI_lo_pos_real hwidth_pos
          -- hmvt : evalFunc1 e ↑I.hi - evalFunc1 e ↑I.lo ≥ ↑dI.lo * (↑I.hi - ↑I.lo)
          -- hdiff_pos : (dI.lo : ℝ) * ((I.hi : ℝ) - I.lo) > 0
          -- So evalFunc1 e I.hi > evalFunc1 e I.lo
          -- hlo : 0 ≤ f I.lo = evalFunc1 e I.lo
          -- hhi : f I.hi ≤ 0 = evalFunc1 e I.hi ≤ 0
          -- This gives: 0 ≤ evalFunc1 e I.lo < evalFunc1 e I.hi ≤ 0, contradiction
          have hstrictly_increasing : evalFunc1 e I.hi > evalFunc1 e I.lo := by linarith
          linarith
        · -- f(lo) ≥ 0 and f(hi) > 0 with f increasing → f > 0 on I
          push_neg at hhi
          by_cases hlo_eq : f I.lo = 0
          · use I.lo
            have hIlo_in_I : (I.lo : ℝ) ∈ I := by
              simp only [IntervalRat.mem_def]
              exact ⟨le_refl _, by exact_mod_cast I.le⟩
            constructor
            · exact ⟨hIlo_in_I, hlo_eq⟩
            · intro y ⟨hy_in_I, hy_root⟩
              exact newton_step_core_at_most_one_root e hsupp hvar0 I cfg ⟨N, hN⟩ hCont y I.lo hy_in_I hIlo_in_I hy_root hlo_eq
          · -- f(lo) > 0, get contradiction via MVT
            have hlo_pos : 0 < f I.lo := lt_of_le_of_ne hlo (Ne.symm hlo_eq)
            exfalso
            -- MVT: fc.hi / dI.lo ≥ hw (half-width)
            have hMVT := mvt_fc_lower_bound_pos_increasing_core e hsupp I cfg hI_nonsingleton hdI_pos hCont hlo_pos
            -- Apply generic contraction contradiction
            exact generic_contraction_absurd_hi I c fc dI N rfl hdI_nonzero hdI_pos
              (evalIntervalCore1_correct e hsupp.toCore c (IntervalRat.singleton c) (IntervalRat.mem_singleton c) cfg (exprSupported_domainValid1 hsupp _ cfg))
              hN_lo hContract.1 hMVT
      · push_neg at hlo
        by_cases hhi : f I.hi ≤ 0
        · by_cases hhi_eq : f I.hi = 0
          · use I.hi
            have hIhi_in_I : (I.hi : ℝ) ∈ I := by
              simp only [IntervalRat.mem_def]
              exact ⟨by exact_mod_cast I.le, le_refl _⟩
            constructor
            · exact ⟨hIhi_in_I, hhi_eq⟩
            · intro y ⟨hy_in_I, hy_root⟩
              exact newton_step_core_at_most_one_root e hsupp hvar0 I cfg ⟨N, hN⟩ hCont y I.hi hy_in_I hIhi_in_I hy_root hhi_eq
          · -- f(hi) < 0, get contradiction via MVT
            have hhi_neg : f I.hi < 0 := lt_of_le_of_ne hhi hhi_eq
            exfalso
            have hMVT := mvt_fc_upper_bound_pos_increasing_core e hsupp I cfg hI_nonsingleton hdI_pos hCont hhi_neg
            exact generic_contraction_absurd_lo I c fc dI N rfl hdI_nonzero hdI_pos
              (evalIntervalCore1_correct e hsupp.toCore c (IntervalRat.singleton c) (IntervalRat.mem_singleton c) cfg (exprSupported_domainValid1 hsupp _ cfg))
              hN_hi hContract.2 hMVT
        · -- f(lo) < 0 and f(hi) > 0: SIGN CHANGE! Apply IVT.
          push_neg at hhi
          have hle : (I.lo : ℝ) ≤ I.hi := by exact_mod_cast I.le
          have h0_in_range : (0 : ℝ) ∈ Set.Icc (f I.lo) (f I.hi) := ⟨le_of_lt hlo, le_of_lt hhi⟩
          have hivt := intermediate_value_Icc hle hCont h0_in_range
          obtain ⟨x, hx_mem, hx_root⟩ := hivt
          use x
          constructor
          · have hx_in_I : x ∈ I := by simp only [IntervalRat.mem_def]; exact hx_mem
            exact ⟨hx_in_I, hx_root⟩
          · intro y ⟨hy_in_I, hy_root⟩
            have hx_in_I : x ∈ I := by simp only [IntervalRat.mem_def]; exact hx_mem
            exact newton_step_core_at_most_one_root e hsupp hvar0 I cfg ⟨N, hN⟩ hCont y x hy_in_I hx_in_I hy_root hx_root
    · -- Case: dI.hi < 0 (strictly decreasing) - symmetric logic
      by_cases hlo : f I.lo ≤ 0
      · by_cases hhi : f I.hi ≥ 0
        · -- f(lo) ≤ 0 ≤ f(hi) with f decreasing is a contradiction
          -- Because f' ≤ dI.hi < 0 implies f(hi) - f(lo) < 0, so f(hi) < f(lo)
          -- Combined with f(lo) ≤ 0 ≤ f(hi), this is impossible
          exfalso
          have hIlo_in_I : (I.lo : ℝ) ∈ I := by
            simp only [IntervalRat.mem_def]
            exact ⟨le_refl _, by exact_mod_cast I.le⟩
          have hIhi_in_I : (I.hi : ℝ) ∈ I := by
            simp only [IntervalRat.mem_def]
            exact ⟨by exact_mod_cast I.le, le_refl _⟩
          have hle : (I.lo : ℝ) ≤ I.hi := by exact_mod_cast I.le
          -- MVT: f(hi) - f(lo) ≤ dI.hi * (hi - lo) < 0
          have hmvt := mvt_upper_bound_core e hsupp I cfg hCont I.lo I.hi hIlo_in_I hIhi_in_I hle
          have hdI_hi_neg_real : (dI.hi : ℝ) < 0 := by exact_mod_cast hdI_neg
          have hwidth_pos : (I.hi : ℝ) - I.lo > 0 := by
            have h : (I.lo : ℝ) < I.hi := by exact_mod_cast hI_nonsingleton
            linarith
          have hdiff_neg : (dI.hi : ℝ) * ((I.hi : ℝ) - I.lo) < 0 := mul_neg_of_neg_of_pos hdI_hi_neg_real hwidth_pos
          -- hmvt : evalFunc1 e ↑I.hi - evalFunc1 e ↑I.lo ≤ ↑dI.hi * (↑I.hi - ↑I.lo)
          -- hdiff_neg : (dI.hi : ℝ) * ((I.hi : ℝ) - I.lo) < 0
          -- So evalFunc1 e I.hi < evalFunc1 e I.lo
          -- hlo : f I.lo ≤ 0 = evalFunc1 e I.lo ≤ 0
          -- hhi : f I.hi ≥ 0 = evalFunc1 e I.hi ≥ 0
          -- This gives: 0 ≤ evalFunc1 e I.hi < evalFunc1 e I.lo ≤ 0, contradiction
          have hstrictly_decreasing : evalFunc1 e I.hi < evalFunc1 e I.lo := by linarith
          linarith
        · push_neg at hhi
          by_cases hlo_eq : f I.lo = 0
          · use I.lo
            have hIlo_in_I : (I.lo : ℝ) ∈ I := by
              simp only [IntervalRat.mem_def]
              exact ⟨le_refl _, by exact_mod_cast I.le⟩
            constructor
            · exact ⟨hIlo_in_I, hlo_eq⟩
            · intro y ⟨hy_in_I, hy_root⟩
              exact newton_step_core_at_most_one_root e hsupp hvar0 I cfg ⟨N, hN⟩ hCont y I.lo hy_in_I hIlo_in_I hy_root hlo_eq
          · -- f(lo) < 0 and f(hi) < 0 with f decreasing → contradiction via MVT
            have hlo_neg : f I.lo < 0 := lt_of_le_of_ne hlo hlo_eq
            exfalso
            have hMVT := mvt_fc_upper_bound_neg_decreasing_core e hsupp I cfg hI_nonsingleton hdI_neg hCont hlo_neg
            exact generic_contraction_absurd_hi_neg I c fc dI N rfl hdI_nonzero hdI_neg
              (evalIntervalCore1_correct e hsupp.toCore c (IntervalRat.singleton c) (IntervalRat.mem_singleton c) cfg (exprSupported_domainValid1 hsupp _ cfg))
              hN_lo hContract.1 hMVT
      · push_neg at hlo
        by_cases hhi : f I.hi ≥ 0
        · by_cases hhi_eq : f I.hi = 0
          · use I.hi
            have hIhi_in_I : (I.hi : ℝ) ∈ I := by
              simp only [IntervalRat.mem_def]
              exact ⟨by exact_mod_cast I.le, le_refl _⟩
            constructor
            · exact ⟨hIhi_in_I, hhi_eq⟩
            · intro y ⟨hy_in_I, hy_root⟩
              exact newton_step_core_at_most_one_root e hsupp hvar0 I cfg ⟨N, hN⟩ hCont y I.hi hy_in_I hIhi_in_I hy_root hhi_eq
          · -- f(hi) > 0 and f(lo) > 0 with f decreasing → contradiction via MVT
            have hhi_pos : 0 < f I.hi := lt_of_le_of_ne hhi (Ne.symm hhi_eq)
            exfalso
            have hMVT := mvt_fc_lower_bound_neg_decreasing_core e hsupp I cfg hI_nonsingleton hdI_neg hCont hhi_pos
            exact generic_contraction_absurd_lo_neg I c fc dI N rfl hdI_nonzero hdI_neg
              (evalIntervalCore1_correct e hsupp.toCore c (IntervalRat.singleton c) (IntervalRat.mem_singleton c) cfg (exprSupported_domainValid1 hsupp _ cfg))
              hN_hi hContract.2 hMVT
        · -- f(lo) > 0 and f(hi) < 0: SIGN CHANGE for decreasing function!
          push_neg at hhi
          have hle : (I.lo : ℝ) ≤ I.hi := by exact_mod_cast I.le
          have h0_in_range : (0 : ℝ) ∈ Set.Icc (f I.hi) (f I.lo) := ⟨le_of_lt hhi, le_of_lt hlo⟩
          have hivt := intermediate_value_Icc' hle hCont h0_in_range
          obtain ⟨x, hx_mem, hx_root⟩ := hivt
          use x
          constructor
          · have hx_in_I : x ∈ I := by simp only [IntervalRat.mem_def]; exact hx_mem
            exact ⟨hx_in_I, hx_root⟩
          · intro y ⟨hy_in_I, hy_root⟩
            have hx_in_I : x ∈ I := by simp only [IntervalRat.mem_def]; exact hx_mem
            exact newton_step_core_at_most_one_root e hsupp hvar0 I cfg ⟨N, hN⟩ hCont y x hy_in_I hx_in_I hy_root hx_root

/-! ### Sign Change Root Existence -/

/-- **Golden Theorem for Sign Change Root Existence**

    If `checkSignChange e I cfg = true`, then there exists a root in I.

    This uses the Intermediate Value Theorem: if f(lo) and f(hi) have opposite signs,
    and f is continuous on I, then f has a root in I. -/
theorem verify_sign_change (e : Expr) (hsupp : ExprSupportedCore e)
    (I : IntervalRat) (cfg : EvalConfig)
    (hCont : ContinuousOn (fun x => Expr.eval (fun _ => x) e) (Set.Icc I.lo I.hi))
    (h_cert : checkSignChange e I cfg = true) :
    ∃ x ∈ I, Expr.eval (fun _ => x) e = 0 := by
  simp only [checkSignChange, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h_cert
  -- Extract domain validity from certificate
  have hdom_lo := checkDomainValid1_correct e (IntervalRat.singleton I.lo) cfg h_cert.1.1
  have hdom_hi := checkDomainValid1_correct e (IntervalRat.singleton I.hi) cfg h_cert.1.2
  -- Define f for convenience
  set f := fun x : ℝ => Expr.eval (fun _ => x) e with hf
  -- Get singleton memberships
  have hlo_sing : (I.lo : ℝ) ∈ IntervalRat.singleton I.lo := IntervalRat.mem_singleton I.lo
  have hhi_sing : (I.hi : ℝ) ∈ IntervalRat.singleton I.hi := IntervalRat.mem_singleton I.hi
  -- Apply evalIntervalCore1_correct to get bounds on f(lo) and f(hi)
  have hflo := evalIntervalCore1_correct e hsupp I.lo (IntervalRat.singleton I.lo) hlo_sing cfg hdom_lo
  have hfhi := evalIntervalCore1_correct e hsupp I.hi (IntervalRat.singleton I.hi) hhi_sing cfg hdom_hi
  simp only [IntervalRat.mem_def] at hflo hfhi
  -- Get the interval bound
  have hle : (I.lo : ℝ) ≤ I.hi := by exact_mod_cast I.le
  -- Extract sign change condition
  have h_sign := h_cert.2
  -- Handle the two cases of signChange
  cases h_sign with
  | inl hcase =>
    -- Case: f(lo).hi < 0 ∧ 0 < f(hi).lo, meaning f(lo) < 0 < f(hi)
    have hflo_neg : f I.lo < 0 := by
      have hbound : f I.lo ≤ (evalIntervalCore1 e (IntervalRat.singleton I.lo) cfg).hi := hflo.2
      have hcast : ((evalIntervalCore1 e (IntervalRat.singleton I.lo) cfg).hi : ℝ) < 0 := by
        exact_mod_cast hcase.1
      linarith
    have hfhi_pos : 0 < f I.hi := by
      have hbound : (evalIntervalCore1 e (IntervalRat.singleton I.hi) cfg).lo ≤ f I.hi := hfhi.1
      have hcast : (0 : ℝ) < (evalIntervalCore1 e (IntervalRat.singleton I.hi) cfg).lo := by
        exact_mod_cast hcase.2
      linarith
    -- Apply IVT: since f(lo) < 0 < f(hi), 0 ∈ Icc (f lo) (f hi) ⊆ f '' Icc lo hi
    have h0_in_range : (0 : ℝ) ∈ Set.Icc (f I.lo) (f I.hi) := ⟨le_of_lt hflo_neg, le_of_lt hfhi_pos⟩
    have hivt := intermediate_value_Icc (α := ℝ) (δ := ℝ) hle hCont
    have h0_in_image := hivt h0_in_range
    obtain ⟨c, hc_mem, hc_eq⟩ := h0_in_image
    refine ⟨c, ?_, hc_eq⟩
    simp only [IntervalRat.mem_def]
    exact hc_mem
  | inr hcase =>
    -- Case: f(hi).hi < 0 ∧ 0 < f(lo).lo, meaning f(hi) < 0 < f(lo)
    have hfhi_neg : f I.hi < 0 := by
      have hbound : f I.hi ≤ (evalIntervalCore1 e (IntervalRat.singleton I.hi) cfg).hi := hfhi.2
      have hcast : ((evalIntervalCore1 e (IntervalRat.singleton I.hi) cfg).hi : ℝ) < 0 := by
        exact_mod_cast hcase.1
      linarith
    have hflo_pos : 0 < f I.lo := by
      have hbound : (evalIntervalCore1 e (IntervalRat.singleton I.lo) cfg).lo ≤ f I.lo := hflo.1
      have hcast : (0 : ℝ) < (evalIntervalCore1 e (IntervalRat.singleton I.lo) cfg).lo := by
        exact_mod_cast hcase.2
      linarith
    -- f '' [lo, hi] is an interval containing both f(lo) and f(hi)
    have hflo_in_image : f I.lo ∈ f '' Set.Icc (↑I.lo) (↑I.hi) :=
      Set.mem_image_of_mem f (Set.left_mem_Icc.mpr hle)
    have hfhi_in_image : f I.hi ∈ f '' Set.Icc (↑I.lo) (↑I.hi) :=
      Set.mem_image_of_mem f (Set.right_mem_Icc.mpr hle)
    -- The image is connected (as continuous image of connected set)
    have hconn : IsConnected (f '' Set.Icc (↑I.lo) (↑I.hi)) :=
      (isConnected_Icc hle).image f hCont
    -- Use IsConnected.Icc_subset: the image contains [f(hi), f(lo)] since it's connected
    have hsub := hconn.Icc_subset hfhi_in_image hflo_in_image
    have h0_mem : (0 : ℝ) ∈ Set.Icc (f I.hi) (f I.lo) := ⟨le_of_lt hfhi_neg, le_of_lt hflo_pos⟩
    have h0_in_img := hsub h0_mem
    obtain ⟨c, hc_mem, hc_eq⟩ := h0_in_img
    refine ⟨c, ?_, hc_eq⟩
    simp only [IntervalRat.mem_def]
    exact hc_mem

/-! ### Bisection-Based Root Existence -/

/-- Check if bisection finds a root (returns hasRoot for some sub-interval).
    This runs the bisection algorithm and checks if any interval has hasRoot status.

    Note: This is noncomputable because bisectRoot uses evalInterval1. -/
noncomputable def checkHasRoot (e : Expr) (I : IntervalRat) (cfg : RootConfig) : Bool :=
  let tol : ℚ := (1 : ℚ) / (2 ^ cfg.maxDepth)
  let htol : 0 < tol := by positivity
  let result := bisectRoot e I cfg.maxDepth tol htol
  result.intervals.any fun (_, s) => s == RootStatus.hasRoot

/-- **Golden Theorem for Bisection Root Existence**

    If `checkHasRoot e I cfg = true`, then there exists a root in I.

    This uses bisectRoot_hasRoot_correct which proves that if bisection returns
    hasRoot for a sub-interval J ⊆ I, then there exists a root in J (hence in I). -/
theorem verify_has_root (e : Expr) (hsupp : ExprSupported e)
    (I : IntervalRat) (cfg : RootConfig)
    (hCont : ContinuousOn (fun x => Expr.eval (fun _ => x) e) (Set.Icc I.lo I.hi))
    (h_cert : checkHasRoot e I cfg = true) :
    ∃ x ∈ I, Expr.eval (fun _ => x) e = 0 := by
  simp only [checkHasRoot] at h_cert
  -- Extract the interval with hasRoot status
  have htol : (0 : ℚ) < 1 / 2 ^ cfg.maxDepth := by positivity
  set result := bisectRoot e I cfg.maxDepth (1 / 2 ^ cfg.maxDepth) htol with hresult
  -- h_cert says some interval has hasRoot status
  simp only [List.any_eq_true, beq_iff_eq] at h_cert
  obtain ⟨⟨J, s⟩, hmem, hs⟩ := h_cert
  -- Apply bisectRoot_hasRoot_correct
  have hroot := bisectRoot_hasRoot_correct e hsupp I cfg.maxDepth (1 / 2 ^ cfg.maxDepth) htol hCont
  have hroot_J := hroot J s hmem hs
  -- hroot_J : ∃ x ∈ J, f(x) = 0
  -- We need to show x ∈ I
  obtain ⟨x, hxJ, hx_root⟩ := hroot_J
  -- Show J ⊆ I using go_subinterval (implicitly used in bisectRoot_hasRoot_correct)
  -- Actually, bisectRoot_hasRoot_correct proves x ∈ J, and we need x ∈ I
  -- The proof in bisectRoot_hasRoot_correct shows J is a sub-interval of I
  -- and applies signChange_correct with continuity on J
  -- So x ∈ J ⊆ I
  refine ⟨x, ?_, hx_root⟩
  -- Need to show x ∈ I given x ∈ J and J is a sub-interval of I
  -- From go_subinterval in the bisectRoot_hasRoot_correct proof
  have hJsub : I.lo ≤ J.lo ∧ J.hi ≤ I.hi := by
    -- This follows from go_subinterval applied in the bisectRoot_hasRoot_correct proof
    -- We need to extract this lemma
    have hSub := go_subinterval e (1 / 2 ^ cfg.maxDepth) cfg.maxDepth I
      [(I, RootStatus.unknown)] cfg.maxDepth []
      (subinterval_inv_initial I)
      (fun _ _ h => by simp only [List.mem_nil_iff] at h)
    exact hSub J s hmem
  simp only [IntervalRat.mem_def] at hxJ ⊢
  constructor
  · calc (I.lo : ℝ) ≤ J.lo := by exact_mod_cast hJsub.1
      _ ≤ x := hxJ.1
  · calc x ≤ J.hi := hxJ.2
      _ ≤ I.hi := by exact_mod_cast hJsub.2

end LeanCert.Validity.RootFinding

/-! ## Integration Certificates -/

namespace LeanCert.Validity.Integration

open LeanCert.Core
open LeanCert.Engine
open MeasureTheory

/-! ### Computable Integration Infrastructure

For `interval_integrate` tactic, we need:
1. A computable integration function using `evalIntervalCore1`
2. A theorem that `ExprSupportedCore` implies `IntervalIntegrable`
3. A verification theorem linking the computation to the real integral
-/

/-- Computable uniform partition using evalIntervalCore1 -/
def uniformPartitionCore (I : IntervalRat) (n : ℕ) (hn : 0 < n) : List IntervalRat :=
  let width := (I.hi - I.lo) / n
  List.ofFn fun i : Fin n =>
    { lo := I.lo + width * i
      hi := I.lo + width * (i + 1)
      le := by
        simp only [add_le_add_iff_left]
        apply mul_le_mul_of_nonneg_left
        · have : (i : ℚ) ≤ (i : ℚ) + 1 := le_add_of_nonneg_right (by norm_num)
          exact this
        · apply div_nonneg
          · linarith [I.le]
          · have : (0 : ℚ) < n := by exact_mod_cast hn
            linarith }

/-- Sum of interval bounds over a partition using computable evalIntervalCore1 -/
def sumIntervalBoundsCore (e : Expr) (parts : List IntervalRat) (cfg : EvalConfig) : IntervalRat :=
  parts.foldl
    (fun acc I =>
      let fBound := evalIntervalCore1 e I cfg
      let contribution := IntervalRat.mul
        (IntervalRat.singleton I.width)
        fBound
      IntervalRat.add acc contribution)
    (IntervalRat.singleton 0)

/-- Computable interval bounds on ∫_a^b f(x) dx using uniform partitioning -/
def integrateIntervalCore (e : Expr) (I : IntervalRat) (n : ℕ) (hn : 0 < n)
    (cfg : EvalConfig := default) : IntervalRat :=
  sumIntervalBoundsCore e (uniformPartitionCore I n hn) cfg

/-- For single-interval integration (n=1), computable version -/
def integrateInterval1Core (e : Expr) (I : IntervalRat) (cfg : EvalConfig := default) : IntervalRat :=
  let fBound := evalIntervalCore1 e I cfg
  IntervalRat.mul (IntervalRat.singleton I.width) fBound

/-! ### IntervalIntegrable from ExprSupportedCore

All `ExprSupportedCore` expressions are continuous, hence integrable on compact intervals. -/

/-- All ExprSupportedCore expressions are interval integrable on any compact interval.

This follows because ExprSupportedCore expressions are continuous (see exprSupportedCore_continuousOn),
and continuous functions on compact intervals are integrable.

Note: Requires domain validity for expressions with log. -/
theorem exprSupportedCore_intervalIntegrable (e : Expr) (hsupp : ExprSupportedCore e)
    (I : IntervalRat)
    (hdom : LeanCert.Meta.exprContinuousDomainValid e (Set.Icc I.lo I.hi)) :
    IntervalIntegrable (fun x => Expr.eval (fun _ => x) e) volume I.lo I.hi := by
  have hCont := LeanCert.Meta.exprSupportedCore_continuousOn e hsupp hdom
  -- Continuous functions on compact intervals are integrable
  have hle : (I.lo : ℝ) ≤ I.hi := by exact_mod_cast I.le
  exact hCont.intervalIntegrable_of_Icc hle

/-! ### Correctness of Computable Integration -/

/-- Single-interval integration correctness for ExprSupportedCore.

This is proved directly using the same structure as integrateInterval1_correct but
with the computable evalIntervalCore1 instead of noncomputable evalInterval1.

The `hdom` hypothesis ensures evaluation domain validity (e.g., log arguments have positive interval bounds).
The `hcontdom` hypothesis ensures continuity domain validity (e.g., log arguments are positive on the set). -/
theorem integrateInterval1Core_correct (e : Expr) (hsupp : ExprSupportedCore e)
    (I : IntervalRat) (cfg : EvalConfig) (hdom : evalDomainValid1 e I cfg)
    (hcontdom : LeanCert.Meta.exprContinuousDomainValid e (Set.Icc I.lo I.hi)) :
    ∫ x in (I.lo : ℝ)..(I.hi : ℝ), Expr.eval (fun _ => x) e ∈ integrateInterval1Core e I cfg := by
  unfold integrateInterval1Core
  -- Get bounds from interval evaluation
  set fBound := evalIntervalCore1 e I cfg with hfBound_def
  have hbounds : ∀ x : ℝ, x ∈ I → Expr.eval (fun _ => x) e ∈ fBound := fun x hx =>
    evalIntervalCore1_correct e hsupp x I hx cfg hdom
  have hlo : ∀ x ∈ Set.Icc (I.lo : ℝ) (I.hi : ℝ), (fBound.lo : ℝ) ≤ Expr.eval (fun _ => x) e := by
    intro x hx; exact (hbounds x hx).1
  have hhi : ∀ x ∈ Set.Icc (I.lo : ℝ) (I.hi : ℝ), Expr.eval (fun _ => x) e ≤ (fBound.hi : ℝ) := by
    intro x hx; exact (hbounds x hx).2
  have hIle : (I.lo : ℝ) ≤ I.hi := by exact_mod_cast I.le
  have hInt := exprSupportedCore_intervalIntegrable e hsupp I hcontdom
  have ⟨h_lower, h_upper⟩ := LeanCert.Engine.integral_bounds_of_bounds hIle hInt hlo hhi
  -- Show membership in the product interval
  have hwidth : (I.width : ℝ) = (I.hi : ℝ) - (I.lo : ℝ) := by
    simp only [IntervalRat.width, Rat.cast_sub]
  have hwidth_nn : (0 : ℝ) ≤ I.width := by exact_mod_cast IntervalRat.width_nonneg I
  have hfBound_le : (fBound.lo : ℝ) ≤ fBound.hi := by exact_mod_cast fBound.le
  -- Convert integral bounds to width-first form
  have h_lo' : (I.width : ℝ) * fBound.lo ≤ ∫ x in (↑I.lo)..(↑I.hi), Expr.eval (fun _ => x) e := by
    calc (I.width : ℝ) * fBound.lo = fBound.lo * I.width := by ring
       _ = fBound.lo * ((I.hi : ℝ) - I.lo) := by rw [hwidth]
       _ ≤ ∫ x in (↑I.lo)..(↑I.hi), Expr.eval (fun _ => x) e := h_lower
  have h_hi' : ∫ x in (↑I.lo)..(↑I.hi), Expr.eval (fun _ => x) e ≤ (I.width : ℝ) * fBound.hi := by
    calc ∫ x in (↑I.lo)..(↑I.hi), Expr.eval (fun _ => x) e
       ≤ fBound.hi * ((I.hi : ℝ) - I.lo) := h_upper
     _ = fBound.hi * I.width := by rw [hwidth]
     _ = (I.width : ℝ) * fBound.hi := by ring
  -- Show membership
  have h1 : (I.width : ℝ) * fBound.lo ≤ I.width * fBound.hi :=
    mul_le_mul_of_nonneg_left hfBound_le hwidth_nn
  rw [IntervalRat.mem_def]
  constructor
  · -- Lower bound
    have hcorner : (IntervalRat.mul (IntervalRat.singleton I.width) fBound).lo =
        min (min (I.width * fBound.lo) (I.width * fBound.hi))
            (min (I.width * fBound.lo) (I.width * fBound.hi)) := rfl
    simp only [hcorner, min_self, Rat.cast_min, Rat.cast_mul]
    calc (↑I.width * ↑fBound.lo) ⊓ (↑I.width * ↑fBound.hi)
        = ↑I.width * ↑fBound.lo := min_eq_left h1
      _ ≤ ∫ x in (↑I.lo)..(↑I.hi), Expr.eval (fun _ => x) e := h_lo'
  · -- Upper bound
    have hcorner : (IntervalRat.mul (IntervalRat.singleton I.width) fBound).hi =
        max (max (I.width * fBound.lo) (I.width * fBound.hi))
            (max (I.width * fBound.lo) (I.width * fBound.hi)) := rfl
    simp only [hcorner, max_self, Rat.cast_max, Rat.cast_mul]
    calc ∫ x in (↑I.lo)..(↑I.hi), Expr.eval (fun _ => x) e
        ≤ ↑I.width * ↑fBound.hi := h_hi'
      _ = (↑I.width * ↑fBound.lo) ⊔ (↑I.width * ↑fBound.hi) := (max_eq_right h1).symm

/-- Check if the integral bound contains a given rational value.
    Returns true if domain is valid and the computed integral bound contains the target value. -/
def checkIntegralBoundsCore (e : Expr) (I : IntervalRat) (target : ℚ)
    (cfg : EvalConfig := default) : Bool :=
  checkDomainValid1 e I cfg &&
  let bound := integrateInterval1Core e I cfg
  decide (bound.lo ≤ target && target ≤ bound.hi)

/-- **Golden Theorem for Integration Bounds**

If `checkIntegralBoundsCore e I target cfg = true`, then the integral is bounded by the
computed interval.

Note: The `target` parameter and `h_cert` hypothesis are used for the `native_decide` workflow
where we verify at compile time that target is in the computed interval. The actual proof
of interval membership uses `integrateInterval1Core_correct` directly.

This theorem allows proving statements like "∫_a^b f(x) dx ∈ [lo, hi]".

Note: Requires continuity domain validity for expressions with log. -/
theorem verify_integral_bound (e : Expr) (hsupp : ExprSupportedCore e)
    (I : IntervalRat) (_target : ℚ) (cfg : EvalConfig)
    (h_cert : checkIntegralBoundsCore e I _target cfg = true)
    (hcontdom : LeanCert.Meta.exprContinuousDomainValid e (Set.Icc I.lo I.hi)) :
    ∫ x in (I.lo : ℝ)..(I.hi : ℝ), Expr.eval (fun _ => x) e ∈ integrateInterval1Core e I cfg := by
  simp only [checkIntegralBoundsCore, Bool.and_eq_true] at h_cert
  have hdom := checkDomainValid1_correct e I cfg h_cert.1
  exact integrateInterval1Core_correct e hsupp I cfg hdom hcontdom

/-- Extract the computed integral bound as an interval -/
def getIntegralBound (e : Expr) (I : IntervalRat) (cfg : EvalConfig := default) : IntervalRat :=
  integrateInterval1Core e I cfg

/-- The integral lies within the computed bound (computable version)

Note: Requires continuity domain validity for expressions with log. -/
theorem integral_in_bound (e : Expr) (hsupp : ExprSupportedCore e)
    (I : IntervalRat) (cfg : EvalConfig) (hdom : evalDomainValid1 e I cfg)
    (hcontdom : LeanCert.Meta.exprContinuousDomainValid e (Set.Icc I.lo I.hi)) :
    (getIntegralBound e I cfg).lo ≤ ∫ x in (I.lo : ℝ)..(I.hi : ℝ), Expr.eval (fun _ => x) e ∧
    ∫ x in (I.lo : ℝ)..(I.hi : ℝ), Expr.eval (fun _ => x) e ≤ (getIntegralBound e I cfg).hi := by
  have hmem := integrateInterval1Core_correct e hsupp I cfg hdom hcontdom
  simp only [IntervalRat.mem_def, getIntegralBound] at hmem ⊢
  exact hmem

/-! ### Single-interval integration for ExprSupportedWithInv -/

/-- Computable single-interval integration using evalInterval?1.
    Returns `none` if interval evaluation fails (e.g., log domain invalid). -/
def integrateInterval1WithInv (e : Expr) (I : IntervalRat) : Option IntervalRat :=
  match evalInterval?1 e I with
  | some J => some (IntervalRat.mul (IntervalRat.singleton I.width) J)
  | none => none

/-- Single-interval integration correctness for ExprSupportedWithInv.
    Requires that evalInterval?1 succeeds on the interval. -/
theorem integrateInterval1WithInv_correct (e : Expr) (hsupp : ExprSupportedWithInv e)
    (I : IntervalRat) (bound : IntervalRat)
    (hsome : integrateInterval1WithInv e I = some bound)
    (hInt : IntervalIntegrable (fun x => Expr.eval (fun _ => x) e) volume I.lo I.hi) :
    ∫ x in (I.lo : ℝ)..(I.hi : ℝ), Expr.eval (fun _ => x) e ∈ bound := by
  unfold integrateInterval1WithInv at hsome
  cases h_eval : evalInterval?1 e I with
  | none =>
    simp only [h_eval] at hsome
    cases hsome
  | some J =>
    simp only [h_eval] at hsome
    cases hsome
    -- Bounds from evalInterval?1
    have hbounds : ∀ x : ℝ, x ∈ I → Expr.eval (fun _ => x) e ∈ J := fun x hx =>
      evalInterval?1_correct e hsupp I J h_eval x hx
    have hlo : ∀ x ∈ Set.Icc (I.lo : ℝ) (I.hi : ℝ),
        (J.lo : ℝ) ≤ Expr.eval (fun _ => x) e := by
      intro x hx; exact (hbounds x hx).1
    have hhi : ∀ x ∈ Set.Icc (I.lo : ℝ) (I.hi : ℝ),
        Expr.eval (fun _ => x) e ≤ (J.hi : ℝ) := by
      intro x hx; exact (hbounds x hx).2
    have hIle : (I.lo : ℝ) ≤ I.hi := by exact_mod_cast I.le
    have ⟨h_lower, h_upper⟩ := LeanCert.Engine.integral_bounds_of_bounds hIle hInt hlo hhi
    have hwidth : (I.width : ℝ) = (I.hi : ℝ) - (I.lo : ℝ) := by
      simp only [IntervalRat.width, Rat.cast_sub]
    have hwidth_nn : (0 : ℝ) ≤ I.width := by exact_mod_cast IntervalRat.width_nonneg I
    have hJ_le : (J.lo : ℝ) ≤ J.hi := by exact_mod_cast J.le
    have h_lo' : (I.width : ℝ) * J.lo ≤
        ∫ x in (↑I.lo)..(↑I.hi), Expr.eval (fun _ => x) e := by
      calc (I.width : ℝ) * J.lo = J.lo * I.width := by ring
         _ = J.lo * ((I.hi : ℝ) - I.lo) := by rw [hwidth]
         _ ≤ ∫ x in (↑I.lo)..(↑I.hi), Expr.eval (fun _ => x) e := h_lower
    have h_hi' : ∫ x in (↑I.lo)..(↑I.hi), Expr.eval (fun _ => x) e ≤
        (I.width : ℝ) * J.hi := by
      calc ∫ x in (↑I.lo)..(↑I.hi), Expr.eval (fun _ => x) e
         ≤ J.hi * ((I.hi : ℝ) - I.lo) := h_upper
       _ = J.hi * I.width := by rw [hwidth]
       _ = (I.width : ℝ) * J.hi := by ring
    have h1 : (I.width : ℝ) * J.lo ≤ I.width * J.hi :=
      mul_le_mul_of_nonneg_left hJ_le hwidth_nn
    rw [IntervalRat.mem_def]
    constructor
    · have hcorner : (IntervalRat.mul (IntervalRat.singleton I.width) J).lo =
          min (min (I.width * J.lo) (I.width * J.hi))
              (min (I.width * J.lo) (I.width * J.hi)) := rfl
      simp only [hcorner, min_self, Rat.cast_min, Rat.cast_mul]
      calc (↑I.width * ↑J.lo) ⊓ (↑I.width * ↑J.hi)
          = ↑I.width * ↑J.lo := min_eq_left h1
        _ ≤ ∫ x in (↑I.lo)..(↑I.hi), Expr.eval (fun _ => x) e := h_lo'
    · have hcorner : (IntervalRat.mul (IntervalRat.singleton I.width) J).hi =
          max (max (I.width * J.lo) (I.width * J.hi))
              (max (I.width * J.lo) (I.width * J.hi)) := rfl
      simp only [hcorner, max_self, Rat.cast_max, Rat.cast_mul]
      calc ∫ x in (↑I.lo)..(↑I.hi), Expr.eval (fun _ => x) e
          ≤ ↑I.width * ↑J.hi := h_hi'
        _ = (↑I.width * ↑J.lo) ⊔ (↑I.width * ↑J.hi) := (max_eq_right h1).symm

/-- Check if the computed integration bound contains a target value.
    Returns false if interval evaluation fails. -/
def checkIntegralBoundsWithInv (e : Expr) (I : IntervalRat) (target : ℚ) : Bool :=
  match evalInterval?1 e I with
  | some J =>
      let bound := IntervalRat.mul (IntervalRat.singleton I.width) J
      decide (bound.lo ≤ target && target ≤ bound.hi)
  | none => false

/-- **Golden Theorem for Integration Bounds (WithInv)**

If `checkIntegralBoundsWithInv e I target = true`, then the integral lies in the
computed bound. The `target` parameter is for the `native_decide` workflow. -/
theorem verify_integral_bound_withInv (e : Expr) (hsupp : ExprSupportedWithInv e)
    (I : IntervalRat) (_target : ℚ)
    (h_cert : checkIntegralBoundsWithInv e I _target = true)
    (hInt : IntervalIntegrable (fun x => Expr.eval (fun _ => x) e) volume I.lo I.hi) :
    ∃ bound, integrateInterval1WithInv e I = some bound ∧
      ∫ x in (I.lo : ℝ)..(I.hi : ℝ), Expr.eval (fun _ => x) e ∈ bound := by
  simp only [checkIntegralBoundsWithInv] at h_cert
  cases h_eval : evalInterval?1 e I with
  | none =>
    simp only [h_eval] at h_cert
    cases h_cert
  | some J =>
    have hbound : integrateInterval1WithInv e I =
        some (IntervalRat.mul (IntervalRat.singleton I.width) J) := by
      simp only [integrateInterval1WithInv, h_eval]
    refine ⟨IntervalRat.mul (IntervalRat.singleton I.width) J, hbound, ?_⟩
    exact integrateInterval1WithInv_correct e hsupp I
      (IntervalRat.mul (IntervalRat.singleton I.width) J) hbound hInt

/-! ### Partitioned integration for ExprSupportedWithInv -/

/-- Collect per-subinterval bounds using evalInterval?1.
    Returns `none` if any subinterval fails. -/
def collectBoundsWithInv (e : Expr) (parts : List IntervalRat) : Option (List IntervalRat) :=
  match parts with
  | [] => some []
  | I :: Is =>
      match integrateInterval1WithInv e I, collectBoundsWithInv e Is with
      | some J, some Js => some (J :: Js)
      | _, _ => none

/-- Sum bounds over a uniform partition using evalInterval?1. -/
def integratePartitionWithInv (e : Expr) (I : IntervalRat) (n : ℕ) : Option IntervalRat :=
  if hn : 0 < n then
    match collectBoundsWithInv e (uniformPartition I n hn) with
    | some bounds => some (bounds.foldl IntervalRat.add (IntervalRat.singleton 0))
    | none => none
  else
    none

theorem collectBoundsWithInv_length (e : Expr) :
    ∀ parts bounds,
      collectBoundsWithInv e parts = some bounds →
      bounds.length = parts.length := by
  intro parts
  induction parts with
  | nil =>
    intro bounds h
    simp [collectBoundsWithInv] at h
    cases h
    rfl
  | cons I Is ih =>
    intro bounds h
    simp [collectBoundsWithInv] at h
    cases hI : integrateInterval1WithInv e I <;>
      cases hIs : collectBoundsWithInv e Is <;>
      simp [hI, hIs] at h
    cases h
    have hlen := ih _ hIs
    simp [hlen]

theorem collectBoundsWithInv_getElem (e : Expr) :
    ∀ parts bounds (h : collectBoundsWithInv e parts = some bounds),
      ∀ i (hi : i < parts.length),
        integrateInterval1WithInv e (parts[i]'(by simpa using hi)) =
          some (bounds[i]'(by
          have hlen := collectBoundsWithInv_length e parts bounds h
          exact hlen ▸ hi)) := by
  intro parts
  induction parts with
  | nil =>
    intro bounds h i hi
    simp [collectBoundsWithInv] at h
    cases h
    simp at hi
  | cons I Is ih =>
    intro bounds h i hi
    simp [collectBoundsWithInv] at h
    cases hI : integrateInterval1WithInv e I <;>
      cases hIs : collectBoundsWithInv e Is <;>
      simp [hI, hIs] at h
    cases h
    cases i with
    | zero =>
      simp [List.getElem_cons, hI]
    | succ i =>
      have hi' : i < Is.length := by
        simpa [List.length] using hi
      have hrec := ih _ hIs i hi'
      simp [hrec]

theorem integral_subinterval_bounded_withInv (e : Expr) (hsupp : ExprSupportedWithInv e)
    (I : IntervalRat) (n : ℕ) (hn : 0 < n) (k : ℕ) (hk : k < n)
    (bound : IntervalRat)
    (hsome : integrateInterval1WithInv e (partitionInterval I n hn k hk) = some bound)
    (hInt : IntervalIntegrable (fun x => Expr.eval (fun _ => x) e) volume I.lo I.hi) :
    ∫ x in (partitionPoints I n k)..(partitionPoints I n (k + 1)),
      Expr.eval (fun _ => x) e ∈ bound := by
  rw [partitionPoints_eq_lo I n hn k hk, partitionPoints_eq_hi I n hn k hk]
  exact integrateInterval1WithInv_correct e hsupp _ bound hsome
    (intervalIntegrable_on_partition e I n hn hInt k hk)

theorem integratePartitionWithInv_correct (e : Expr) (hsupp : ExprSupportedWithInv e)
    (I : IntervalRat) (n : ℕ) (hn : 0 < n) (bound : IntervalRat)
    (hsome : integratePartitionWithInv e I n = some bound)
    (hInt : IntervalIntegrable (fun x => Expr.eval (fun _ => x) e) volume I.lo I.hi) :
    ∫ x in (I.lo : ℝ)..(I.hi : ℝ), Expr.eval (fun _ => x) e ∈ bound := by
  -- Decompose integral into sum over subintervals
  rw [integral_partition_sum e I n hn hInt]
  -- Unpack the computed bounds list
  unfold integratePartitionWithInv at hsome
  simp only [hn, ↓reduceDIte] at hsome
  cases hbounds : collectBoundsWithInv e (uniformPartition I n hn) with
  | none =>
    simp [hbounds] at hsome
  | some bounds =>
    have hbound_eq : bounds.foldl IntervalRat.add (IntervalRat.singleton 0) = bound := by
      simpa [hbounds] using hsome
    -- Express the Finset sum as a List sum
    have hsum_eq : ∑ k ∈ Finset.range n,
        ∫ x in (partitionPoints I n k)..(partitionPoints I n (k + 1)),
          Expr.eval (fun _ => x) e =
        (List.ofFn (fun k : Fin n =>
          ∫ x in (partitionPoints I n k)..(partitionPoints I n (k + 1)),
            Expr.eval (fun _ => x) e)).sum := by
      simp only [Finset.sum_range, List.sum_ofFn]
    rw [hsum_eq, ← hbound_eq]
    -- Set integrals list and bounds list
    set integrals := List.ofFn (fun k : Fin n =>
      ∫ x in (partitionPoints I n k)..(partitionPoints I n (k + 1)),
        Expr.eval (fun _ => x) e) with hintegrals_def
    -- Show lengths match
    have hlen : integrals.length = bounds.length := by
      have hlen_bounds := collectBoundsWithInv_length e _ _ hbounds
      simp [hintegrals_def, uniformPartition] at hlen_bounds ⊢
      exact hlen_bounds.symm
    -- Each integral is bounded by the corresponding bound
    have hmem : ∀ i (hi : i < integrals.length),
        integrals[i] ∈ bounds[i]'(hlen ▸ hi) := by
      intro i hi
      have hi' : i < n := by
        simpa [hintegrals_def, List.length_ofFn] using hi
      simp only [hintegrals_def]
      rw [List.getElem_ofFn]
      have hparts :
          integrateInterval1WithInv e ((uniformPartition I n hn)[i]'(by
            simp [uniformPartition]; exact hi')) = some (bounds[i]'(hlen ▸ hi)) := by
        exact collectBoundsWithInv_getElem e _ _ hbounds i (by
          simpa [uniformPartition] using hi')
      have hpart_eq :
          (uniformPartition I n hn)[i]'(by simp [uniformPartition]; exact hi') =
            partitionInterval I n hn i hi' := by
        simp [partitionInterval, uniformPartition]
      rw [hpart_eq] at hparts
      exact integral_subinterval_bounded_withInv e hsupp I n hn i hi' _ hparts hInt
    -- Apply sum_mem_foldl_add
    exact sum_mem_foldl_add hlen hmem

/-! ### Adaptive Integration for ExprSupportedWithInv

Adaptive integration concentrates partitions where the error is high (near singularities),
dramatically reducing the number of function evaluations compared to uniform partitioning.

The algorithm:
1. Compute a refined bound (n=2) on the current interval
2. If error (width of bound) is below tolerance, return
3. Otherwise, split at midpoint and recurse with half tolerance
4. Sum the bounds from sub-intervals

This naturally concentrates partitions near singularities where the function varies rapidly.
-/

/-- Result of adaptive integration with inverse support -/
structure AdaptiveResultWithInv where
  /-- Interval containing the integral -/
  bound : IntervalRat
  /-- Number of subintervals used -/
  partitions : ℕ
  deriving Repr

/-- Error estimate for adaptive integration: width of the refined bound -/
def adaptiveErrorEstimate (bound : IntervalRat) : ℚ := bound.width

/-- Compute a refined bound (n=2) on a single interval using WithInv support.
    Returns `none` if evaluation fails (domain issues). -/
def integrateRefinedWithInv (e : Expr) (I : IntervalRat) : Option IntervalRat :=
  integratePartitionWithInv e I 2

/-- Recursive adaptive integration with inverse support.
    At each level, computes refined bound and either:
    - Returns if error ≤ tol or maxDepth = 0
    - Subdivides and recurses -/
def integrateAdaptiveAuxWithInv (e : Expr) (I : IntervalRat) (tol : ℚ)
    (maxDepth : ℕ) : Option AdaptiveResultWithInv :=
  match maxDepth with
  | 0 =>
    -- Base case: return the best bound we can compute
    match integrateRefinedWithInv e I with
    | some refined => some { bound := refined, partitions := 2 }
    | none => none
  | n + 1 =>
    match integrateRefinedWithInv e I with
    | none => none
    | some refined =>
      if adaptiveErrorEstimate refined ≤ tol then
        -- Error is acceptable, return
        some { bound := refined, partitions := 2 }
      else
        -- Subdivide and recurse
        let (I₁, I₂) := splitMid I
        let localTol := tol / 2  -- Split tolerance between halves
        match integrateAdaptiveAuxWithInv e I₁ localTol n,
              integrateAdaptiveAuxWithInv e I₂ localTol n with
        | some r₁, some r₂ =>
          some {
            bound := IntervalRat.add r₁.bound r₂.bound
            partitions := r₁.partitions + r₂.partitions
          }
        | _, _ => none

/-- Adaptive integration with inverse support and error tolerance.
    Keeps subdividing until the uncertainty is below `tol`. -/
def integrateAdaptiveWithInv (e : Expr) (I : IntervalRat) (tol : ℚ)
    (maxDepth : ℕ) : Option AdaptiveResultWithInv :=
  integrateAdaptiveAuxWithInv e I tol maxDepth

/-! #### Correctness proofs for adaptive integration with inverse support -/

/-- integrateRefinedWithInv is correct (direct from integratePartitionWithInv_correct) -/
theorem integrateRefinedWithInv_correct (e : Expr) (hsupp : ExprSupportedWithInv e)
    (I : IntervalRat) (bound : IntervalRat)
    (hsome : integrateRefinedWithInv e I = some bound)
    (hInt : IntervalIntegrable (fun x => Expr.eval (fun _ => x) e) volume I.lo I.hi) :
    ∫ x in (I.lo : ℝ)..(I.hi : ℝ), Expr.eval (fun _ => x) e ∈ bound :=
  integratePartitionWithInv_correct e hsupp I 2 (by norm_num) bound hsome hInt

/-- Integrability on left half after midpoint split -/
theorem intervalIntegrable_splitMid_left_withInv (e : Expr) (I : IntervalRat)
    (hInt : IntervalIntegrable (fun x => Expr.eval (fun _ => x) e) volume I.lo I.hi) :
    IntervalIntegrable (fun x => Expr.eval (fun _ => x) e) volume
      (splitMid I).1.lo (splitMid I).1.hi := by
  simp only [splitMid_left_lo, splitMid_left_hi]
  exact hInt.mono_set (Set.uIcc_subset_uIcc (Set.left_mem_uIcc) (midpoint_mem_uIcc I))

/-- Integrability on right half after midpoint split -/
theorem intervalIntegrable_splitMid_right_withInv (e : Expr) (I : IntervalRat)
    (hInt : IntervalIntegrable (fun x => Expr.eval (fun _ => x) e) volume I.lo I.hi) :
    IntervalIntegrable (fun x => Expr.eval (fun _ => x) e) volume
      (splitMid I).2.lo (splitMid I).2.hi := by
  simp only [splitMid_right_lo, splitMid_right_hi]
  exact hInt.mono_set (Set.uIcc_subset_uIcc (midpoint_mem_uIcc I) (Set.right_mem_uIcc))

/-- Integral over split interval equals sum of integrals over halves -/
theorem integral_split_mid_withInv (e : Expr) (I : IntervalRat)
    (hInt : IntervalIntegrable (fun x => Expr.eval (fun _ => x) e) volume I.lo I.hi) :
    ∫ x in (I.lo : ℝ)..(I.hi : ℝ), Expr.eval (fun _ => x) e =
    (∫ x in (I.lo : ℝ)..(I.midpoint : ℝ), Expr.eval (fun _ => x) e) +
    (∫ x in (I.midpoint : ℝ)..(I.hi : ℝ), Expr.eval (fun _ => x) e) := by
  have hInt1 : IntervalIntegrable (fun x => Expr.eval (fun _ => x) e) volume I.lo I.midpoint :=
    hInt.mono_set (Set.uIcc_subset_uIcc (Set.left_mem_uIcc) (midpoint_mem_uIcc I))
  have hInt2 : IntervalIntegrable (fun x => Expr.eval (fun _ => x) e) volume I.midpoint I.hi :=
    hInt.mono_set (Set.uIcc_subset_uIcc (midpoint_mem_uIcc I) (Set.right_mem_uIcc))
  exact (intervalIntegral.integral_add_adjacent_intervals hInt1 hInt2).symm

/-- Main soundness theorem: adaptive integration returns a bound containing the true integral.
    This is proved by induction on maxDepth. -/
theorem integrateAdaptiveAuxWithInv_correct (e : Expr) (hsupp : ExprSupportedWithInv e)
    (I : IntervalRat) (tol : ℚ) (maxDepth : ℕ) (result : AdaptiveResultWithInv)
    (hsome : integrateAdaptiveAuxWithInv e I tol maxDepth = some result)
    (hInt : IntervalIntegrable (fun x => Expr.eval (fun _ => x) e) volume I.lo I.hi) :
    ∫ x in (I.lo : ℝ)..(I.hi : ℝ), Expr.eval (fun _ => x) e ∈ result.bound := by
  induction maxDepth generalizing I tol result with
  | zero =>
    -- Base case: returns integrateRefinedWithInv, which is correct
    simp only [integrateAdaptiveAuxWithInv] at hsome
    cases hrefined : integrateRefinedWithInv e I with
    | none => simp [hrefined] at hsome
    | some refined =>
      simp only [hrefined, Option.some.injEq] at hsome
      cases hsome
      exact integrateRefinedWithInv_correct e hsupp I refined hrefined hInt
  | succ n ih =>
    simp only [integrateAdaptiveAuxWithInv] at hsome
    cases hrefined : integrateRefinedWithInv e I with
    | none => simp [hrefined] at hsome
    | some refined =>
      simp only [hrefined] at hsome
      split_ifs at hsome with herr
      · -- Error acceptable: returns integrateRefinedWithInv
        simp only [Option.some.injEq] at hsome
        cases hsome
        exact integrateRefinedWithInv_correct e hsupp I refined hrefined hInt
      · -- Subdivide case
        cases hr1 : integrateAdaptiveAuxWithInv e (splitMid I).1 (tol / 2) n with
        | none => simp [hr1] at hsome
        | some r1 =>
          cases hr2 : integrateAdaptiveAuxWithInv e (splitMid I).2 (tol / 2) n with
          | none => simp [hr1, hr2] at hsome
          | some r2 =>
            simp only [hr1, hr2, Option.some.injEq] at hsome
            cases hsome
            -- Split the integral
            have hsplit := integral_split_mid_withInv e I hInt
            rw [hsplit]
            -- Get bounds for each half
            have hInt₁ := intervalIntegrable_splitMid_left_withInv e I hInt
            have hInt₂ := intervalIntegrable_splitMid_right_withInv e I hInt
            have h1 := ih (splitMid I).1 (tol / 2) r1 hr1 hInt₁
            have h2 := ih (splitMid I).2 (tol / 2) r2 hr2 hInt₂
            -- The bounds are correct, so their sum contains the sum of integrals
            simp only [splitMid_left_lo, splitMid_left_hi,
                       splitMid_right_lo, splitMid_right_hi] at h1 h2
            exact IntervalRat.mem_add h1 h2

/-- Soundness of the main adaptive integration function with inverse support -/
theorem integrateAdaptiveWithInv_correct (e : Expr) (hsupp : ExprSupportedWithInv e)
    (I : IntervalRat) (tol : ℚ) (maxDepth : ℕ) (result : AdaptiveResultWithInv)
    (hsome : integrateAdaptiveWithInv e I tol maxDepth = some result)
    (hInt : IntervalIntegrable (fun x => Expr.eval (fun _ => x) e) volume I.lo I.hi) :
    ∫ x in (I.lo : ℝ)..(I.hi : ℝ), Expr.eval (fun _ => x) e ∈ result.bound :=
  integrateAdaptiveAuxWithInv_correct e hsupp I tol maxDepth result hsome hInt

/-! #### Adaptive integral bound checkers for native_decide -/

/-- Boolean checker for adaptive integral lower bounds.
    More efficient than uniform partitioning for functions with singularities. -/
def checkIntegralAdaptiveLowerBound (e : Expr) (I : IntervalRat) (tol : ℚ)
    (maxDepth : ℕ) (c : ℚ) : Bool :=
  match integrateAdaptiveWithInv e I tol maxDepth with
  | some result => decide (c ≤ result.bound.lo)
  | none => false

/-- Boolean checker for adaptive integral upper bounds.
    More efficient than uniform partitioning for functions with singularities. -/
def checkIntegralAdaptiveUpperBound (e : Expr) (I : IntervalRat) (tol : ℚ)
    (maxDepth : ℕ) (c : ℚ) : Bool :=
  match integrateAdaptiveWithInv e I tol maxDepth with
  | some result => decide (result.bound.hi ≤ c)
  | none => false

/-- Bridge theorem: if `checkIntegralAdaptiveLowerBound` returns true, the integral is ≥ c. -/
theorem integral_adaptive_lower_of_check (e : Expr) (hsupp : ExprSupportedWithInv e)
    (I : IntervalRat) (tol : ℚ) (maxDepth : ℕ) (c : ℚ)
    (hcheck : checkIntegralAdaptiveLowerBound e I tol maxDepth c = true)
    (hInt : IntervalIntegrable (fun x => Expr.eval (fun _ => x) e) volume I.lo I.hi) :
    (c : ℝ) ≤ ∫ x in (I.lo : ℝ)..(I.hi : ℝ), Expr.eval (fun _ => x) e := by
  unfold checkIntegralAdaptiveLowerBound at hcheck
  cases hbound : integrateAdaptiveWithInv e I tol maxDepth with
  | none => simp [hbound] at hcheck
  | some result =>
    simp only [hbound, decide_eq_true_eq] at hcheck
    have hmem := integrateAdaptiveWithInv_correct e hsupp I tol maxDepth result hbound hInt
    simp only [IntervalRat.mem_def] at hmem
    calc (c : ℝ) ≤ (result.bound.lo : ℝ) := by exact_mod_cast hcheck
      _ ≤ ∫ x in (I.lo : ℝ)..(I.hi : ℝ), Expr.eval (fun _ => x) e := hmem.1

/-- Bridge theorem: if `checkIntegralAdaptiveUpperBound` returns true, the integral is ≤ c. -/
theorem integral_adaptive_upper_of_check (e : Expr) (hsupp : ExprSupportedWithInv e)
    (I : IntervalRat) (tol : ℚ) (maxDepth : ℕ) (c : ℚ)
    (hcheck : checkIntegralAdaptiveUpperBound e I tol maxDepth c = true)
    (hInt : IntervalIntegrable (fun x => Expr.eval (fun _ => x) e) volume I.lo I.hi) :
    ∫ x in (I.lo : ℝ)..(I.hi : ℝ), Expr.eval (fun _ => x) e ≤ (c : ℝ) := by
  unfold checkIntegralAdaptiveUpperBound at hcheck
  cases hbound : integrateAdaptiveWithInv e I tol maxDepth with
  | none => simp [hbound] at hcheck
  | some result =>
    simp only [hbound, decide_eq_true_eq] at hcheck
    have hmem := integrateAdaptiveWithInv_correct e hsupp I tol maxDepth result hbound hInt
    simp only [IntervalRat.mem_def] at hmem
    calc ∫ x in (I.lo : ℝ)..(I.hi : ℝ), Expr.eval (fun _ => x) e ≤ (result.bound.hi : ℝ) := hmem.2
      _ ≤ (c : ℝ) := by exact_mod_cast hcheck

/-! ### Exponential Search for Optimal Partition Count

Instead of using a fixed large N or deep adaptive recursion, we can search for
the minimum partition count that achieves the desired bound. This is often
much faster because many integrals only need N=100-500 instead of N=3000.

Algorithm:
1. Start with N=startN (e.g., 32)
2. Double N until the bound is achieved (exponential search)
3. Return the first N that works

This finds the optimal N in O(log(N)) integration attempts.
-/

/-- Exponential search with explicit fuel for termination.
    Returns the computed bound if found within fuel doublings, or `none` otherwise. -/
def searchPartitionLowerAux (e : Expr) (I : IntervalRat) (n maxN : ℕ) (c : ℚ)
    (fuel : ℕ) : Option IntervalRat :=
  match fuel with
  | 0 => none
  | fuel' + 1 =>
    if n > maxN then none
    else if _hn : 0 < n then
      match integratePartitionWithInv e I n with
      | some J =>
        if decide (c ≤ J.lo) then some J
        else searchPartitionLowerAux e I (2 * n) maxN c fuel'
      | none => none
    else none

/-- Exponential search for minimum partition count that achieves a lower bound. -/
def searchPartitionLower (e : Expr) (I : IntervalRat) (startN maxN : ℕ) (c : ℚ) :
    Option IntervalRat :=
  searchPartitionLowerAux e I startN maxN c 20  -- 20 doublings allows up to startN * 2^20

/-- Exponential search with explicit fuel for upper bounds. -/
def searchPartitionUpperAux (e : Expr) (I : IntervalRat) (n maxN : ℕ) (c : ℚ)
    (fuel : ℕ) : Option IntervalRat :=
  match fuel with
  | 0 => none
  | fuel' + 1 =>
    if n > maxN then none
    else if _hn : 0 < n then
      match integratePartitionWithInv e I n with
      | some J =>
        if decide (J.hi ≤ c) then some J
        else searchPartitionUpperAux e I (2 * n) maxN c fuel'
      | none => none
    else none

/-- Exponential search for minimum partition count that achieves an upper bound. -/
def searchPartitionUpper (e : Expr) (I : IntervalRat) (startN maxN : ℕ) (c : ℚ) :
    Option IntervalRat :=
  searchPartitionUpperAux e I startN maxN c 20

/-- Check lower bound using exponential search to find optimal N.
    Much faster than fixed large N when fewer partitions suffice.
    startN: initial partition count (e.g., 32)
    maxN: maximum partitions to try (e.g., 8192) -/
def checkIntegralSearchLowerBound (e : Expr) (I : IntervalRat)
    (startN maxN : ℕ) (c : ℚ) : Bool :=
  (searchPartitionLower e I startN maxN c).isSome

/-- Check upper bound using exponential search to find optimal N. -/
def checkIntegralSearchUpperBound (e : Expr) (I : IntervalRat)
    (startN maxN : ℕ) (c : ℚ) : Bool :=
  (searchPartitionUpper e I startN maxN c).isSome

/-- Helper: if searchPartitionLowerAux succeeds, the result satisfies the bound. -/
theorem searchPartitionLowerAux_spec (e : Expr) (I : IntervalRat) (n maxN : ℕ) (c : ℚ)
    (fuel : ℕ) (J : IntervalRat) (hfind : searchPartitionLowerAux e I n maxN c fuel = some J) :
    c ≤ J.lo := by
  induction fuel generalizing n with
  | zero => simp [searchPartitionLowerAux] at hfind
  | succ fuel' ih =>
    simp only [searchPartitionLowerAux] at hfind
    split at hfind
    · simp at hfind
    · split at hfind
      · cases hint : integratePartitionWithInv e I n with
        | none => simp [hint] at hfind
        | some J' =>
          simp only [hint] at hfind
          split at hfind
          · simp only [Option.some.injEq] at hfind
            subst hfind
            simp_all only [decide_eq_true_eq]
          · exact ih (2 * n) hfind
      · simp at hfind

/-- Helper: if searchPartitionUpperAux succeeds, the result satisfies the bound. -/
theorem searchPartitionUpperAux_spec (e : Expr) (I : IntervalRat) (n maxN : ℕ) (c : ℚ)
    (fuel : ℕ) (J : IntervalRat) (hfind : searchPartitionUpperAux e I n maxN c fuel = some J) :
    J.hi ≤ c := by
  induction fuel generalizing n with
  | zero => simp [searchPartitionUpperAux] at hfind
  | succ fuel' ih =>
    simp only [searchPartitionUpperAux] at hfind
    split at hfind
    · simp at hfind
    · split at hfind
      · cases hint : integratePartitionWithInv e I n with
        | none => simp [hint] at hfind
        | some J' =>
          simp only [hint] at hfind
          split at hfind
          · simp only [Option.some.injEq] at hfind
            subst hfind
            simp_all only [decide_eq_true_eq]
          · exact ih (2 * n) hfind
      · simp at hfind

/-- Helper: searchPartitionLowerAux returns a valid integration bound. -/
theorem searchPartitionLowerAux_valid (e : Expr) (hsupp : ExprSupportedWithInv e)
    (I : IntervalRat) (n maxN : ℕ) (_hn : 0 < n) (c : ℚ) (fuel : ℕ) (J : IntervalRat)
    (hfind : searchPartitionLowerAux e I n maxN c fuel = some J)
    (hInt : IntervalIntegrable (fun x => Expr.eval (fun _ => x) e) volume I.lo I.hi) :
    ∫ x in (I.lo : ℝ)..(I.hi : ℝ), Expr.eval (fun _ => x) e ∈ J := by
  induction fuel generalizing n with
  | zero => simp [searchPartitionLowerAux] at hfind
  | succ fuel' ih =>
    simp only [searchPartitionLowerAux] at hfind
    by_cases hle : n > maxN
    · simp [hle] at hfind
    · simp only [hle, ↓reduceIte] at hfind
      by_cases hn' : 0 < n
      · simp only [hn', ↓reduceDIte] at hfind
        cases hint : integratePartitionWithInv e I n with
        | none => simp [hint] at hfind
        | some J' =>
          simp only [hint] at hfind
          by_cases hdec : c ≤ J'.lo
          · simp only [decide_eq_true hdec, ↓reduceIte, Option.some.injEq] at hfind
            subst hfind
            exact integratePartitionWithInv_correct e hsupp I n hn' J' hint hInt
          · simp only [decide_eq_false hdec, Bool.false_eq_true, ↓reduceIte] at hfind
            have h2n_pos : 0 < 2 * n := by omega
            exact ih (2 * n) h2n_pos hfind
      · simp [hn'] at hfind

/-- Helper: searchPartitionUpperAux returns a valid integration bound. -/
theorem searchPartitionUpperAux_valid (e : Expr) (hsupp : ExprSupportedWithInv e)
    (I : IntervalRat) (n maxN : ℕ) (_hn : 0 < n) (c : ℚ) (fuel : ℕ) (J : IntervalRat)
    (hfind : searchPartitionUpperAux e I n maxN c fuel = some J)
    (hInt : IntervalIntegrable (fun x => Expr.eval (fun _ => x) e) volume I.lo I.hi) :
    ∫ x in (I.lo : ℝ)..(I.hi : ℝ), Expr.eval (fun _ => x) e ∈ J := by
  induction fuel generalizing n with
  | zero => simp [searchPartitionUpperAux] at hfind
  | succ fuel' ih =>
    simp only [searchPartitionUpperAux] at hfind
    by_cases hle : n > maxN
    · simp [hle] at hfind
    · simp only [hle, ↓reduceIte] at hfind
      by_cases hn' : 0 < n
      · simp only [hn', ↓reduceDIte] at hfind
        cases hint : integratePartitionWithInv e I n with
        | none => simp [hint] at hfind
        | some J' =>
          simp only [hint] at hfind
          by_cases hdec : J'.hi ≤ c
          · simp only [decide_eq_true hdec, ↓reduceIte, Option.some.injEq] at hfind
            subst hfind
            exact integratePartitionWithInv_correct e hsupp I n hn' J' hint hInt
          · simp only [decide_eq_false hdec, Bool.false_eq_true, ↓reduceIte] at hfind
            have h2n_pos : 0 < 2 * n := by omega
            exact ih (2 * n) h2n_pos hfind
      · simp [hn'] at hfind

/-- Bridge theorem: if exponential search succeeds, the integral satisfies the lower bound. -/
theorem integral_search_lower_of_check (e : Expr) (hsupp : ExprSupportedWithInv e)
    (I : IntervalRat) (startN maxN : ℕ) (hstart : 0 < startN) (c : ℚ)
    (hcheck : checkIntegralSearchLowerBound e I startN maxN c = true)
    (hInt : IntervalIntegrable (fun x => Expr.eval (fun _ => x) e) volume I.lo I.hi) :
    (c : ℝ) ≤ ∫ x in (I.lo : ℝ)..(I.hi : ℝ), Expr.eval (fun _ => x) e := by
  unfold checkIntegralSearchLowerBound searchPartitionLower at hcheck
  simp only [Option.isSome_iff_exists] at hcheck
  obtain ⟨J, hJ⟩ := hcheck
  have hcJ := searchPartitionLowerAux_spec e I startN maxN c 20 J hJ
  have hmem := searchPartitionLowerAux_valid e hsupp I startN maxN hstart c 20 J hJ hInt
  simp only [IntervalRat.mem_def] at hmem
  calc (c : ℝ) ≤ (J.lo : ℝ) := by exact_mod_cast hcJ
    _ ≤ ∫ x in (I.lo : ℝ)..(I.hi : ℝ), Expr.eval (fun _ => x) e := hmem.1

/-- Bridge theorem: if exponential search succeeds, the integral satisfies the upper bound. -/
theorem integral_search_upper_of_check (e : Expr) (hsupp : ExprSupportedWithInv e)
    (I : IntervalRat) (startN maxN : ℕ) (hstart : 0 < startN) (c : ℚ)
    (hcheck : checkIntegralSearchUpperBound e I startN maxN c = true)
    (hInt : IntervalIntegrable (fun x => Expr.eval (fun _ => x) e) volume I.lo I.hi) :
    ∫ x in (I.lo : ℝ)..(I.hi : ℝ), Expr.eval (fun _ => x) e ≤ (c : ℝ) := by
  unfold checkIntegralSearchUpperBound searchPartitionUpper at hcheck
  simp only [Option.isSome_iff_exists] at hcheck
  obtain ⟨J, hJ⟩ := hcheck
  have hcJ := searchPartitionUpperAux_spec e I startN maxN c 20 J hJ
  have hmem := searchPartitionUpperAux_valid e hsupp I startN maxN hstart c 20 J hJ hInt
  simp only [IntervalRat.mem_def] at hmem
  calc ∫ x in (I.lo : ℝ)..(I.hi : ℝ), Expr.eval (fun _ => x) e ≤ (J.hi : ℝ) := hmem.2
    _ ≤ (c : ℝ) := by exact_mod_cast hcJ

end LeanCert.Validity.Integration

/-! ## Certificate-Based Integration (Proof by Reflection)

This implements the "mega-theorem" approach where:
1. **Search (untrusted)**: Pre-compute partition list via adaptive algorithm
2. **Certificate**: Store the list of (domain, bound) pairs
3. **Verify (trusted)**: Linear checker verifies each bound is valid

Why this is faster:
- No branching/recursion in kernel - just linear iteration
- Certificate can be saved/loaded (checkpointing)
- Separates algorithm complexity from verification complexity
-/

namespace LeanCert.Validity.CertificateIntegration

open LeanCert.Core
open LeanCert.Engine
open LeanCert.Validity.Integration

/-- A single partition entry in an integral certificate -/
structure PartitionEntry where
  /-- The domain interval for this partition -/
  domain : IntervalRat
  /-- The claimed bound on the integral over this partition -/
  bound : IntervalRat
  deriving Repr

instance : Inhabited PartitionEntry where
  default := ⟨⟨0, 0, le_refl 0⟩, ⟨0, 0, le_refl 0⟩⟩

/-- Certificate for a definite integral computation.
    Contains pre-computed partitions and their bounds. -/
structure IntegralCertificate where
  /-- The expression being integrated -/
  expr_id : String  -- For documentation/debugging only
  /-- The overall integration domain [a, b] -/
  domain : IntervalRat
  /-- List of partition entries -/
  partitions : List PartitionEntry
  deriving Repr

/-! ### Certificate Verification (Linear Checker)

These functions are what the kernel actually executes.
They are purely linear - no recursion, no branching on computed values.
-/

/-- Check that partition domains cover [a, b] contiguously.
    Returns true iff domains are [a, t₁], [t₁, t₂], ..., [tₙ₋₁, b] -/
def checkCoverage (entries : List PartitionEntry) (domain : IntervalRat) : Bool :=
  match entries with
  | [] => false  -- Empty partition doesn't cover anything
  | e :: es =>
    -- First partition must start at domain.lo
    if decide (e.domain.lo ≠ domain.lo) then false
    else
      let rec checkContiguous : List PartitionEntry → ℚ → Bool
        | [], lastHi => decide (lastHi = domain.hi)
        | e :: es, lastHi =>
          if decide (e.domain.lo ≠ lastHi) then false
          else checkContiguous es e.domain.hi
      checkContiguous es e.domain.hi

/-- Check that a single partition bound is valid using evalInterval?1.
    This is the core soundness check for each partition. -/
def checkPartitionBound (e : Expr) (entry : PartitionEntry) : Bool :=
  match evalInterval?1 e entry.domain with
  | none => false  -- Domain invalid
  | some computed =>
    -- The computed integral bound must be contained in the claimed bound
    -- Integral bound = computed * width
    let width := entry.domain.hi - entry.domain.lo
    let integralLo := computed.lo * width
    let integralHi := computed.hi * width
    decide (entry.bound.lo ≤ integralLo ∧ integralHi ≤ entry.bound.hi)

/-- Check all partition bounds are valid -/
def checkAllBounds (e : Expr) (entries : List PartitionEntry) : Bool :=
  entries.all (checkPartitionBound e)

/-- Sum all partition bounds -/
def sumBounds (entries : List PartitionEntry) : IntervalRat :=
  entries.foldl (fun acc entry => IntervalRat.add acc entry.bound)
    ⟨0, 0, le_refl 0⟩

/-- Check that the sum of bounds is contained in a target interval -/
def checkSumInTarget (entries : List PartitionEntry) (target : IntervalRat) : Bool :=
  let sum := sumBounds entries
  decide (target.lo ≤ sum.lo ∧ sum.hi ≤ target.hi)

/-- The main certificate verifier - LINEAR, no recursion in control flow.
    Returns true iff:
    1. Coverage: partition domains cover the overall domain contiguously
    2. Soundness: each partition bound is valid (evalInterval ⊆ bound)
    3. Target: sum of bounds is contained in target -/
def verifyCertificate (e : Expr) (cert : IntegralCertificate) (target : IntervalRat) : Bool :=
  checkCoverage cert.partitions cert.domain &&
  checkAllBounds e cert.partitions &&
  checkSumInTarget cert.partitions target

/-! ### Soundness Theorems

These theorems prove that if verifyCertificate returns true,
the actual integral is contained in the target interval.
-/

/-- Coverage implies the partition intervals form a valid partition -/
theorem coverage_implies_partition (entries : List PartitionEntry)
    (domain : IntervalRat) (hcov : checkCoverage entries domain = true) :
    entries ≠ [] := by
  cases entries with
  | nil => simp [checkCoverage] at hcov
  | cons e es => simp

/-! ### Singleton Multiplication Lemmas

These lemmas characterize the behavior of IntervalRat.mul when one operand
is a singleton interval [w, w]. For w ≥ 0, multiplying [w, w] × [lo, hi]
gives [w·lo, w·hi]. -/

/-- For singleton multiplication, .lo equals min of corner products,
    which simplifies to min (w*lo) (w*hi) since singleton has equal endpoints. -/
theorem singleton_mul_lo_eq_min (w : ℚ) (J : IntervalRat) :
    (IntervalRat.mul (IntervalRat.singleton w) J).lo = min (w * J.lo) (w * J.hi) := by
  -- The mul definition uses min4 of all corner products
  -- For singleton, corner products are (w*lo), (w*hi), (w*lo), (w*hi)
  -- min4 a b a b = min (min a b) (min a b) = min a b
  simp only [IntervalRat.mul, IntervalRat.singleton]
  -- Goal: min4 (w*J.lo) (w*J.hi) (w*J.lo) (w*J.hi) = min (w*J.lo) (w*J.hi)
  -- min4 is defined as: min (min a b) (min c d)
  -- So min4 a b a b = min (min a b) (min a b) = min a b
  show min (min (w * J.lo) (w * J.hi)) (min (w * J.lo) (w * J.hi)) = min (w * J.lo) (w * J.hi)
  rw [min_self]

/-- For singleton multiplication, .hi equals max of corner products,
    which simplifies to max (w*lo) (w*hi) since singleton has equal endpoints. -/
theorem singleton_mul_hi_eq_max (w : ℚ) (J : IntervalRat) :
    (IntervalRat.mul (IntervalRat.singleton w) J).hi = max (w * J.lo) (w * J.hi) := by
  simp only [IntervalRat.mul, IntervalRat.singleton]
  show max (max (w * J.lo) (w * J.hi)) (max (w * J.lo) (w * J.hi)) = max (w * J.lo) (w * J.hi)
  rw [max_self]

/-- For singleton multiplication with non-negative width, the lower bound
    equals width times the interval's lower bound. -/
theorem singleton_mul_lo_nonneg (w : ℚ) (J : IntervalRat) (hw : 0 ≤ w) :
    (IntervalRat.mul (IntervalRat.singleton w) J).lo = w * J.lo := by
  rw [singleton_mul_lo_eq_min]
  have h := J.le
  have hwmul : w * J.lo ≤ w * J.hi := mul_le_mul_of_nonneg_left h hw
  exact min_eq_left hwmul

/-- For singleton multiplication with non-negative width, the upper bound
    equals width times the interval's upper bound. -/
theorem singleton_mul_hi_nonneg (w : ℚ) (J : IntervalRat) (hw : 0 ≤ w) :
    (IntervalRat.mul (IntervalRat.singleton w) J).hi = w * J.hi := by
  rw [singleton_mul_hi_eq_max]
  have h := J.le
  have hwmul : w * J.lo ≤ w * J.hi := mul_le_mul_of_nonneg_left h hw
  exact max_eq_right hwmul

/-- Single partition bound correctness.

The proof uses `integrateInterval1WithInv_correct` which shows that for
`evalInterval?1 e I = some J`, the integral ∫[I.lo, I.hi] f ∈ I.width * J.

Since `checkPartitionBound` verifies that `entry.bound` contains `width * computed`,
we get that the integral is in `entry.bound`. -/
theorem partition_bound_correct (e : Expr) (hsupp : ExprSupportedWithInv e)
    (entry : PartitionEntry)
    (hcheck : checkPartitionBound e entry = true)
    (hInt : IntervalIntegrable (fun x => Expr.eval (fun _ => x) e)
      MeasureTheory.volume (entry.domain.lo : ℝ) (entry.domain.hi : ℝ)) :
    ∫ x in (entry.domain.lo : ℝ)..(entry.domain.hi : ℝ),
      Expr.eval (fun _ => x) e ∈ entry.bound := by
  -- Extract the computed interval from checkPartitionBound
  simp only [checkPartitionBound] at hcheck
  cases heval : evalInterval?1 e entry.domain with
  | none => simp [heval] at hcheck
  | some computed =>
    simp only [heval, decide_eq_true_eq] at hcheck
    obtain ⟨hlo_check, hhi_check⟩ := hcheck
    -- Use integrateInterval1WithInv_correct to get integral bounds
    have hsome : integrateInterval1WithInv e entry.domain =
        some (IntervalRat.mul (IntervalRat.singleton entry.domain.width) computed) := by
      simp only [integrateInterval1WithInv, heval]
    have hmem := integrateInterval1WithInv_correct e hsupp entry.domain
      (IntervalRat.mul (IntervalRat.singleton entry.domain.width) computed) hsome hInt
    -- hmem says: integral ∈ IntervalRat.mul (singleton width) computed
    -- hlo_check says: entry.bound.lo ≤ computed.lo * width
    -- hhi_check says: computed.hi * width ≤ entry.bound.hi
    -- The interval mul (singleton w) J gives [w*J.lo, w*J.hi] when w ≥ 0
    -- So we need: entry.bound contains [width * computed.lo, width * computed.hi]
    -- which contains the integral.
    rw [IntervalRat.mem_def] at hmem ⊢
    have hwidth_nn : (0 : ℚ) ≤ entry.domain.width := IntervalRat.width_nonneg entry.domain
    have hcomp_le : computed.lo ≤ computed.hi := computed.le
    -- Technical lemmas about interval multiplication bounds
    have hmul_lo_le : (entry.domain.width * computed.lo : ℝ) ≤
        ((IntervalRat.mul (IntervalRat.singleton entry.domain.width) computed).lo : ℝ) ∨
        ((IntervalRat.mul (IntervalRat.singleton entry.domain.width) computed).lo : ℝ) ≤
        (entry.domain.width * computed.lo : ℝ) := le_total _ _
    have hmul_hi_le : (entry.domain.width * computed.hi : ℝ) ≤
        ((IntervalRat.mul (IntervalRat.singleton entry.domain.width) computed).hi : ℝ) ∨
        ((IntervalRat.mul (IntervalRat.singleton entry.domain.width) computed).hi : ℝ) ≤
        (entry.domain.width * computed.hi : ℝ) := le_total _ _
    -- The interval bound from integrateInterval1WithInv satisfies:
    -- lo ≤ width * computed.lo and width * computed.hi ≤ hi (when width ≥ 0)
    -- This follows from how IntervalRat.mul is defined for singletons
    have hlo_eq : (computed.lo * (entry.domain.hi - entry.domain.lo) : ℚ) =
        entry.domain.width * computed.lo := by unfold IntervalRat.width; ring
    have hhi_eq : (computed.hi * (entry.domain.hi - entry.domain.lo) : ℚ) =
        entry.domain.width * computed.hi := by unfold IntervalRat.width; ring
    constructor
    · -- entry.bound.lo ≤ integral
      have h1 : (entry.bound.lo : ℝ) ≤ (entry.domain.width * computed.lo : ℝ) := by
        have h := hlo_check
        rw [hlo_eq] at h
        exact_mod_cast h
      -- Use singleton_mul_lo_nonneg: for w ≥ 0, (singleton w).mul J).lo = w * J.lo
      have hmul_bound_lo_eq : ((IntervalRat.mul (IntervalRat.singleton entry.domain.width) computed).lo : ℝ) =
          (entry.domain.width * computed.lo : ℝ) := by
        simp only [singleton_mul_lo_nonneg entry.domain.width computed hwidth_nn, Rat.cast_mul]
      linarith [hmem.1]
    · -- integral ≤ entry.bound.hi
      have h1 : (entry.domain.width * computed.hi : ℝ) ≤ (entry.bound.hi : ℝ) := by
        have h := hhi_check
        rw [hhi_eq] at h
        exact_mod_cast h
      -- Use singleton_mul_hi_nonneg: for w ≥ 0, (singleton w).mul J).hi = w * J.hi
      have hmul_bound_hi_eq : ((IntervalRat.mul (IntervalRat.singleton entry.domain.width) computed).hi : ℝ) =
          (entry.domain.width * computed.hi : ℝ) := by
        simp only [singleton_mul_hi_nonneg entry.domain.width computed hwidth_nn, Rat.cast_mul]
      linarith [hmem.2]

/-- Helper: foldl add accumulates correctly -/
private theorem foldl_add_mem (acc : IntervalRat) (accVal : ℝ) (hacc : accVal ∈ acc)
    (vals : List ℝ) (intervals : List IntervalRat)
    (hlen : vals.length = intervals.length)
    (hmem : ∀ i (hi : i < vals.length),
      (vals[i] : ℝ) ∈ (intervals[i]'(hlen ▸ hi) : IntervalRat)) :
    accVal + vals.sum ∈ (intervals.foldl (fun a I => IntervalRat.add a I) acc) := by
  induction vals generalizing acc accVal intervals with
  | nil =>
    simp only [List.length_nil] at hlen
    cases intervals with
    | nil => simp [hacc]
    | cons h t => simp at hlen
  | cons v vs ih =>
    cases intervals with
    | nil => simp at hlen
    | cons I Is =>
      simp only [List.length_cons, add_left_inj] at hlen
      simp only [List.foldl_cons, List.sum_cons]
      -- accVal + (v + vs.sum) = (accVal + v) + vs.sum
      rw [← add_assoc]
      -- Show accVal + v ∈ IntervalRat.add acc I
      have hacc' : accVal + v ∈ IntervalRat.add acc I := by
        apply IntervalRat.mem_add hacc
        exact hmem 0 (by simp)
      -- Show remaining membership
      have hmem' : ∀ (i : ℕ) (hi : i < vs.length), vs[i] ∈ Is[i] := by
        intro i hi
        have h := hmem (i + 1) (by simp; omega)
        simp only [List.getElem_cons_succ] at h
        convert h using 1
      exact ih (IntervalRat.add acc I) (accVal + v) hacc' Is hlen hmem'

/-- Sum of values in intervals is in the sum interval -/
theorem sum_mem_sum_intervals (vals : List ℝ) (intervals : List IntervalRat)
    (hlen : vals.length = intervals.length)
    (hmem : ∀ i (hi : i < vals.length),
      (vals[i] : ℝ) ∈ (intervals[i]'(hlen ▸ hi) : IntervalRat)) :
    vals.sum ∈ (intervals.foldl (fun acc I => IntervalRat.add acc I) ⟨0, 0, le_refl 0⟩) := by
  have h := foldl_add_mem ⟨0, 0, le_refl 0⟩ 0 (by simp [IntervalRat.mem_def]) vals intervals hlen hmem
  simp at h
  exact h

/-- Coverage implies the first entry starts at domain.lo -/
theorem coverage_first_starts (entries : List PartitionEntry) (domain : IntervalRat)
    (hcov : checkCoverage entries domain = true) (hne : entries ≠ []) :
    (entries.head hne).domain.lo = domain.lo := by
  cases entries with
  | nil => simp at hne
  | cons e es =>
    simp only [List.head_cons]
    simp only [checkCoverage] at hcov
    by_cases h : e.domain.lo = domain.lo
    · exact h
    · -- Contradiction: checkCoverage would return false
      exfalso
      simp only [ne_eq, h, not_false_eq_true, decide_true, ↓reduceIte] at hcov
      exact Bool.noConfusion hcov

/-- Helper: checkContiguous ending at domain.hi means the last entry ends there -/
private theorem checkContiguous_last_ends_aux (es : List PartitionEntry) (lastHi : ℚ)
    (domain : IntervalRat)
    (hcheck : checkCoverage.checkContiguous domain es lastHi = true)
    (hne : es ≠ []) :
    (es.getLast hne).domain.hi = domain.hi := by
  induction es generalizing lastHi with
  | nil => simp at hne
  | cons e es' ih =>
    simp only [checkCoverage.checkContiguous] at hcheck
    by_cases h : e.domain.lo = lastHi
    · simp only [h, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte] at hcheck
      cases es' with
      | nil =>
        simp only [List.getLast_singleton]
        simp only [checkCoverage.checkContiguous, decide_eq_true_eq] at hcheck
        exact hcheck
      | cons e' es'' =>
        simp only [List.getLast_cons_cons]
        exact ih e.domain.hi hcheck (by simp)
    · simp only [ne_eq, h, not_false_eq_true, decide_true, Bool.false_eq_true, ↓reduceIte] at hcheck

/-- Coverage implies the last entry ends at domain.hi -/
theorem coverage_last_ends (entries : List PartitionEntry) (domain : IntervalRat)
    (hcov : checkCoverage entries domain = true) (hne : entries ≠ []) :
    (entries.getLast hne).domain.hi = domain.hi := by
  cases entries with
  | nil => simp at hne
  | cons e es =>
    simp only [checkCoverage] at hcov
    by_cases h : e.domain.lo = domain.lo
    · simp only [h, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte] at hcov
      cases es with
      | nil =>
        simp only [List.getLast_singleton]
        simp only [checkCoverage.checkContiguous, decide_eq_true_eq] at hcov
        exact hcov
      | cons e' es' =>
        simp only [List.getLast_cons_cons]
        exact checkContiguous_last_ends_aux (e' :: es') e.domain.hi domain hcov (by simp)
    · simp only [ne_eq, h, not_false_eq_true, decide_true, Bool.false_eq_true, ↓reduceIte] at hcov

/-- Helper: checkContiguous implies adjacency within the list -/
private theorem checkContiguous_adjacent_aux (es : List PartitionEntry) (lastHi : ℚ)
    (domain : IntervalRat)
    (hcheck : checkCoverage.checkContiguous domain es lastHi = true)
    (i : ℕ) (hi : i + 1 < es.length) :
    (es[i]'(by omega)).domain.hi = (es[i + 1]'hi).domain.lo := by
  induction es generalizing lastHi i with
  | nil => simp at hi
  | cons e es' ih =>
    simp only [checkCoverage.checkContiguous] at hcheck
    by_cases h : e.domain.lo = lastHi
    · simp only [h, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte] at hcheck
      cases i with
      | zero =>
        -- Need to show e.domain.hi = (es'[0]).domain.lo
        cases es' with
        | nil => simp at hi
        | cons e' es'' =>
          -- From checkContiguous, e'.domain.lo = e.domain.hi (lastHi for next iteration)
          simp only [checkCoverage.checkContiguous] at hcheck
          by_cases h' : e'.domain.lo = e.domain.hi
          · exact h'.symm
          · simp only [ne_eq, h', not_false_eq_true, decide_true, Bool.false_eq_true, ↓reduceIte] at hcheck
      | succ j =>
        -- Use IH for es' with index j
        simp only [List.length_cons, Nat.add_lt_add_iff_right] at hi
        exact ih e.domain.hi hcheck j hi
    · simp only [ne_eq, h, not_false_eq_true, decide_true, Bool.false_eq_true, ↓reduceIte] at hcheck

/-- Coverage implies consecutive entries are adjacent -/
theorem coverage_adjacent (entries : List PartitionEntry) (domain : IntervalRat)
    (hcov : checkCoverage entries domain = true) (i : ℕ) (hi : i + 1 < entries.length) :
    (entries[i]'(by omega)).domain.hi = (entries[i + 1]'hi).domain.lo := by
  cases entries with
  | nil => simp at hi
  | cons e es =>
    simp only [checkCoverage] at hcov
    by_cases h : e.domain.lo = domain.lo
    · simp only [h, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte] at hcov
      cases i with
      | zero =>
        cases es with
        | nil => simp at hi
        | cons e' es' =>
          simp only [checkCoverage.checkContiguous] at hcov
          by_cases h' : e'.domain.lo = e.domain.hi
          · exact h'.symm
          · simp only [ne_eq, h', not_false_eq_true, decide_true, Bool.false_eq_true, ↓reduceIte] at hcov
      | succ j =>
        simp only [List.length_cons, Nat.add_lt_add_iff_right] at hi
        exact checkContiguous_adjacent_aux es e.domain.hi domain hcov j hi
    · simp only [ne_eq, h, not_false_eq_true, decide_true, Bool.false_eq_true, ↓reduceIte] at hcov

/-- Helper: integrability on a subinterval -/
private theorem integrable_subinterval (f : ℝ → ℝ) (a b c d : ℝ)
    (hab : a ≤ b) (hcd : c ≤ d) (hac : a ≤ c) (hdb : d ≤ b)
    (hInt : IntervalIntegrable f MeasureTheory.volume a b) :
    IntervalIntegrable f MeasureTheory.volume c d := by
  apply IntervalIntegrable.mono_set hInt
  rw [Set.uIcc_subset_uIcc_iff_le]
  simp only [min_eq_left hab, max_eq_right hab, min_eq_left hcd, max_eq_right hcd]
  exact ⟨hac, hdb⟩

/-- Coverage implies list is nonempty -/
private theorem coverage_nonempty (entries : List PartitionEntry) (domain : IntervalRat)
    (hcov : checkCoverage entries domain = true) : entries ≠ [] := by
  intro h
  simp only [h, checkCoverage, Bool.false_eq_true] at hcov

/-- Helper: coverage on cons implies checkContiguous on tail -/
private theorem coverage_tail_contiguous (e : PartitionEntry) (es : List PartitionEntry)
    (domain : IntervalRat) (hcov : checkCoverage (e :: es) domain = true) :
    checkCoverage.checkContiguous domain es e.domain.hi = true := by
  simp only [checkCoverage] at hcov
  by_cases h : e.domain.lo = domain.lo
  · simp only [h, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte] at hcov
    exact hcov
  · simp only [ne_eq, h, not_false_eq_true, decide_true, Bool.false_eq_true, ↓reduceIte] at hcov

/-- Helper: every entry's hi ≤ domain.hi when checkContiguous holds -/
private theorem contiguous_all_hi_le_domain_hi (es : List PartitionEntry) (lastHi : ℚ)
    (domain : IntervalRat)
    (hcheck : checkCoverage.checkContiguous domain es lastHi = true) :
    ∀ e ∈ es, e.domain.hi ≤ domain.hi := by
  induction es generalizing lastHi with
  | nil => intro e he; simp at he
  | cons e es' ih =>
    simp only [checkCoverage.checkContiguous] at hcheck
    by_cases h : e.domain.lo = lastHi
    · simp only [h, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte] at hcheck
      intro e' he'
      simp only [List.mem_cons] at he'
      cases he' with
      | inl heq =>
        rw [heq]
        cases es' with
        | nil =>
          simp only [checkCoverage.checkContiguous, decide_eq_true_eq] at hcheck
          exact le_of_eq hcheck
        | cons e'' es'' =>
          have hrec := ih e.domain.hi hcheck
          have he''_mem : e'' ∈ (e'' :: es'') := by simp
          have he''_hi := hrec e'' he''_mem
          simp only [checkCoverage.checkContiguous] at hcheck
          by_cases h' : e''.domain.lo = e.domain.hi
          · calc e.domain.hi = e''.domain.lo := h'.symm
              _ ≤ e''.domain.hi := e''.domain.le
              _ ≤ domain.hi := he''_hi
          · simp only [ne_eq, h', not_false_eq_true, decide_true, Bool.false_eq_true, ↓reduceIte] at hcheck
      | inr hmem =>
        exact ih e.domain.hi hcheck e' hmem
    · simp only [ne_eq, h, not_false_eq_true, decide_true, Bool.false_eq_true, ↓reduceIte] at hcheck

/-- Helper: monotonicity of entry endpoints in a contiguous partition -/
private theorem contiguous_entry_le_domain_hi (es : List PartitionEntry) (lastHi : ℚ)
    (domain : IntervalRat)
    (hcheck : checkCoverage.checkContiguous domain es lastHi = true)
    (i : ℕ) (hi : i < es.length) :
    (es[i]'hi).domain.hi ≤ domain.hi := by
  have hall := contiguous_all_hi_le_domain_hi es lastHi domain hcheck
  exact hall (es[i]'hi) (List.getElem_mem hi)

/-- Helper: first entry hi ≤ domain.hi -/
private theorem coverage_first_hi_le (entries : List PartitionEntry) (domain : IntervalRat)
    (hcov : checkCoverage entries domain = true) (hne : entries ≠ []) :
    (entries.head hne).domain.hi ≤ domain.hi := by
  cases entries with
  | nil => simp at hne
  | cons e es =>
    simp only [List.head_cons]
    have hcontig := coverage_tail_contiguous e es domain hcov
    cases es with
    | nil =>
      simp only [checkCoverage.checkContiguous, decide_eq_true_eq] at hcontig
      exact le_of_eq hcontig
    | cons e' es' =>
      exact contiguous_entry_le_domain_hi (e' :: es') e.domain.hi domain hcontig 0 (by simp) |>
        fun h => le_trans (by
          have := coverage_adjacent (e :: e' :: es') domain hcov 0 (by simp)
          simp at this
          calc e.domain.hi = e'.domain.lo := this
            _ ≤ e'.domain.hi := e'.domain.le) h

/-- Helper: every entry's hi ≤ domain.hi when coverage holds -/
private theorem coverage_entry_hi_le_domain_hi (entries : List PartitionEntry)
    (domain : IntervalRat) (hcov : checkCoverage entries domain = true)
    (i : ℕ) (hi : i < entries.length) :
    (entries[i]'hi).domain.hi ≤ domain.hi := by
  cases entries with
  | nil => simp at hi
  | cons e es =>
    have hcontig := coverage_tail_contiguous e es domain hcov
    cases i with
    | zero =>
      simp only [List.getElem_cons_zero]
      exact coverage_first_hi_le (e :: es) domain hcov (by simp)
    | succ j =>
      simp only [List.getElem_cons_succ]
      exact contiguous_entry_le_domain_hi es e.domain.hi domain hcontig j (by simp at hi; omega)

/-- Helper: every entry's lo ≥ domain.lo when coverage holds -/
private theorem coverage_entry_lo_ge_domain_lo (entries : List PartitionEntry)
    (domain : IntervalRat) (hcov : checkCoverage entries domain = true)
    (i : ℕ) (hi : i < entries.length) :
    domain.lo ≤ (entries[i]'hi).domain.lo := by
  cases i with
  | zero =>
    cases entries with
    | nil => simp at hi
    | cons e es =>
      simp only [List.getElem_cons_zero]
      have hfirst := coverage_first_starts (e :: es) domain hcov (by simp)
      simp only [List.head_cons] at hfirst
      exact le_of_eq hfirst.symm
  | succ j =>
    cases entries with
    | nil => simp at hi
    | cons e es =>
      simp only [List.getElem_cons_succ]
      have hfirst := coverage_first_starts (e :: es) domain hcov (by simp)
      simp only [List.head_cons] at hfirst
      -- entry[j+1].lo = entry[j].hi by adjacency, and entry[j].hi ≥ domain.lo
      -- by induction on j
      have hadj : ∀ k (hk : k + 1 < (e :: es).length),
          (e :: es)[k].domain.hi = (e :: es)[k + 1].domain.lo :=
        coverage_adjacent (e :: es) domain hcov
      have hentry_lo : domain.lo ≤ e.domain.lo := le_of_eq hfirst.symm
      -- Show by induction: domain.lo ≤ entry[k].lo for all k
      have hrec : ∀ k (hk : k < es.length), domain.lo ≤ es[k].domain.lo := by
        intro k hk
        induction k with
        | zero =>
          cases es with
          | nil => simp at hk
          | cons e' es' =>
            simp only [List.getElem_cons_zero]
            have h01 := hadj 0 (by simp)
            simp only [List.getElem_cons_zero, List.getElem_cons_succ] at h01
            calc domain.lo ≤ e.domain.lo := hentry_lo
              _ ≤ e.domain.hi := e.domain.le
              _ = e'.domain.lo := h01
        | succ m ih =>
          have hm : m < es.length := by omega
          have hm1 : m + 1 < (e :: es).length := by simp; omega
          have hk1 := hadj (m + 1) (by simp; omega)
          simp only [List.getElem_cons_succ] at hk1
          calc domain.lo ≤ es[m].domain.lo := ih hm
            _ ≤ es[m].domain.hi := es[m].domain.le
            _ = es[m + 1].domain.lo := hk1
      exact hrec j (by simp at hi; omega)

/-- Helper: checkContiguous only depends on domain.hi -/
private theorem checkContiguous_depends_only_on_hi (es : List PartitionEntry)
    (dom1 dom2 : IntervalRat) (lastHi : ℚ)
    (hhi : dom1.hi = dom2.hi) :
    checkCoverage.checkContiguous dom1 es lastHi = checkCoverage.checkContiguous dom2 es lastHi := by
  induction es generalizing lastHi with
  | nil => simp only [checkCoverage.checkContiguous, hhi]
  | cons e es' ih =>
    simp only [checkCoverage.checkContiguous]
    by_cases h : e.domain.lo = lastHi
    · simp only [h, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte]
      exact ih e.domain.hi
    · simp only [ne_eq, h, not_false_eq_true, decide_true, ↓reduceIte]

/-- Helper: checkContiguous implies checkCoverage on tail with adjusted domain -/
private theorem contiguous_to_coverage_tail (e' : PartitionEntry) (es' : List PartitionEntry)
    (lastHi : ℚ) (domain : IntervalRat)
    (hcheck : checkCoverage.checkContiguous domain (e' :: es') lastHi = true)
    (hlastHi_eq : e'.domain.lo = lastHi)
    (hle : lastHi ≤ domain.hi) :
    checkCoverage (e' :: es') ⟨lastHi, domain.hi, hle⟩ = true := by
  simp only [checkCoverage]
  simp only [hlastHi_eq, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte]
  simp only [checkCoverage.checkContiguous] at hcheck
  by_cases h : e'.domain.lo = lastHi
  · simp only [h, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte] at hcheck
    -- checkContiguous only depends on domain.hi, which is the same
    rw [checkContiguous_depends_only_on_hi es' ⟨lastHi, domain.hi, hle⟩ domain e'.domain.hi rfl]
    exact hcheck
  · exact absurd hlastHi_eq h

theorem coverage_integral_sum (f : ℝ → ℝ) (entries : List PartitionEntry)
    (domain : IntervalRat) (hcov : checkCoverage entries domain = true)
    (hInt : IntervalIntegrable f MeasureTheory.volume domain.lo domain.hi) :
    ∫ x in (domain.lo : ℝ)..(domain.hi : ℝ), f x =
      (entries.map (fun e => ∫ x in (e.domain.lo : ℝ)..(e.domain.hi : ℝ), f x)).sum := by
  have hne : entries ≠ [] := coverage_nonempty entries domain hcov
  induction entries generalizing domain with
  | nil => exact absurd rfl hne
  | cons e es ih =>
    simp only [List.map_cons, List.sum_cons]
    cases es with
    | nil =>
      -- Single entry: e covers the whole domain
      simp only [List.map_nil, List.sum_nil, add_zero]
      have hfirst := coverage_first_starts [e] domain hcov (by simp)
      have hlast := coverage_last_ends [e] domain hcov (by simp)
      simp only [List.head_cons, List.getLast_singleton] at hfirst hlast
      rw [hfirst, hlast]
    | cons e' es' =>
      -- Multiple entries: use integral additivity
      have hfirst := coverage_first_starts (e :: e' :: es') domain hcov (by simp)
      simp only [List.head_cons] at hfirst
      have hadj := coverage_adjacent (e :: e' :: es') domain hcov 0 (by simp)
      simp only [List.getElem_cons_zero, List.getElem_cons_succ] at hadj
      -- Key: split integral at e.domain.hi
      have hhi_le : e.domain.hi ≤ domain.hi := coverage_first_hi_le (e :: e' :: es') domain hcov (by simp)
      have hlo_le : domain.lo ≤ e.domain.hi := by
        have h := e.domain.le; rw [hfirst] at h; exact h
      -- Build tail domain
      let tailDomain : IntervalRat := ⟨e.domain.hi, domain.hi, hhi_le⟩
      -- Show tail has coverage
      have hcontig := coverage_tail_contiguous e (e' :: es') domain hcov
      have htail_cov : checkCoverage (e' :: es') tailDomain = true :=
        contiguous_to_coverage_tail e' es' e.domain.hi domain hcontig hadj.symm hhi_le
      -- Integrability on subintervals
      have hInt_e : IntervalIntegrable f MeasureTheory.volume e.domain.lo e.domain.hi := by
        apply integrable_subinterval f domain.lo domain.hi e.domain.lo e.domain.hi
          (Rat.cast_le.mpr domain.le) (Rat.cast_le.mpr e.domain.le)
        · exact Rat.cast_le.mpr (le_of_eq hfirst.symm)
        · exact Rat.cast_le.mpr hhi_le
        · exact hInt
      have hInt_tail : IntervalIntegrable f MeasureTheory.volume tailDomain.lo tailDomain.hi := by
        apply integrable_subinterval f domain.lo domain.hi tailDomain.lo tailDomain.hi
          (Rat.cast_le.mpr domain.le) (Rat.cast_le.mpr tailDomain.le)
        · exact Rat.cast_le.mpr hlo_le
        · exact le_refl _
        · exact hInt
      -- Use IH on tail (es = e' :: es')
      -- IH signature: domain → coverage → integrability → nonempty → result
      have hne_tail : (e' :: es') ≠ [] := by simp
      have ih_result := ih tailDomain htail_cov hInt_tail hne_tail
      -- Use integral additivity: ∫[a,b] + ∫[b,c] = ∫[a,c]
      have h_add := intervalIntegral.integral_add_adjacent_intervals hInt_e hInt_tail
      -- tailDomain = ⟨e.domain.hi, domain.hi, _⟩, so tailDomain.hi = domain.hi
      have htail_hi_eq : (tailDomain.hi : ℝ) = (domain.hi : ℝ) := rfl
      -- Substitute in h_add and ih_result
      simp only [htail_hi_eq] at h_add ih_result
      -- Goal: ∫[domain.lo, domain.hi] = ∫[e.lo, e.hi] + sum(rest)
      -- hfirst: e.domain.lo = domain.lo (in ℚ)
      -- h_add: ∫[e.lo, e.hi] + ∫[e.hi, domain.hi] = ∫[e.lo, domain.hi]
      -- ih_result: ∫[e.hi, domain.hi] = sum(rest)
      have hfirst_cast : (e.domain.lo : ℝ) = (domain.lo : ℝ) := by exact_mod_cast hfirst
      rw [← hfirst_cast]
      -- Goal: ∫[e.lo, domain.hi] = ∫[e.lo, e.hi] + sum(rest)
      rw [← h_add, ih_result]

/-- **Main Soundness Theorem for Certificate-Based Integration**

If verifyCertificate returns true, the actual integral is in the target interval.
This is the key theorem that makes certificate-based verification sound.

The proof proceeds as follows:
1. Extract the three conditions from verifyCertificate = true
2. Use coverage_integral_sum to write total integral as sum of partition integrals
3. Use partition_bound_correct to show each partition integral ∈ its bound
4. Use sum_mem_sum_intervals to show the sum of integrals ∈ sum of bounds
5. Use checkSumInTarget to show sum of bounds ⊆ target
-/
theorem verify_certificate_correct (e : Expr) (hsupp : ExprSupportedWithInv e)
    (cert : IntegralCertificate) (target : IntervalRat)
    (hverify : verifyCertificate e cert target = true)
    (hInt : IntervalIntegrable (fun x => Expr.eval (fun _ => x) e)
      MeasureTheory.volume (cert.domain.lo : ℝ) (cert.domain.hi : ℝ)) :
    ∫ x in (cert.domain.lo : ℝ)..(cert.domain.hi : ℝ),
      Expr.eval (fun _ => x) e ∈ target := by
  -- Unpack verifyCertificate into its three conditions
  simp only [verifyCertificate, Bool.and_eq_true] at hverify
  obtain ⟨⟨hcov, hbounds⟩, hsum⟩ := hverify
  -- Extract checkAllBounds
  simp only [checkAllBounds, List.all_eq_true] at hbounds
  -- Extract checkSumInTarget
  simp only [checkSumInTarget, decide_eq_true_eq] at hsum
  -- Step 1: Rewrite integral as sum of partition integrals
  have h_sum_eq := coverage_integral_sum (fun x => Expr.eval (fun _ => x) e)
    cert.partitions cert.domain hcov hInt
  rw [h_sum_eq]
  -- Define the values and bounds lists
  set integrals := cert.partitions.map fun entry =>
    ∫ x in (entry.domain.lo : ℝ)..(entry.domain.hi : ℝ), Expr.eval (fun _ => x) e with h_integrals
  set bounds := cert.partitions.map fun entry => entry.bound with h_bounds
  -- Step 2: Each partition integral is in its bound
  have hlen : integrals.length = bounds.length := by
    simp only [h_integrals, h_bounds, List.length_map]
  have hmem : ∀ i (hi : i < integrals.length),
      integrals[i] ∈ (bounds[i]'(hlen ▸ hi)) := by
    intro i hi
    simp only [h_integrals, h_bounds, List.getElem_map]
    have hi' : i < cert.partitions.length := by
      simp only [h_integrals, List.length_map] at hi; exact hi
    let entry := cert.partitions[i]'hi'
    have hcheck := hbounds entry (List.getElem_mem hi')
    have hInt_i : IntervalIntegrable (fun x => Expr.eval (fun _ => x) e)
        MeasureTheory.volume entry.domain.lo entry.domain.hi := by
      -- Integrability on subinterval - entry ⊆ domain by coverage
      have hlo := coverage_entry_lo_ge_domain_lo cert.partitions cert.domain hcov i hi'
      have hhi := coverage_entry_hi_le_domain_hi cert.partitions cert.domain hcov i hi'
      apply integrable_subinterval _ cert.domain.lo cert.domain.hi entry.domain.lo entry.domain.hi
        (Rat.cast_le.mpr cert.domain.le) (Rat.cast_le.mpr entry.domain.le)
        (Rat.cast_le.mpr hlo) (Rat.cast_le.mpr hhi) hInt
    exact partition_bound_correct e hsupp entry hcheck hInt_i
  -- Step 3: Apply sum_mem_sum_intervals
  have h_in_sum := sum_mem_sum_intervals integrals bounds hlen hmem
  -- The sumBounds equals foldl add zero bounds
  have h_sumBounds_eq : sumBounds cert.partitions =
      bounds.foldl (fun acc I => IntervalRat.add acc I) ⟨0, 0, le_refl 0⟩ := by
    simp only [sumBounds, h_bounds]
    -- Use foldl_map: foldl f init (map g l) = foldl (fun acc x => f acc (g x)) init l
    rw [List.foldl_map]
  -- Membership in sumBounds implies membership in target
  have h_in_bounds : integrals.sum ∈ sumBounds cert.partitions := by
    rw [h_sumBounds_eq]
    exact h_in_sum
  simp only [IntervalRat.mem_def] at h_in_bounds ⊢
  constructor
  · calc (target.lo : ℝ) ≤ (sumBounds cert.partitions).lo := by exact_mod_cast hsum.1
      _ ≤ integrals.sum := h_in_bounds.1
  · calc integrals.sum ≤ (sumBounds cert.partitions).hi := h_in_bounds.2
      _ ≤ target.hi := by exact_mod_cast hsum.2

/-! ### Certificate Generation

Generate certificates from the adaptive integration algorithm.
This captures the result of the search for later verification.
-/

/-- Build a certificate entry from a successful interval evaluation -/
def mkPartitionEntry (e : Expr) (domain : IntervalRat) : Option PartitionEntry :=
  match evalInterval?1 e domain with
  | none => none
  | some computed =>
    let width := domain.hi - domain.lo
    -- Use min/max to avoid ordering issues with potentially negative values
    let blo := min (computed.lo * width) (computed.hi * width)
    let bhi := max (computed.lo * width) (computed.hi * width)
    some {
      domain := domain
      bound := ⟨blo, bhi, le_max_of_le_left (min_le_left _ _)⟩
    }

/-- Helper: midpoint is between lo and hi -/
private theorem midpoint_le_hi (lo hi : ℚ) (h : lo ≤ hi) : (lo + hi) / 2 ≤ hi := by
  linarith

private theorem lo_le_midpoint (lo hi : ℚ) (h : lo ≤ hi) : lo ≤ (lo + hi) / 2 := by
  linarith

/-- Recursively build certificate from adaptive search -/
partial def buildCertificateAux (e : Expr) (domain : IntervalRat) (tol : ℚ)
    (maxDepth : ℕ) : Option (List PartitionEntry) :=
  if maxDepth = 0 then
    -- Base case: try to build a single entry
    match mkPartitionEntry e domain with
    | some entry => some [entry]
    | none => none
  else
    -- Try single partition first
    match mkPartitionEntry e domain with
    | none => none  -- Domain invalid
    | some entry =>
      let width := entry.bound.hi - entry.bound.lo
      if width ≤ tol then
        some [entry]
      else
        -- Split and recurse
        let mid := (domain.lo + domain.hi) / 2
        let left : IntervalRat := ⟨domain.lo, mid, lo_le_midpoint domain.lo domain.hi domain.le⟩
        let right : IntervalRat := ⟨mid, domain.hi, midpoint_le_hi domain.lo domain.hi domain.le⟩
        match buildCertificateAux e left (tol / 2) (maxDepth - 1),
              buildCertificateAux e right (tol / 2) (maxDepth - 1) with
        | some leftEntries, some rightEntries => some (leftEntries ++ rightEntries)
        | _, _ => none

/-- Build an integration certificate using adaptive partitioning -/
def buildCertificate (e : Expr) (domain : IntervalRat) (tol : ℚ)
    (maxDepth : ℕ := 20) (name : String := "integral") : Option IntegralCertificate :=
  match buildCertificateAux e domain tol maxDepth with
  | some entries => some {
      expr_id := name
      domain := domain
      partitions := entries
    }
  | none => none

/-! ### Golden Theorems for Certificate-Based Integration -/

/-- Check if an integral lower bound holds via certificate verification -/
def checkIntegralCertLowerBound (e : Expr) (cert : IntegralCertificate) (c : ℚ) : Bool :=
  checkCoverage cert.partitions cert.domain &&
  checkAllBounds e cert.partitions &&
  decide (c ≤ (sumBounds cert.partitions).lo)

/-- Check if an integral upper bound holds via certificate verification -/
def checkIntegralCertUpperBound (e : Expr) (cert : IntegralCertificate) (c : ℚ) : Bool :=
  checkCoverage cert.partitions cert.domain &&
  checkAllBounds e cert.partitions &&
  decide ((sumBounds cert.partitions).hi ≤ c)

/-- **Golden Theorem**: Certificate-verified integral lower bound -/
theorem verify_integral_cert_lower_bound (e : Expr) (hsupp : ExprSupportedWithInv e)
    (cert : IntegralCertificate) (c : ℚ)
    (hcheck : checkIntegralCertLowerBound e cert c = true)
    (hInt : IntervalIntegrable (fun x => Expr.eval (fun _ => x) e)
      MeasureTheory.volume (cert.domain.lo : ℝ) (cert.domain.hi : ℝ)) :
    c ≤ ∫ x in (cert.domain.lo : ℝ)..(cert.domain.hi : ℝ), Expr.eval (fun _ => x) e := by
  simp only [checkIntegralCertLowerBound, Bool.and_eq_true, decide_eq_true_eq] at hcheck
  obtain ⟨⟨hcov, hbounds⟩, hlo⟩ := hcheck
  -- Build target interval [c, ∞) represented as [c, sumBounds.hi]
  let target : IntervalRat := ⟨c, (sumBounds cert.partitions).hi, by
    calc c ≤ (sumBounds cert.partitions).lo := hlo
      _ ≤ (sumBounds cert.partitions).hi := (sumBounds cert.partitions).le⟩
  -- checkSumInTarget target holds
  have hsum : checkSumInTarget cert.partitions target = true := by
    simp only [checkSumInTarget, decide_eq_true_eq]
    exact ⟨hlo, le_refl _⟩
  have hverify : verifyCertificate e cert target = true := by
    simp only [verifyCertificate, Bool.and_eq_true]
    exact ⟨⟨hcov, hbounds⟩, hsum⟩
  have hmem := verify_certificate_correct e hsupp cert target hverify hInt
  simp only [IntervalRat.mem_def] at hmem
  exact_mod_cast hmem.1

/-- **Golden Theorem**: Certificate-verified integral upper bound -/
theorem verify_integral_cert_upper_bound (e : Expr) (hsupp : ExprSupportedWithInv e)
    (cert : IntegralCertificate) (c : ℚ)
    (hcheck : checkIntegralCertUpperBound e cert c = true)
    (hInt : IntervalIntegrable (fun x => Expr.eval (fun _ => x) e)
      MeasureTheory.volume (cert.domain.lo : ℝ) (cert.domain.hi : ℝ)) :
    ∫ x in (cert.domain.lo : ℝ)..(cert.domain.hi : ℝ), Expr.eval (fun _ => x) e ≤ c := by
  simp only [checkIntegralCertUpperBound, Bool.and_eq_true, decide_eq_true_eq] at hcheck
  obtain ⟨⟨hcov, hbounds⟩, hhi⟩ := hcheck
  -- Build target interval (-∞, c] represented as [sumBounds.lo, c]
  let target : IntervalRat := ⟨(sumBounds cert.partitions).lo, c, by
    calc (sumBounds cert.partitions).lo ≤ (sumBounds cert.partitions).hi := (sumBounds cert.partitions).le
      _ ≤ c := hhi⟩
  -- checkSumInTarget target holds
  have hsum : checkSumInTarget cert.partitions target = true := by
    simp only [checkSumInTarget, decide_eq_true_eq]
    exact ⟨le_refl _, hhi⟩
  have hverify : verifyCertificate e cert target = true := by
    simp only [verifyCertificate, Bool.and_eq_true]
    exact ⟨⟨hcov, hbounds⟩, hsum⟩
  have hmem := verify_certificate_correct e hsupp cert target hverify hInt
  simp only [IntervalRat.mem_def] at hmem
  exact_mod_cast hmem.2

end LeanCert.Validity.CertificateIntegration
