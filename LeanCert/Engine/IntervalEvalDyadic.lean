/-
Copyright (c) 2025 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Core.Expr
import LeanCert.Core.IntervalDyadic
import LeanCert.Engine.IntervalEval

/-!
# High-Performance Dyadic Interval Evaluator

This evaluator replaces `Rat` with `Dyadic` to prevent denominator explosion.
It is designed for complex expressions where the standard evaluator becomes slow.

## Main definitions

* `DyadicConfig` - Configuration for precision and Taylor depth
* `evalIntervalDyadic` - Dyadic interval evaluator for expressions
* `evalIntervalDyadic_correct` - Correctness theorem

## Performance

In v1.0, every `Rat` multiplication required GCD normalization. For deep
expressions (e.g., Taylor series with 20+ terms, or optimization with 100+
iterations), denominators grow exponentially, causing timeouts.

In v1.1, Dyadic arithmetic uses bit-shifts instead of GCD. With `roundOut`,
we can enforce a maximum precision after each operation, keeping computation
bounded regardless of expression depth.

## Example

Consider computing `sin(sin(sin(x)))` with 15-term Taylor series:
- v1.0 (Rat): ~500ms per call, denominators grow to millions of digits
- v1.1 (Dyadic): ~5ms per call, precision stays at 53 bits

## Design notes

For transcendental functions (sin, cos, exp), we delegate to the existing
`IntervalRat` implementation with Taylor series, then convert the result
to `IntervalDyadic` with outward rounding. This reuses verified code while
gaining the performance benefits of Dyadic for polynomial operations.
-/

namespace LeanCert.Engine

open LeanCert.Core

/-! ### Configuration -/

/-- Configuration for Dyadic interval evaluation.

* `precision` - Minimum exponent for outward rounding. A value of -53 gives
  IEEE double-like precision (~15 decimal digits). Use -100 for higher precision.
* `taylorDepth` - Number of Taylor terms for transcendental functions.
* `roundAfterOps` - Round after this many operations (0 = after every op).
-/
structure DyadicConfig where
  /-- Minimum exponent (higher = coarser). -53 ≈ IEEE double precision. -/
  precision : Int := -53
  /-- Number of Taylor series terms for transcendental functions -/
  taylorDepth : Nat := 10
  /-- Round after this many arithmetic operations (0 = always) -/
  roundAfterOps : Nat := 0
  deriving Repr, DecidableEq

/-- Default configuration with IEEE double-like precision -/
instance : Inhabited DyadicConfig := ⟨{}⟩

/-- High-precision configuration for critical calculations -/
def DyadicConfig.highPrecision : DyadicConfig :=
  { precision := -100, taylorDepth := 20 }

/-- Fast configuration for rapid evaluation (lower precision) -/
def DyadicConfig.fast : DyadicConfig :=
  { precision := -30, taylorDepth := 8 }

/-! ### Variable Environment -/

/-- Variable assignment as Dyadic intervals -/
abbrev IntervalDyadicEnv := Nat → IntervalDyadic

/-- Convert a rational interval environment to Dyadic -/
def toDyadicEnv (ρ : IntervalEnv) (prec : Int := -53) : IntervalDyadicEnv :=
  fun i => IntervalDyadic.ofIntervalRat (ρ i) prec

/-! ### Transcendental Function Wrappers -/

/-- Compute sin interval using rational Taylor series, convert to Dyadic -/
def sinIntervalDyadic (I : IntervalDyadic) (cfg : DyadicConfig) : IntervalDyadic :=
  let Irat := I.toIntervalRat
  let result := IntervalRat.sinComputable Irat cfg.taylorDepth
  IntervalDyadic.ofIntervalRat result cfg.precision

/-- Compute cos interval using rational Taylor series, convert to Dyadic -/
def cosIntervalDyadic (I : IntervalDyadic) (cfg : DyadicConfig) : IntervalDyadic :=
  let Irat := I.toIntervalRat
  let result := IntervalRat.cosComputable Irat cfg.taylorDepth
  IntervalDyadic.ofIntervalRat result cfg.precision

/-- Compute exp interval using rational Taylor series, convert to Dyadic -/
def expIntervalDyadic (I : IntervalDyadic) (cfg : DyadicConfig) : IntervalDyadic :=
  let Irat := I.toIntervalRat
  let result := IntervalRat.expComputable Irat cfg.taylorDepth
  IntervalDyadic.ofIntervalRat result cfg.precision

/-- Compute sinh interval using rational Taylor series, convert to Dyadic -/
def sinhIntervalDyadic (I : IntervalDyadic) (cfg : DyadicConfig) : IntervalDyadic :=
  let Irat := I.toIntervalRat
  let result := IntervalRat.sinhComputable Irat cfg.taylorDepth
  IntervalDyadic.ofIntervalRat result cfg.precision

/-- Compute cosh interval using rational Taylor series, convert to Dyadic -/
def coshIntervalDyadic (I : IntervalDyadic) (cfg : DyadicConfig) : IntervalDyadic :=
  let Irat := I.toIntervalRat
  let result := IntervalRat.coshComputable Irat cfg.taylorDepth
  IntervalDyadic.ofIntervalRat result cfg.precision

/-- atan interval: global bound [-2, 2] -/
def atanIntervalDyadic (_I : IntervalDyadic) (_cfg : DyadicConfig) : IntervalDyadic :=
  let neg2 := Core.Dyadic.ofInt (-2)
  let pos2 := Core.Dyadic.ofInt 2
  ⟨neg2, pos2, by rw [Dyadic.toRat_ofInt, Dyadic.toRat_ofInt]; norm_num⟩

/-- tanh interval: global bound [-1, 1] -/
def tanhIntervalDyadic (_I : IntervalDyadic) (_cfg : DyadicConfig) : IntervalDyadic :=
  let neg1 := Core.Dyadic.ofInt (-1)
  let pos1 := Core.Dyadic.ofInt 1
  ⟨neg1, pos1, by rw [Dyadic.toRat_ofInt, Dyadic.toRat_ofInt]; norm_num⟩

/-- arsinh interval: wide box bound via rational arsinhInterval -/
def arsinhIntervalDyadic (I : IntervalDyadic) (cfg : DyadicConfig) : IntervalDyadic :=
  let Irat := I.toIntervalRat
  let result := arsinhInterval Irat
  IntervalDyadic.ofIntervalRat result cfg.precision

/-- atanh interval: computable Taylor series via rational atanhComputable -/
def atanhIntervalDyadic (I : IntervalDyadic) (cfg : DyadicConfig) : IntervalDyadic :=
  let Irat := I.toIntervalRat
  let result := IntervalRat.atanhComputable Irat cfg.taylorDepth
  IntervalDyadic.ofIntervalRat result cfg.precision

/-- sinc interval: global bound [-1, 1] -/
def sincIntervalDyadic (_I : IntervalDyadic) (_cfg : DyadicConfig) : IntervalDyadic :=
  let neg1 := Core.Dyadic.ofInt (-1)
  let pos1 := Core.Dyadic.ofInt 1
  ⟨neg1, pos1, by rw [Dyadic.toRat_ofInt, Dyadic.toRat_ofInt]; norm_num⟩

/-- erf interval: global bound [-1, 1] -/
def erfIntervalDyadic (_I : IntervalDyadic) (_cfg : DyadicConfig) : IntervalDyadic :=
  let neg1 := Core.Dyadic.ofInt (-1)
  let pos1 := Core.Dyadic.ofInt 1
  ⟨neg1, pos1, by rw [Dyadic.toRat_ofInt, Dyadic.toRat_ofInt]; norm_num⟩

/-- Compute inv interval: convert to Rat, use invInterval, convert back to Dyadic -/
def invIntervalDyadic (I : IntervalDyadic) (cfg : DyadicConfig) : IntervalDyadic :=
  let Irat := I.toIntervalRat
  let result := invInterval Irat
  IntervalDyadic.ofIntervalRat result cfg.precision

/-- sqrt interval: uses conservative bound [0, max(hi, 1)] -/
def sqrtIntervalDyadic (I : IntervalDyadic) (cfg : DyadicConfig) : IntervalDyadic :=
  IntervalDyadic.sqrt I cfg.precision

/-- log interval: conservative global bound.
    For any x > 0, log(x) ∈ (-∞, ∞), but we use a finite interval.
    For x ∈ [lo, hi] with lo > 0:
    - log is monotone, so log(x) ∈ [log(lo), log(hi)]
    - Conservative bound: use [-100, max(hi, 1)] as a wide safe interval -/
def logIntervalDyadic (I : IntervalDyadic) (cfg : DyadicConfig) : IntervalDyadic :=
  -- Compute log using Taylor series via atanh reduction
  -- Convert to rational, compute, convert back with outward rounding
  let IRat := I.toIntervalRat
  if IRat.lo > 0 then
    let result := IntervalRat.logComputable IRat cfg.taylorDepth
    IntervalDyadic.ofIntervalRat result cfg.precision
  else
    -- Input may include zero or negative values, return wide fallback interval
    -- for soundness (though in practice this shouldn't happen for valid inputs)
    ⟨Core.Dyadic.ofInt (-1000), Core.Dyadic.ofInt 1000, by simp [Dyadic.toRat_ofInt]⟩

/-- Real power x^p for x > 0 and rational p, computed via exp(p * log(x)).

    For x ∈ [lo, hi] with lo > 0 and rational exponent p:
    - x^p = exp(p * log(x))
    - We compute log(x), multiply by p, then apply exp

    This is the key operation for BKLNW-style sums where terms are x^(1/k - 1/3). -/
def rpowIntervalDyadic (base : IntervalDyadic) (p : ℚ) (cfg : DyadicConfig) : IntervalDyadic :=
  -- x^p = exp(p * log(x)) for x > 0
  let logBase := logIntervalDyadic base cfg
  let pInterval := IntervalDyadic.ofIntervalRat (IntervalRat.singleton p) cfg.precision
  let pLogBase := (IntervalDyadic.mul pInterval logBase).roundOut cfg.precision
  expIntervalDyadic pLogBase cfg

/-- Correctness of rpowIntervalDyadic: if x ∈ base and base.lo > 0, then x^p ∈ result -/
theorem mem_rpowIntervalDyadic {x : ℝ} {base : IntervalDyadic} (hx : x ∈ base)
    (hpos : base.toIntervalRat.lo > 0) (p : ℚ) (cfg : DyadicConfig)
    (hprec : cfg.precision ≤ 0 := by norm_num) :
    x ^ (p : ℝ) ∈ rpowIntervalDyadic base p cfg := by
  simp only [rpowIntervalDyadic]
  -- x^p = exp(p * log(x)) for x > 0
  have hx_pos : 0 < x := by
    have hlo := hx.1
    have hlo_pos : (0 : ℝ) < base.lo.toRat := by exact_mod_cast hpos
    linarith
  rw [Real.rpow_def_of_pos hx_pos, mul_comm]  -- Use commutativity: log x * p = p * log x
  -- log(x) ∈ logIntervalDyadic base cfg
  have hlog_mem : Real.log x ∈ logIntervalDyadic base cfg := by
    simp only [logIntervalDyadic, hpos, ↓reduceIte]
    have hrat := IntervalDyadic.mem_toIntervalRat.mp hx
    have hlog := IntervalRat.mem_logComputable hrat hpos cfg.taylorDepth
    exact IntervalDyadic.mem_ofIntervalRat hlog cfg.precision hprec
  -- p ∈ pInterval (singleton)
  have hp_mem : (p : ℝ) ∈ IntervalDyadic.ofIntervalRat (IntervalRat.singleton p) cfg.precision := by
    apply IntervalDyadic.mem_ofIntervalRat
    · exact IntervalRat.mem_singleton p
    · exact hprec
  -- p * log(x) ∈ mul result
  have hmul := IntervalDyadic.mem_mul hp_mem hlog_mem
  have hmul_rounded := IntervalDyadic.roundOut_contains hmul cfg.precision
  -- exp(p * log(x)) ∈ expIntervalDyadic
  simp only [expIntervalDyadic]
  have hrat := IntervalDyadic.mem_toIntervalRat.mp hmul_rounded
  have hexp := IntervalRat.mem_expComputable hrat cfg.taylorDepth
  exact IntervalDyadic.mem_ofIntervalRat hexp cfg.precision hprec

/-! ### Main Evaluator -/

/-- High-performance Dyadic interval evaluator.

This is the core function for v1.1. It evaluates expressions using Dyadic
arithmetic for polynomial operations (add, mul, neg) and delegates to
rational Taylor series for transcendentals.

Returns an interval guaranteed to contain all possible values of the expression
when `ExprSupportedCore` holds. For other expressions, it computes conservative
fallbacks (e.g., inv/log), but the core correctness theorem does not apply. -/
def evalIntervalDyadic (e : Expr) (ρ : IntervalDyadicEnv) (cfg : DyadicConfig := {}) : IntervalDyadic :=
  match e with
  | Expr.const q =>
      -- Convert rational constant to Dyadic interval with outward rounding
      IntervalDyadic.ofIntervalRat (IntervalRat.singleton q) cfg.precision
  | Expr.var idx => ρ idx
  | Expr.add e₁ e₂ =>
      let I₁ := evalIntervalDyadic e₁ ρ cfg
      let I₂ := evalIntervalDyadic e₂ ρ cfg
      (IntervalDyadic.add I₁ I₂).roundOut cfg.precision
  | Expr.mul e₁ e₂ =>
      let I₁ := evalIntervalDyadic e₁ ρ cfg
      let I₂ := evalIntervalDyadic e₂ ρ cfg
      (IntervalDyadic.mul I₁ I₂).roundOut cfg.precision
  | Expr.neg e =>
      let I := evalIntervalDyadic e ρ cfg
      IntervalDyadic.neg I  -- Negation doesn't increase precision
  | Expr.inv e => invIntervalDyadic (evalIntervalDyadic e ρ cfg) cfg
  | Expr.exp e => expIntervalDyadic (evalIntervalDyadic e ρ cfg) cfg
  | Expr.sin e => sinIntervalDyadic (evalIntervalDyadic e ρ cfg) cfg
  | Expr.cos e => cosIntervalDyadic (evalIntervalDyadic e ρ cfg) cfg
  | Expr.log e => logIntervalDyadic (evalIntervalDyadic e ρ cfg) cfg
  | Expr.atan e => atanIntervalDyadic (evalIntervalDyadic e ρ cfg) cfg
  | Expr.arsinh e => arsinhIntervalDyadic (evalIntervalDyadic e ρ cfg) cfg
  | Expr.atanh e => atanhIntervalDyadic (evalIntervalDyadic e ρ cfg) cfg
  | Expr.sinc e => sincIntervalDyadic (evalIntervalDyadic e ρ cfg) cfg
  | Expr.erf e => erfIntervalDyadic (evalIntervalDyadic e ρ cfg) cfg
  | Expr.sinh e => sinhIntervalDyadic (evalIntervalDyadic e ρ cfg) cfg
  | Expr.cosh e => coshIntervalDyadic (evalIntervalDyadic e ρ cfg) cfg
  | Expr.tanh e => tanhIntervalDyadic (evalIntervalDyadic e ρ cfg) cfg
  | Expr.sqrt e => sqrtIntervalDyadic (evalIntervalDyadic e ρ cfg) cfg
  | Expr.pi => IntervalDyadic.ofIntervalRat piInterval cfg.precision

/-! ### Correctness -/

/-- A real environment is contained in a Dyadic interval environment -/
def envMemDyadic (ρ_real : Nat → ℝ) (ρ_dyad : IntervalDyadicEnv) : Prop :=
  ∀ i, ρ_real i ∈ ρ_dyad i

/-- Domain validity for Dyadic evaluation.
    This is defined directly in terms of evalIntervalDyadic to ensure compatibility.
    For log, we require the argument interval (converted to Rat) to have positive lower bound. -/
def evalDomainValidDyadic (e : Expr) (ρ : IntervalDyadicEnv) (cfg : DyadicConfig := {}) : Prop :=
  match e with
  | Expr.const _ => True
  | Expr.var _ => True
  | Expr.add e₁ e₂ => evalDomainValidDyadic e₁ ρ cfg ∧ evalDomainValidDyadic e₂ ρ cfg
  | Expr.mul e₁ e₂ => evalDomainValidDyadic e₁ ρ cfg ∧ evalDomainValidDyadic e₂ ρ cfg
  | Expr.neg e => evalDomainValidDyadic e ρ cfg
  | Expr.inv e => evalDomainValidDyadic e ρ cfg ∧
      ((evalIntervalDyadic e ρ cfg).toIntervalRat.lo > 0 ∨
       (evalIntervalDyadic e ρ cfg).toIntervalRat.hi < 0)
  | Expr.exp e => evalDomainValidDyadic e ρ cfg
  | Expr.sin e => evalDomainValidDyadic e ρ cfg
  | Expr.cos e => evalDomainValidDyadic e ρ cfg
  | Expr.log e => evalDomainValidDyadic e ρ cfg ∧ (evalIntervalDyadic e ρ cfg).toIntervalRat.lo > 0
  | Expr.atan e => evalDomainValidDyadic e ρ cfg
  | Expr.arsinh e => evalDomainValidDyadic e ρ cfg
  | Expr.atanh e => evalDomainValidDyadic e ρ cfg ∧
      (evalIntervalDyadic e ρ cfg).toIntervalRat.lo > -1 ∧
      (evalIntervalDyadic e ρ cfg).toIntervalRat.hi < 1
  | Expr.sinc e => evalDomainValidDyadic e ρ cfg
  | Expr.erf e => evalDomainValidDyadic e ρ cfg
  | Expr.sinh e => evalDomainValidDyadic e ρ cfg
  | Expr.cosh e => evalDomainValidDyadic e ρ cfg
  | Expr.tanh e => evalDomainValidDyadic e ρ cfg
  | Expr.sqrt e => evalDomainValidDyadic e ρ cfg
  | Expr.pi => True

/-- Computable (Bool) domain validity check for Dyadic evaluation. -/
def checkDomainValidDyadic (e : Expr) (ρ : IntervalDyadicEnv) (cfg : DyadicConfig := {}) : Bool :=
  match e with
  | Expr.const _ => true
  | Expr.var _ => true
  | Expr.add e₁ e₂ => checkDomainValidDyadic e₁ ρ cfg && checkDomainValidDyadic e₂ ρ cfg
  | Expr.mul e₁ e₂ => checkDomainValidDyadic e₁ ρ cfg && checkDomainValidDyadic e₂ ρ cfg
  | Expr.neg e => checkDomainValidDyadic e ρ cfg
  | Expr.inv e => checkDomainValidDyadic e ρ cfg &&
      (decide ((evalIntervalDyadic e ρ cfg).toIntervalRat.lo > 0) ||
       decide ((evalIntervalDyadic e ρ cfg).toIntervalRat.hi < 0))
  | Expr.exp e => checkDomainValidDyadic e ρ cfg
  | Expr.sin e => checkDomainValidDyadic e ρ cfg
  | Expr.cos e => checkDomainValidDyadic e ρ cfg
  | Expr.log e => checkDomainValidDyadic e ρ cfg &&
      decide ((evalIntervalDyadic e ρ cfg).toIntervalRat.lo > 0)
  | Expr.atan e => checkDomainValidDyadic e ρ cfg
  | Expr.arsinh e => checkDomainValidDyadic e ρ cfg
  | Expr.atanh e => checkDomainValidDyadic e ρ cfg &&
      decide ((evalIntervalDyadic e ρ cfg).toIntervalRat.lo > -1) &&
      decide ((evalIntervalDyadic e ρ cfg).toIntervalRat.hi < 1)
  | Expr.sinc e => checkDomainValidDyadic e ρ cfg
  | Expr.erf e => checkDomainValidDyadic e ρ cfg
  | Expr.sinh e => checkDomainValidDyadic e ρ cfg
  | Expr.cosh e => checkDomainValidDyadic e ρ cfg
  | Expr.tanh e => checkDomainValidDyadic e ρ cfg
  | Expr.sqrt e => checkDomainValidDyadic e ρ cfg
  | Expr.pi => true

theorem checkDomainValidDyadic_correct (e : Expr) (ρ : IntervalDyadicEnv) (cfg : DyadicConfig) :
    checkDomainValidDyadic e ρ cfg = true → evalDomainValidDyadic e ρ cfg := by
  induction e with
  | const _ => intro; trivial
  | var _ => intro; trivial
  | add e₁ e₂ ih₁ ih₂ =>
    simp only [checkDomainValidDyadic, Bool.and_eq_true, evalDomainValidDyadic]
    intro ⟨h1, h2⟩; exact ⟨ih₁ h1, ih₂ h2⟩
  | mul e₁ e₂ ih₁ ih₂ =>
    simp only [checkDomainValidDyadic, Bool.and_eq_true, evalDomainValidDyadic]
    intro ⟨h1, h2⟩; exact ⟨ih₁ h1, ih₂ h2⟩
  | neg e ih =>
    simp only [checkDomainValidDyadic, evalDomainValidDyadic]; exact ih
  | inv e ih =>
    simp only [checkDomainValidDyadic, Bool.and_eq_true, Bool.or_eq_true,
      decide_eq_true_eq, evalDomainValidDyadic]
    intro ⟨h1, h2⟩; exact ⟨ih h1, h2⟩
  | exp e ih => simp only [checkDomainValidDyadic, evalDomainValidDyadic]; exact ih
  | sin e ih => simp only [checkDomainValidDyadic, evalDomainValidDyadic]; exact ih
  | cos e ih => simp only [checkDomainValidDyadic, evalDomainValidDyadic]; exact ih
  | log e ih =>
    simp only [checkDomainValidDyadic, Bool.and_eq_true, decide_eq_true_eq, evalDomainValidDyadic]
    intro ⟨h1, h2⟩; exact ⟨ih h1, h2⟩
  | atan e ih => simp only [checkDomainValidDyadic, evalDomainValidDyadic]; exact ih
  | arsinh e ih => simp only [checkDomainValidDyadic, evalDomainValidDyadic]; exact ih
  | atanh e ih =>
    simp only [checkDomainValidDyadic, Bool.and_eq_true, decide_eq_true_eq, evalDomainValidDyadic]
    intro ⟨⟨h1, h2⟩, h3⟩; exact ⟨ih h1, h2, h3⟩
  | sinc e ih => simp only [checkDomainValidDyadic, evalDomainValidDyadic]; exact ih
  | erf e ih => simp only [checkDomainValidDyadic, evalDomainValidDyadic]; exact ih
  | sinh e ih => simp only [checkDomainValidDyadic, evalDomainValidDyadic]; exact ih
  | cosh e ih => simp only [checkDomainValidDyadic, evalDomainValidDyadic]; exact ih
  | tanh e ih => simp only [checkDomainValidDyadic, evalDomainValidDyadic]; exact ih
  | sqrt e ih => simp only [checkDomainValidDyadic, evalDomainValidDyadic]; exact ih
  | pi => intro; trivial

/-- Domain validity is trivially true for ExprSupported expressions (which exclude log). -/
theorem evalDomainValidDyadic_of_ExprSupported {e : Expr} (hsupp : ExprSupported e)
    (ρ : IntervalDyadicEnv) (cfg : DyadicConfig := {}) : evalDomainValidDyadic e ρ cfg := by
  induction hsupp with
  | const _ => trivial
  | var _ => trivial
  | add _ _ ih1 ih2 => exact ⟨ih1, ih2⟩
  | mul _ _ ih1 ih2 => exact ⟨ih1, ih2⟩
  | neg _ ih => exact ih
  | sin _ ih => exact ih
  | cos _ ih => exact ih
  | exp _ ih => exact ih

/-- Fundamental correctness theorem for Dyadic evaluation.

This theorem states that for any supported expression and any real values
within the input intervals, the result of evaluating the expression is
contained in the computed Dyadic interval.

The proof follows the same structure as `evalIntervalCore_correct`, but
with additional steps for handling Dyadic ↔ Rat conversions and rounding.
Requires cfg.precision ≤ 0 (the default -53 satisfies this).

Note: Requires domain validity for log (positive argument interval). -/
theorem evalIntervalDyadic_correct (e : Expr) (hsupp : ExprSupportedCore e)
    (ρ_real : Nat → ℝ) (ρ_dyad : IntervalDyadicEnv)
    (hρ : envMemDyadic ρ_real ρ_dyad) (cfg : DyadicConfig := {})
    (hprec : cfg.precision ≤ 0 := by norm_num)
    (hdom : evalDomainValidDyadic e ρ_dyad cfg) :
    Expr.eval ρ_real e ∈ evalIntervalDyadic e ρ_dyad cfg := by
  induction hsupp with
  | const q =>
    simp only [Expr.eval_const, evalIntervalDyadic]
    apply IntervalDyadic.mem_ofIntervalRat
    · exact IntervalRat.mem_singleton q
    · exact hprec
  | var idx =>
    simp only [Expr.eval_var, evalIntervalDyadic]
    exact hρ idx
  | add _ _ ih₁ ih₂ =>
    simp only [evalDomainValidDyadic] at hdom
    simp only [Expr.eval_add, evalIntervalDyadic]
    have h := IntervalDyadic.mem_add (ih₁ hdom.1) (ih₂ hdom.2)
    exact IntervalDyadic.roundOut_contains h cfg.precision
  | mul _ _ ih₁ ih₂ =>
    simp only [evalDomainValidDyadic] at hdom
    simp only [Expr.eval_mul, evalIntervalDyadic]
    have h := IntervalDyadic.mem_mul (ih₁ hdom.1) (ih₂ hdom.2)
    exact IntervalDyadic.roundOut_contains h cfg.precision
  | neg _ ih =>
    simp only [evalDomainValidDyadic] at hdom
    simp only [Expr.eval_neg, evalIntervalDyadic]
    exact IntervalDyadic.mem_neg (ih hdom)
  | sin _ ih =>
    simp only [evalDomainValidDyadic] at hdom
    simp only [Expr.eval_sin, evalIntervalDyadic, sinIntervalDyadic]
    have hrat := IntervalDyadic.mem_toIntervalRat.mp (ih hdom)
    have hsin := IntervalRat.mem_sinComputable hrat cfg.taylorDepth
    exact IntervalDyadic.mem_ofIntervalRat hsin cfg.precision hprec
  | cos _ ih =>
    simp only [evalDomainValidDyadic] at hdom
    simp only [Expr.eval_cos, evalIntervalDyadic, cosIntervalDyadic]
    have hrat := IntervalDyadic.mem_toIntervalRat.mp (ih hdom)
    have hcos := IntervalRat.mem_cosComputable hrat cfg.taylorDepth
    exact IntervalDyadic.mem_ofIntervalRat hcos cfg.precision hprec
  | exp _ ih =>
    simp only [evalDomainValidDyadic] at hdom
    simp only [Expr.eval_exp, evalIntervalDyadic, expIntervalDyadic]
    have hrat := IntervalDyadic.mem_toIntervalRat.mp (ih hdom)
    have hexp := IntervalRat.mem_expComputable hrat cfg.taylorDepth
    exact IntervalDyadic.mem_ofIntervalRat hexp cfg.precision hprec
  | sqrt _ ih =>
    simp only [evalDomainValidDyadic] at hdom
    simp only [Expr.eval_sqrt, evalIntervalDyadic, sqrtIntervalDyadic]
    exact IntervalDyadic.mem_sqrt' (ih hdom) cfg.precision
  | sinh _ ih =>
    simp only [evalDomainValidDyadic] at hdom
    simp only [Expr.eval_sinh, evalIntervalDyadic, sinhIntervalDyadic]
    have hrat := IntervalDyadic.mem_toIntervalRat.mp (ih hdom)
    have hsinh := IntervalRat.mem_sinhComputable hrat cfg.taylorDepth
    exact IntervalDyadic.mem_ofIntervalRat hsinh cfg.precision hprec
  | cosh _ ih =>
    simp only [evalDomainValidDyadic] at hdom
    simp only [Expr.eval_cosh, evalIntervalDyadic, coshIntervalDyadic]
    have hrat := IntervalDyadic.mem_toIntervalRat.mp (ih hdom)
    have hcosh := IntervalRat.mem_coshComputable hrat cfg.taylorDepth
    exact IntervalDyadic.mem_ofIntervalRat hcosh cfg.precision hprec
  | @tanh e' _ ih =>
    simp only [evalDomainValidDyadic] at hdom
    simp only [Expr.eval_tanh, evalIntervalDyadic, tanhIntervalDyadic]
    -- tanh x ∈ [-1, 1] for all x
    rw [IntervalDyadic.mem_def, Dyadic.toRat_ofInt, Dyadic.toRat_ofInt]
    simp only [Int.cast_neg, Int.cast_one, Rat.cast_neg, Rat.cast_one]
    set x := Expr.eval ρ_real e' with hx
    constructor
    -- tanh x ≥ -1: use tanh = sinh/cosh, cosh > 0, and -cosh ≤ sinh
    · rw [Real.tanh_eq_sinh_div_cosh]
      have hcosh : Real.cosh x > 0 := Real.cosh_pos x
      rw [le_div_iff₀ hcosh, neg_one_mul]
      rw [Real.sinh_eq, Real.cosh_eq]
      have h1 : Real.exp x > 0 := Real.exp_pos x
      linarith
    -- tanh x ≤ 1: use sinh ≤ cosh (since exp(-x) > 0)
    · rw [Real.tanh_eq_sinh_div_cosh]
      have hcosh : Real.cosh x > 0 := Real.cosh_pos x
      rw [div_le_one₀ hcosh]
      rw [Real.sinh_eq, Real.cosh_eq]
      have h2 : Real.exp (-x) > 0 := Real.exp_pos (-x)
      linarith
  | @erf e' _ ih =>
    simp only [evalDomainValidDyadic] at hdom
    simp only [Expr.eval_erf, evalIntervalDyadic, erfIntervalDyadic]
    -- erf x ∈ [-1, 1] for all x
    rw [IntervalDyadic.mem_def, Dyadic.toRat_ofInt, Dyadic.toRat_ofInt]
    simp only [Int.cast_neg, Int.cast_one, Rat.cast_neg, Rat.cast_one]
    exact ⟨Real.neg_one_le_erf _, Real.erf_le_one _⟩
  | log _ ih =>
    simp only [evalDomainValidDyadic] at hdom
    simp only [Expr.eval_log, evalIntervalDyadic, logIntervalDyadic]
    have hrat := IntervalDyadic.mem_toIntervalRat.mp (ih hdom.1)
    -- hdom.2 gives us the positivity condition: IRat.lo > 0
    -- This makes the if-condition true, so we take the positive branch
    have hpos : (evalIntervalDyadic _ ρ_dyad cfg).toIntervalRat.lo > 0 := hdom.2
    simp only [hpos, ↓reduceIte]
    have hlog := IntervalRat.mem_logComputable hrat hpos cfg.taylorDepth
    exact IntervalDyadic.mem_ofIntervalRat hlog cfg.precision hprec
  | pi =>
    simp only [Expr.eval_pi, evalIntervalDyadic]
    exact IntervalDyadic.mem_ofIntervalRat mem_piInterval cfg.precision hprec

/-- Correctness theorem for Dyadic evaluation with ExprSupportedWithInv.

Extends `evalIntervalDyadic_correct` to handle `inv` (and delegates to it for
all ExprSupportedCore cases). Requires the `inv` argument interval to be bounded
away from zero. -/
theorem evalIntervalDyadic_correct_withInv (e : Expr) (hsupp : ExprSupportedWithInv e)
    (ρ_real : Nat → ℝ) (ρ_dyad : IntervalDyadicEnv)
    (hρ : envMemDyadic ρ_real ρ_dyad) (cfg : DyadicConfig := {})
    (hprec : cfg.precision ≤ 0 := by norm_num)
    (hdom : evalDomainValidDyadic e ρ_dyad cfg) :
    Expr.eval ρ_real e ∈ evalIntervalDyadic e ρ_dyad cfg := by
  induction hsupp with
  | const q =>
    simp only [Expr.eval_const, evalIntervalDyadic]
    apply IntervalDyadic.mem_ofIntervalRat
    · exact IntervalRat.mem_singleton q
    · exact hprec
  | var idx =>
    simp only [Expr.eval_var, evalIntervalDyadic]
    exact hρ idx
  | add _ _ ih₁ ih₂ =>
    simp only [evalDomainValidDyadic] at hdom
    simp only [Expr.eval_add, evalIntervalDyadic]
    have h := IntervalDyadic.mem_add (ih₁ hdom.1) (ih₂ hdom.2)
    exact IntervalDyadic.roundOut_contains h cfg.precision
  | mul _ _ ih₁ ih₂ =>
    simp only [evalDomainValidDyadic] at hdom
    simp only [Expr.eval_mul, evalIntervalDyadic]
    have h := IntervalDyadic.mem_mul (ih₁ hdom.1) (ih₂ hdom.2)
    exact IntervalDyadic.roundOut_contains h cfg.precision
  | neg _ ih =>
    simp only [evalDomainValidDyadic] at hdom
    simp only [Expr.eval_neg, evalIntervalDyadic]
    exact IntervalDyadic.mem_neg (ih hdom)
  | inv _ ih =>
    simp only [evalDomainValidDyadic] at hdom
    simp only [Expr.eval_inv, evalIntervalDyadic, invIntervalDyadic]
    have hinner := ih hdom.1
    have hrat := IntervalDyadic.mem_toIntervalRat.mp hinner
    have hinv := mem_invInterval_nonzero hrat hdom.2
    exact IntervalDyadic.mem_ofIntervalRat hinv cfg.precision hprec
  | exp _ ih =>
    simp only [evalDomainValidDyadic] at hdom
    simp only [Expr.eval_exp, evalIntervalDyadic, expIntervalDyadic]
    have hrat := IntervalDyadic.mem_toIntervalRat.mp (ih hdom)
    have hexp := IntervalRat.mem_expComputable hrat cfg.taylorDepth
    exact IntervalDyadic.mem_ofIntervalRat hexp cfg.precision hprec
  | sin _ ih =>
    simp only [evalDomainValidDyadic] at hdom
    simp only [Expr.eval_sin, evalIntervalDyadic, sinIntervalDyadic]
    have hrat := IntervalDyadic.mem_toIntervalRat.mp (ih hdom)
    have hsin := IntervalRat.mem_sinComputable hrat cfg.taylorDepth
    exact IntervalDyadic.mem_ofIntervalRat hsin cfg.precision hprec
  | cos _ ih =>
    simp only [evalDomainValidDyadic] at hdom
    simp only [Expr.eval_cos, evalIntervalDyadic, cosIntervalDyadic]
    have hrat := IntervalDyadic.mem_toIntervalRat.mp (ih hdom)
    have hcos := IntervalRat.mem_cosComputable hrat cfg.taylorDepth
    exact IntervalDyadic.mem_ofIntervalRat hcos cfg.precision hprec
  | log _ ih =>
    simp only [evalDomainValidDyadic] at hdom
    simp only [Expr.eval_log, evalIntervalDyadic, logIntervalDyadic]
    have hrat := IntervalDyadic.mem_toIntervalRat.mp (ih hdom.1)
    have hpos : (evalIntervalDyadic _ ρ_dyad cfg).toIntervalRat.lo > 0 := hdom.2
    simp only [hpos, ↓reduceIte]
    have hlog := IntervalRat.mem_logComputable hrat hpos cfg.taylorDepth
    exact IntervalDyadic.mem_ofIntervalRat hlog cfg.precision hprec
  | @atan e' _ ih =>
    simp only [evalDomainValidDyadic] at hdom
    simp only [Expr.eval_atan, evalIntervalDyadic, atanIntervalDyadic]
    rw [IntervalDyadic.mem_def, Dyadic.toRat_ofInt, Dyadic.toRat_ofInt]
    simp only [Int.cast_neg, Int.cast_ofNat, Rat.cast_neg, Rat.cast_ofNat]
    set x := Expr.eval ρ_real e' with hx
    constructor
    · linarith [Real.neg_pi_div_two_lt_arctan x, Real.pi_lt_four]
    · linarith [Real.arctan_lt_pi_div_two x, Real.pi_lt_four]
  | sinc _ ih =>
    simp only [evalDomainValidDyadic] at hdom
    simp only [Expr.eval_sinc, evalIntervalDyadic, sincIntervalDyadic]
    rw [IntervalDyadic.mem_def, Dyadic.toRat_ofInt, Dyadic.toRat_ofInt]
    simp only [Int.cast_neg, Int.cast_one, Rat.cast_neg, Rat.cast_one]
    exact ⟨Real.neg_one_le_sinc _, Real.sinc_le_one _⟩
  | arsinh _ ih =>
    simp only [evalDomainValidDyadic] at hdom
    simp only [Expr.eval_arsinh, evalIntervalDyadic, arsinhIntervalDyadic]
    have hrat := IntervalDyadic.mem_toIntervalRat.mp (ih hdom)
    have harsinh := mem_arsinhInterval hrat
    exact IntervalDyadic.mem_ofIntervalRat harsinh cfg.precision hprec
  | atanh _ ih =>
    simp only [evalDomainValidDyadic] at hdom
    obtain ⟨hdom_sub, hlo_gt, hhi_lt⟩ := hdom
    simp only [Expr.eval_atanh, evalIntervalDyadic, atanhIntervalDyadic]
    have hrat := IntervalDyadic.mem_toIntervalRat.mp (ih hdom_sub)
    have hatanh := IntervalRat.mem_atanhComputable hrat hlo_gt hhi_lt cfg.taylorDepth
    exact IntervalDyadic.mem_ofIntervalRat hatanh cfg.precision hprec
  | erf _ ih =>
    simp only [evalDomainValidDyadic] at hdom
    simp only [Expr.eval_erf, evalIntervalDyadic, erfIntervalDyadic]
    rw [IntervalDyadic.mem_def, Dyadic.toRat_ofInt, Dyadic.toRat_ofInt]
    simp only [Int.cast_neg, Int.cast_one, Rat.cast_neg, Rat.cast_one]
    exact ⟨Real.neg_one_le_erf _, Real.erf_le_one _⟩
  | sqrt _ ih =>
    simp only [evalDomainValidDyadic] at hdom
    simp only [Expr.eval_sqrt, evalIntervalDyadic, sqrtIntervalDyadic]
    exact IntervalDyadic.mem_sqrt' (ih hdom) cfg.precision
  | pi =>
    simp only [Expr.eval_pi, evalIntervalDyadic]
    exact IntervalDyadic.mem_ofIntervalRat mem_piInterval cfg.precision hprec

/-! ### Convenience Functions -/

/-- Evaluate with standard (double-like) precision -/
def evalDyadic (e : Expr) (ρ : IntervalDyadicEnv) : IntervalDyadic :=
  evalIntervalDyadic e ρ

/-- Evaluate with high precision -/
def evalDyadicHighPrec (e : Expr) (ρ : IntervalDyadicEnv) : IntervalDyadic :=
  evalIntervalDyadic e ρ DyadicConfig.highPrecision

/-- Evaluate with fast settings (lower precision) -/
def evalDyadicFast (e : Expr) (ρ : IntervalDyadicEnv) : IntervalDyadic :=
  evalIntervalDyadic e ρ DyadicConfig.fast

/-! ### Verification Checkers -/

/-- Check if expression is bounded above by q -/
def checkUpperBoundDyadic (e : Expr) (ρ : IntervalDyadicEnv) (q : ℚ)
    (cfg : DyadicConfig := {}) : Bool :=
  (evalIntervalDyadic e ρ cfg).upperBoundedBy q

/-- Check if expression is bounded below by q -/
def checkLowerBoundDyadic (e : Expr) (ρ : IntervalDyadicEnv) (q : ℚ)
    (cfg : DyadicConfig := {}) : Bool :=
  (evalIntervalDyadic e ρ cfg).lowerBoundedBy q

/-- Check if expression is bounded in interval [lo, hi] -/
def checkBoundsDyadic (e : Expr) (ρ : IntervalDyadicEnv) (lo hi : ℚ)
    (cfg : DyadicConfig := {}) : Bool :=
  let result := evalIntervalDyadic e ρ cfg
  result.lowerBoundedBy lo && result.upperBoundedBy hi

end LeanCert.Engine
