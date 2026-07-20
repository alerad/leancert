# Golden Theorems

LeanCert operates on a **certificate-driven architecture** where computable
checkers run in Lean, and Golden Theorems lift successful checks to semantic
theorems over real numbers.

## Concept

A Golden Theorem bridges the gap between a computable boolean check (which `native_decide` can run) and a semantic proposition about real numbers.

For example, to prove $f(x) \le c$ for all $x \in I$, we use:

$$
\text{checkUpperBound}(e, I, c) = \text{true} \implies \forall x \in I,\ \text{eval}(x, e) \le c
$$

The key insight is that the checker runs in the Lean kernel using computable rational arithmetic, while the conclusion is a statement about real numbers.

## Core Theorems

Golden Theorems are defined across multiple files:
- `Validity/Bounds.lean` - Rational arithmetic (the tactic-level default)
- `Validity/DyadicBounds.lean` - Dyadic arithmetic (fast)
- `Validity/AffineBounds.lean` - Affine arithmetic (tight bounds)
- `Validity/Monotonicity.lean` - Monotonicity via automatic differentiation
- `Validity/Krawczyk.lean` - existence and uniqueness for square systems in the differentiable AD fragment
- `Engine/Chebyshev/Psi.lean` - Chebyshev `ψ` finite-range certificates
- `Engine/Chebyshev/Theta.lean` - Chebyshev `θ` finite-range certificates
- `Cert/Interval.lean` - shared rational interval Golden Theorem combinators
- `ANT/Step.lean` - finite arithmetic step-sum certificates
- `ANT/Abel.lean` - finite Abel / partial-summation certificates
- `ANT/EulerProduct.lean` - finite Euler-product and log-product certificates
- `ANT/PrimeEuler.lean` - prime Euler-product presets
- `ANT/Dirichlet.lean` - finite Dirichlet-style truncation certificates
- `ANT/Mertens.lean` - finite Mertens-style prime-sum certificates
- `ANT/Asymp/Env.lean` - asymptotic main-term/error envelope certificates
- `ANT/Asymp/Stieltjes.lean` - Stieltjes-Abel envelope transform certificates
- `ANT/Asymp/Hyperbola.lean` - Dirichlet-hyperbola envelope certificates
- `ANT/Asymp/Checkers.lean` - dyadic domination checkers for envelope errors
- `QProduct/Certificate.lean` - Exact finite q-product integrals
- `QProduct/PrimeLambda.lean` - Prime-limit q-product certificates

### Bound Verification

| Goal | Theorem | Checker |
|------|---------|---------|
| Upper bound $f(x) \le c$ | `verify_upper_bound` | `checkUpperBound` |
| Lower bound $c \le f(x)$ | `verify_lower_bound` | `checkLowerBound` |
| Strict upper $f(x) < c$ | `verify_strict_upper_bound` | `checkStrictUpperBound` |
| Strict lower $c < f(x)$ | `verify_strict_lower_bound` | `checkStrictLowerBound` |

```lean
theorem verify_upper_bound (e : Expr) (hsupp : ExprSupportedCore e)
    (I : IntervalRat) (c : ℚ) (cfg : EvalConfig)
    (h_cert : checkUpperBound e I c cfg = true) :
    ∀ x ∈ I, Expr.eval (fun _ => x) e ≤ c
```

### Root Finding

| Goal | Theorem | Checker |
|------|---------|---------|
| Root existence | `verify_sign_change` | `checkSignChange` |
| Root uniqueness | `verify_unique_root_computable` | `checkNewtonContractsCore` |
| No roots | `verify_no_root` | `checkNoRoot` |
| System-root existence | `verify_system_root_exists` | `krawczykCheck` |
| System-root uniqueness | `verify_system_root_unique` | `krawczykCheck` |
| Unique system root | `verify_unique_system_root` | `krawczykCheck` |

```lean
theorem verify_sign_change (e : Expr) (hsupp : ExprSupportedCore e)
    (I : IntervalRat) (cfg : EvalConfig)
    (hCont : ContinuousOn (fun x => Expr.eval (fun _ => x) e) (Set.Icc I.lo I.hi))
    (h_cert : checkSignChange e I cfg = true) :
    ∃ x ∈ I, Expr.eval (fun _ => x) e = 0
```

### Global Optimization

| Goal | Theorem | Checker |
|------|---------|---------|
| Global lower bound | `verify_global_lower_bound` | `checkGlobalLowerBound` |
| Global upper bound | `verify_global_upper_bound` | `checkGlobalUpperBound` |

```lean
theorem verify_global_lower_bound (e : Expr) (hsupp : ADSupported e)
    (B : Box) (c : ℚ) (cfg : GlobalOptConfig)
    (h_cert : checkGlobalLowerBound e B c cfg = true) :
    ∀ (ρ : Nat → ℝ), Box.envMem ρ B → (∀ i, i ≥ B.length → ρ i = 0) →
      c ≤ Expr.eval ρ e
```

> **Note**: Global optimization uses `ADSupported` (not `ExprSupportedCore`) and multivariate environments.

### Integration

**Rational backend:**

```lean
theorem verify_integral_bound (e : Expr) (hsupp : ExprSupportedCore e)
    (I : IntervalRat) (target : ℚ) (cfg : EvalConfig)
    (h_cert : checkIntegralBoundsCore e I target cfg = true)
    (hcontdom : exprContinuousDomainValid e (Set.Icc I.lo I.hi)) :
    ∫ x in I.lo..I.hi, Expr.eval (fun _ => x) e ∈ integrateInterval1Core e I cfg
```

**Dyadic backend** (for complex integrands like Li₂ where rational arithmetic explodes):

```lean
theorem integrateInterval1Dyadic_correct (e : Expr)
    (I : IntervalRat) (cfg : DyadicConfig)
    (hprec : cfg.precision ≤ 0)
    (hdom : evalDomainValidDyadic e (fun _ => IntervalDyadic.ofIntervalRat I cfg.precision) cfg)
    (hInt : IntervalIntegrable (fun x => Expr.eval (fun _ => x) e) volume I.lo I.hi) :
    ∫ x in (I.lo : ℝ)..(I.hi : ℝ), Expr.eval (fun _ => x) e ∈
      integrateInterval1Dyadic e I cfg
```

The theorem-level dyadic integration path accepts arbitrary expressions
(including `inv`, `log`, `atanh`) under explicit domain-validity hypotheses.
Public computational endpoints use checked evaluators and return a domain error
instead of exposing finite fallback bounds.

```lean
theorem integratePartitionDyadic_correct (e : Expr)
    (I : IntervalRat) (n : ℕ) (hn : 0 < n) (cfg : DyadicConfig)
    (hprec : cfg.precision ≤ 0)
    (hdom : ∀ k (hk : k < n), evalDomainValidDyadic e ...)
    (hInt : IntervalIntegrable ...) :
    ∫ x in (I.lo : ℝ)..(I.hi : ℝ), Expr.eval (fun _ => x) e ∈
      integratePartitionDyadic e I n hn cfg
```

### QProduct Product Integrals

`LeanCert.QProduct` is a specialized exact-arithmetic certificate family for
finite products

$$
F(S) = \int_0^1 \prod_{n \in S} (1 - u^n)\,du.
$$

The finite checker expands the product into a signed subset-sum polynomial and
integrates exactly over `ℚ`.

| Goal | Theorem | Checker |
|------|---------|---------|
| Exact finite interval | `verify_finiteIntegral_interval` | `checkFiniteIntegralInterval` |
| Finite upper bound | `verify_finiteIntegral_upper` | `checkFiniteIntegralUpper` |
| Finite lower bound | `verify_finiteIntegral_lower` | `checkFiniteIntegralLower` |
| Prime-limit upper bound | `verify_primeLambda_upper` | `checkPrimeLambdaUpper` |

```lean
theorem verify_finiteIntegral_interval (S : Finset Nat) (lo hi : ℚ)
    (hcheck : checkFiniteIntegralInterval S lo hi = true) :
    (lo : ℝ) ≤ F S ∧ F S ≤ (hi : ℝ)
```

```lean
theorem verify_primeLambda_upper (N : Nat) (hi : ℚ)
    (hcheck : checkPrimeLambdaUpper N hi = true) :
    primeLambda ≤ (hi : ℝ)
```

Prime-limit lower bounds are intentionally hybrid: the finite arithmetic is
exact, but the lower side needs a mathematical tail proof. The bridge theorem
is:

```lean
theorem primeLambda_lower_of_forall (lo : ℚ)
    (hlo : ∀ N : Nat, (lo : ℝ) ≤ (primeFRat N : ℝ)) :
    (lo : ℝ) ≤ primeLambda
```

The reusable odd-prime tail certificate is:

```lean
theorem primeLambda_sandwich {N m : Nat}
    (hN : 2 ≤ N) (hm : Odd m)
    (htail_ge : ∀ p, Nat.Prime p → N < p → m ≤ p) :
    (primeFRat N : ℝ) - (primeSandwichErrorRat N m : ℝ) ≤ primeLambda ∧
      primeLambda ≤ (primeFRat N : ℝ)
```

The initial module includes the formally proved tail certificate
`primeLambda_gt_half : (1 : ℝ) / 2 < primeLambda`.

### Chebyshev Certificates

The Chebyshev engines expose specialized finite-range Golden Theorems for
number-theoretic functions.

For `ψ`, the checker bounds a computable rational envelope `psiUB`:

| Goal | Theorem | Checker |
|------|---------|---------|
| One natural input | `verify_psi_le_mul` | `checkPsiLeMulWith` |
| All natural inputs up to `bound` | `verify_all_psi_le_mul` | `checkAllPsiLeMulWith` |
| All real inputs up to `bound` | `verify_all_psi_le_mul_real` | `checkAllPsiLeMulWith` |

```lean
theorem verify_all_psi_le_mul
    (bound depth : Nat) (slope : ℚ)
    (hcheck : checkAllPsiLeMulWith bound slope depth = true) :
    ∀ N : Nat, 0 < N → N ≤ bound →
      Chebyshev.psi (N : ℝ) ≤ (slope : ℝ) * N
```

For `θ`, the checker supports upper, absolute-error, and relative-error bounds:

| Goal | Theorem | Checker |
|------|---------|---------|
| Upper bound | `verify_theta_le_mul` | `checkThetaLeMulWith` |
| Absolute error | `verify_theta_abs_error` | `checkThetaAbsError` |
| Relative error | `verify_theta_rel_error` | `checkThetaRelError` |
| Range relative error | `verify_all_theta_rel_error` | `checkAllThetaRelError` |
| Unit-interval real relative error | `verify_theta_rel_error_real` | `checkThetaRelErrorReal` |

```lean
theorem verify_all_theta_rel_error
    (start limit depth : Nat) (bound : ℚ)
    (hcheck : checkAllThetaRelError start limit bound depth = true) :
    ∀ N : Nat, 0 < N → start ≤ N → N ≤ limit →
      |Chebyshev.theta (N : ℝ) - N| ≤ (bound : ℝ) * N
```

### Analytic Number Theory Bridges

The ANT layer exposes small bridge Golden Theorems that compose with the
Chebyshev engines.

The shared interval helper used by these APIs is:

```lean
theorem LeanCert.Cert.verify_rat_interval {value : ℝ} {lower upper lo hi : ℚ}
    (hlower : (lower : ℝ) ≤ value)
    (hupper : value ≤ (upper : ℝ))
    (hcheck : checkRatInterval lower upper lo hi = true) :
    (lo : ℝ) ≤ value ∧ value ≤ (hi : ℝ)
```

| Goal | Theorem | Checker/Data |
|------|---------|--------------|
| Finite step-sum interval | `verify_stepSum_interval` | `checkStepSumInterval` |
| Exact Abel interval | `verify_abel_interval` | `checkAbelInterval` |
| Bounded Abel interval | `verify_abelBound_interval` | `checkAbelBoundInterval` |
| Finite Euler product interval | `verify_eulerProduct_interval` | `checkEulerProductInterval` |
| Finite log-product interval | `verify_logProduct_interval` | `checkLogProductInterval` |
| Log interval to product interval | `verify_product_interval_of_log_interval` | log interval proof |
| Log lower to product lower | `verify_product_lower_of_log_lower` | log lower proof |
| Log upper to product upper | `verify_product_upper_of_log_upper` | log upper proof |
| Prime product `∏(1 - 1/p)` | `verify_primeEulerOneMinusInv_interval` | `checkPrimeEulerOneMinusInvInterval` |
| Prime product `∏(1 + 1/p)` | `verify_primeEulerOnePlusInv_interval` | `checkPrimeEulerOnePlusInvInterval` |
| Finite Dirichlet sum interval | `verify_dirichletSum_interval` | `checkDirichletSumInterval` |
| Harmonic truncation interval | `verify_harmonicSum_interval` | `checkHarmonicSumInterval` |
| Prime harmonic truncation interval | `verify_primeHarmonicSum_interval` | `checkPrimeHarmonicSumInterval` |
| Prime log-over-prime interval | `verify_logPrimeOverPrimeSum_interval` | `checkLogPrimeOverPrimeSumInterval` |
| Finite Mertens log-sum interval | `verify_mertensLogSum_interval` | `checkMertensLogSumInterval` |
| Abel-routed Mertens interval | `verify_mertensAbel_interval` | `checkMertensAbelInterval` |

The central exact identity is:

```lean
theorem weightedSumRat_eq_abelTransformRat {a f : Nat → ℚ} {m n : Nat}
    (hmn : m < n) :
    (weightedSumRat a f m n : ℝ) = (abelTransformRat a f m n : ℝ)
```

The first Chebyshev-to-Mertens bridge is finite:

```lean
theorem verify_mertensLogSum_interval (N depth : Nat) (lo hi : ℚ)
    (hcheck : checkMertensLogSumInterval N depth lo hi = true) :
    (lo : ℝ) ≤ mertensLogSum N ∧ mertensLogSum N ≤ (hi : ℝ)
```

Here `mertensLogSum N` is `∑ p ≤ N, log p / p`, and the checker uses the
existing Chebyshev theta logarithm envelopes.

The bounded Abel bridge has the reusable shape:

```lean
theorem verify_abelBound_interval
    (a : Nat → ℝ) (f ALo AHi : Nat → ℚ) {m n : Nat} (hmn : m < n)
    (hA : ∀ k, (ALo k : ℝ) ≤ prefixSum a k ∧
      prefixSum a k ≤ (AHi k : ℝ))
    (lo hi : ℚ)
    (hcheck : checkAbelBoundInterval f ALo AHi m n lo hi = true) :
    (lo : ℝ) ≤ weightedSum a f m n ∧ weightedSum a f m n ≤ (hi : ℝ)
```

### Asymptotic Envelope Certificates

The asymptotic layer introduces semantic main-term/error-term envelopes for
summatory functions:

```lean
structure AsympEnv where
  seq : Nat → ℝ
  cutoff : Nat
  mainTerm : Expr
  errorTerm : Expr
  cert :
    ∀ N, cutoff ≤ N →
      |prefixSum seq (N + 1) - evalAtNat mainTerm N| ≤ evalAtNat errorTerm N
  error_nonneg :
    ∀ N, cutoff ≤ N → 0 ≤ evalAtNat errorTerm N
```

The Golden Theorem families are:

| Goal | Theorem / API |
|------|---------------|
| Envelope lower/upper bounds | `AsympEnv.lower_le_summatory`, `AsympEnv.summatory_le_upper` |
| Stieltjes-Abel envelope | `verify_stieltjes_envelope` |
| `1 / n` Stieltjes envelope | `verify_one_over_n_stieltjes_envelope` |
| Dirichlet hyperbola envelope | `verify_dirichlet_hyperbola_envelope` |
| Convolution via hyperbola bridge | `verify_dirichlet_convolution_envelope` |
| Dyadic expression domination | `verify_expr_le_on_interval_dyadic`, `verify_expr_le_with_slab_tail_dyadic` |
| Generated Stieltjes error domination | `verify_stieltjes_error_le_target_with_slab_tail_dyadic` |
| Generated hyperbola error domination | `verify_hyperbola_error_le_target_with_slab_tail_dyadic` |

The usual workflow is to generate a transform envelope, prove that its generated
error term is dominated by a simpler public error term, and then use
`AsympEnv.weakenError` to expose the simpler statement.

### Monotonicity

Prove monotonicity properties using automatic differentiation with interval arithmetic.

| Goal | Theorem | Checker |
|------|---------|---------|
| Strictly increasing | `verify_strictly_increasing` | `checkStrictlyIncreasing` |
| Strictly decreasing | `verify_strictly_decreasing` | `checkStrictlyDecreasing` |
| Monotone (weak) | `verify_monotone` | `checkStrictlyIncreasing` |
| Antitone (weak) | `verify_antitone` | `checkStrictlyDecreasing` |

```lean
theorem verify_strictly_increasing (e : Expr) (hsupp : ADSupported e)
    (I : IntervalRat) (cfg : EvalConfig)
    (h_check : checkStrictlyIncreasing e I cfg = true) :
    StrictMonoOn (fun x => Expr.eval (fun _ => x) e) (Set.Icc I.lo I.hi)
```

The approach uses automatic differentiation to compute interval bounds on derivatives:
1. Compute `dI := derivIntervalCore e I cfg` (interval containing all derivatives)
2. If `dI.lo > 0`, then f'(x) > 0 for all x ∈ I, so f is strictly increasing
3. If `dI.hi < 0`, then f'(x) < 0 for all x ∈ I, so f is strictly decreasing

The mathematical foundation is the Mean Value Theorem: if f' has consistent sign, then f is monotonic.

**Example:**
```lean
-- Prove exp is strictly increasing on [0, 1]
theorem exp_strictly_increasing :
    StrictMonoOn (fun x => Real.exp x) (Set.Icc 0 1) := by
  have h := verify_strictly_increasing (Expr.exp (Expr.var 0))
    (ADSupported.exp (ADSupported.var 0))
    ⟨0, 1, by norm_num⟩ {} (by native_decide)
  simp only [Expr.eval_exp, Expr.eval_var] at h
  convert h using 2 <;> simp
```

## Expression Support Tiers

Not all expressions support all theorems.

### ExprSupportedCore

Fully computable subset enabling `native_decide`:

- `const`, `var`, `add`, `mul`, `neg`
- `sin`, `cos`, `exp`, `sqrt` (via Taylor series)

Trigonometric range reduction is shared through `LeanCert.Core.TrigReduction`.
That module provides rational bounds for `π` and `2π`, computable period
shifting, and correctness lemmas reused by both interval-rational and Taylor
model trigonometric evaluators.

### Checked evaluation and domains

Checked evaluators accept arbitrary `Expr` values. Partial functions such as
`inv`, `log`, and `atanh` are governed by runtime domain checks rather than a
second syntactic support predicate. A successful `Option`/`EvalResult` carries
an enclosure; an invalid domain returns `none` or a structured error.

## Arithmetic Backends

LeanCert provides three arithmetic backends, each with different tradeoffs:

| Backend | File | Speed | Precision | Best For |
|---------|------|-------|-----------|----------|
| **Rational** | `Validity/Bounds.lean` | Slow | Exact | Small expressions, reproducibility |
| **Dyadic** | `Validity/DyadicBounds.lean` | Fast | Fixed-precision | Deep expressions, neural networks |
| **Affine** | `Validity/AffineBounds.lean` | Medium | Correlation-aware | Dependency-heavy expressions |

### Rational Backend (Tactic Default)

The standard theorem/tactic backend uses arbitrary-precision rationals. It
guarantees exact intermediate results but can suffer from denominator
explosion on deep expressions. The unified programmatic selector defaults to
the checked Dyadic backend for evaluation and optimization.

### Dyadic Backend

Uses fixed-precision dyadic numbers (m · 2^e) to avoid denominator explosion:

```lean
theorem verify_upper_bound_dyadic (e : Expr) (hsupp : ExprSupportedCore e)
    (lo hi : ℚ) (hle : lo ≤ hi) (c : ℚ)
    (prec : Int) (depth : Nat) (h_prec : prec ≤ 0)
    (hdom : evalDomainValidDyadic e ...)
    (h_check : checkUpperBoundDyadic e lo hi hle c prec depth = true) :
    ∀ x ∈ Set.Icc lo hi, Expr.eval (fun _ => x) e ≤ c
```

> **Note**: The API takes rational bounds (`lo`, `hi`, `c : ℚ`) for user convenience, but internally converts to `IntervalDyadic` and runs `evalIntervalDyadic` — the actual computation uses Dyadic arithmetic for speed.

Key parameters:
- `prec : Int` - Precision (negative = more precision, must be ≤ 0)
- `depth : Nat` - Taylor series depth for transcendentals

The `'` variant (`verify_upper_bound_dyadic'`) uses `ADSupported` and handles domain validity automatically.

Essential for neural network verification and optimization loops where expression depth can be in the hundreds.

### Affine Backend

Solves the "dependency problem" in interval arithmetic by tracking linear correlations:

```lean
theorem verify_upper_bound_affine1 (e : Expr) (hsupp : ExprSupportedCore e)
    (I : IntervalRat) (c : ℚ) (cfg : AffineConfig)
    (hdom : evalDomainValidAffine e (toAffineEnvConst I) cfg)
    (h_check : checkUpperBoundAffine1 e I c cfg = true) :
    ∀ x ∈ I, Expr.eval (fun _ => x) e ≤ c
```

The `'` variant (`verify_upper_bound_affine1'`) uses `ADSupported` and handles domain validity automatically.

Affine arithmetic represents values as `x̂ = c₀ + Σᵢ cᵢ·εᵢ + [-r, r]` where εᵢ ∈ [-1, 1] are noise symbols. This means:

- Standard IA: `x - x` on `[-1, 1]` → `[-2, 2]` (pessimistic)
- Affine AA: `x - x` on `[-1, 1]` → `[0, 0]` (exact)

Use affine when the same variable appears multiple times in an expression.

## Backend Theorems Summary

| Goal | Rational | Dyadic | Affine |
|------|----------|--------|--------|
| Upper bound | `verify_upper_bound` | `verify_upper_bound_dyadic` | `verify_upper_bound_affine1` |
| Lower bound | `verify_lower_bound` | `verify_lower_bound_dyadic` | `verify_lower_bound_affine1` |

Each backend also provides `'` variants for `ADSupported` expressions where domain validity is automatic:
- `verify_upper_bound_dyadic'`
- `verify_lower_bound_affine1'`
- etc.

## Kernel Verification

For higher trust, the dyadic backend supports verification via `decide` instead of `native_decide`:

| Theorem | Verification | Trust Level |
|---------|--------------|-------------|
| `verify_upper_bound_dyadic` | `decide` | Kernel only |
| `verify_lower_bound_dyadic` | `decide` | Kernel only |

This removes the compiler from the trusted computing base—only the Lean kernel must be trusted.

**Note**: Kernel verification requires the goal to be in `Core.Expr.eval` form with rational interval bounds.

## The Certificate Workflow

1. **Formulate the goal in Lean**: expression, domain, and target claim
2. **Run the checker**: evaluate `check... = true` (typically via `native_decide`)
3. **Apply the Golden Theorem**: lift the boolean result to a semantic theorem
4. **Complete the proof script**: keep the theorem statement and proof term in Lean

Optional external orchestration now lives in separate repos:

- `https://github.com/alerad/leancert-python`
- `https://github.com/alerad/leancert-bridge`

```
External tooling (optional)      Lean
──────                           ────
find_bounds(x²+sin(x), [0,1])
    │
    ▼
{expr: "...", interval: [0,1],   ──▶  checkUpperBound(...) = true
 upper_bound: 2, config: {...}}        │
                                       ▼
                                  verify_upper_bound(...)
                                       │
                                       ▼
                                  ∀ x ∈ [0,1], x² + sin(x) ≤ 2
```

## Real-World Examples

The `examples/` folder contains complete working examples demonstrating LeanCert on real-world problems from various domains.

### Number Theory: √2 (`examples/Sqrt2.lean`)

Proves existence, uniqueness, and arbitrary-precision bounds for √2:

```lean
-- Existence via IVT (sign change)
theorem sqrt2_exists : ∃ x ∈ I12, x * x - 2 = 0 := by
  interval_roots

-- Uniqueness via Newton contraction
theorem sqrt2_unique : ∃! x, x ∈ I12 ∧ x * x - 2 = 0 := by
  interval_unique_root

-- 9 decimal places of precision
theorem sqrt2_9_decimals : ∃ x ∈ ⟨1414213562/1000000000, 1414213563/1000000000, _⟩,
    x * x - 2 = 0 := by
  interval_roots
```

### ML Safety: Neural Network Verification (`examples/NeuralNet.lean`)

Demonstrates interval propagation through neural networks:

```lean
def simpleNet : TwoLayerNet where
  layer1 := ⟨[[1, 1], [1, -1]], [0, 0]⟩
  layer2 := ⟨[[1, 1]], [0]⟩

-- Compute certified output bounds for input region
def outputBounds : IntervalVector :=
  TwoLayerNet.forwardInterval simpleNet inputRegion (-53)
```

### Control Theory: Lyapunov Stability (`examples/Lyapunov.lean`)

Proves energy dissipation for a damped harmonic oscillator:

```lean
-- V̇ = -2ζωₙv² ≤ 0 proves stability
theorem energy_derivative_nonpositive :
    ∀ v ∈ Set.Icc (-1:ℝ) 1, -2/5 * v * v ≤ (0 : ℝ) := by
  -- Split domain to handle dependency problem
  intro v ⟨hlo, hhi⟩
  by_cases h : v ≥ 0
  · have := energy_derivative_on_positive v ⟨h, hhi⟩; linarith
  · have := energy_derivative_on_negative v ⟨hlo, le_of_lt (not_le.mp h)⟩; linarith
```

**Key technique**: Domain splitting to handle the dependency problem (IA computes `v*v` on `[-1,1]` as `[-1,1]` instead of `[0,1]`).

### Finance: Black-Scholes Bounds (`examples/BlackScholes.lean`)

Proves bounds on option pricing components:

```lean
-- Discount factor: e^(-rT) bounds for risk-free rate
theorem discount_factor_lower :
    ∀ r ∈ Set.Icc (-6/100 : ℝ) (-4/100), (94/100 : ℚ) ≤ Real.exp r := by
  certify_bound

-- Log-moneyness for near-ATM options
theorem log_moneyness_upper :
    ∀ x ∈ Set.Icc (9/10 : ℝ) (11/10), Real.log x ≤ (10/100 : ℚ) := by
  certify_bound

-- Gaussian core for vega calculation
theorem gaussian_core_upper :
    ∀ x ∈ Set.Icc (0:ℝ) 2, Real.exp (-x * x / 2) ≤ (1 : ℚ) := by
  certify_bound
```

### Physics: Projectile Motion (`examples/Projectile.lean`)

Proves bounds on projectile dynamics with air resistance:

```lean
-- Drag acceleration: F_drag/m = k·v² ≤ 8.33 m/s²
theorem drag_accel_upper :
    ∀ v ∈ Set.Icc (0:ℝ) 50, 1/300 * v * v ≤ (25/3 : ℚ) := by
  certify_bound

-- Net acceleration with gravity and drag
theorem net_accel_lower :
    ∀ v ∈ Set.Icc (0:ℝ) 50, (7/5 : ℚ) ≤ 49/5 - 1/300 * v * v := by
  certify_bound

-- Exponential velocity decay
theorem exp_decay_lower :
    ∀ t ∈ Set.Icc (-1:ℝ) 0, (36/100 : ℚ) ≤ Real.exp t := by
  certify_bound
```

### Running the Examples

```bash
# Test all examples
for f in examples/*.lean; do lake env lean "$f"; done

# Test a specific example
lake env lean examples/Sqrt2.lean
```

### Lessons Learned

| Issue | Solution |
|-------|----------|
| **Dependency problem** (`v*v` gives `[-1,1]` instead of `[0,1]`) | Split domain and prove separately on `[0,1]` and `[-1,0]` |
| **Rational cast errors** (`(2/5 : ℚ)` in expressions) | Use plain fractions: `2/5` without type annotation |
| **Taylor overflow on wide intervals** (sin/cos) | Use narrower intervals or accept looser bounds |
| **Division has a domain** (`1/x` bounds) | Use a checked evaluator/checker; intervals containing zero are rejected |
| **Discovery command syntax** | Use `#bounds (fun x => ...) on [a, b]` with integer endpoints |
