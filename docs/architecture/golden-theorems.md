# Golden Theorems

LeanCert operates on a **certificate-driven architecture** where computable
checkers run in Lean, and Golden Theorems lift successful checks to semantic
theorems over real numbers.

## Concept

A Golden Theorem bridges the gap between a computable boolean check and a
semantic proposition about real numbers. The checker can be evaluated through
LeanCert's native, kernel, or automatic verification route.

For example, to prove $f(x) \le c$ for all $x \in I$, we use:

$$
\text{checkUpperBound}(e, I, c) = \text{true} \implies \forall x \in I,\ \text{eval}(x, e) \le c
$$

The key insight is that the checker uses computable exact arithmetic, while the
conclusion is a statement about real numbers. The Golden Theorem is
kernel-checked in every route; the route controls how Lean proves that the
checker returned `true`.

## Core Theorems

Golden Theorems are defined across multiple files:
- `Validity/Bounds.lean` - Rational arithmetic (the tactic-level default)
- `Validity/DyadicBounds.lean` - Dyadic arithmetic (fast)
- `Validity/AffineBounds.lean` - Affine arithmetic (tight bounds)
- `Validity/Monotonicity.lean` - Monotonicity via automatic differentiation
- `Validity/Krawczyk.lean` - existence and uniqueness for square systems in the differentiable AD fragment
- `Validity/Algebra.lean` - algebraic root counts and simplicity, complete cubic isolation, and separation meshes
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
#check verify_upper_bound
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
| Polynomial separability | `verify_separable` | `bezoutCheck` |
| Every real polynomial root is simple | `verify_real_roots_simple` | `bezoutCheck` |

```lean
#check verify_sign_change
```
### Global Optimization

| Goal | Theorem | Checker |
|------|---------|---------|
| Global lower bound | `verify_global_lower_bound` | `checkGlobalLowerBound` |
| Global upper bound | `verify_global_upper_bound` | `checkGlobalUpperBound` |

```lean
#check LeanCert.Validity.GlobalOpt.verify_global_lower_bound
```
> **Note**: Global optimization uses `ADSupported` (not `ExprSupportedCore`) and multivariate environments.

### Checked Automatic Differentiation

Checked AD combines support and box-dependent domain validation with interval
dual-number evaluation. A successful result is therefore enough to derive the
semantic derivative statement; callers do not separately prove that reciprocal
arguments exclude zero or logarithm arguments are positive.

| Boundary | Rational arithmetic | Dyadic arithmetic |
|---|---|---|
| One partial | `derivIntervalChecked_correct` | `derivIntervalDyadicChecked_correct` |
| Gradient | `gradientIntervalChecked_correct` | `gradientIntervalDyadicChecked_correct` |
| Rational input converted to Dyadic | — | `derivIntervalDyadicCheckedOfRat_correct`, `gradientIntervalDyadicCheckedOfRat_correct` |
| Differentiability from a successful value-and-derivative call | `evalWithDerivChecked_differentiableAt` | `evalWithDerivDyadicChecked_differentiableAt` |

The Dyadic `OfRat` theorems include the outward input-conversion proof. See
[Checked Automatic Differentiation](../direct/checked-ad.md) for a complete
compiled example and the exact coordinate alignment of gradient results.

### Integration

**Rational backend:**

```lean
#check LeanCert.Validity.Integration.verify_integral_bound
```
**Dyadic backend** (for complex integrands like Li₂ where rational arithmetic explodes):

```lean
#check LeanCert.Validity.IntegrationDyadic.integrateInterval1Dyadic_correct
```
The theorem-level dyadic integration path accepts arbitrary expressions
(including `inv`, `log`, `atanh`) under explicit domain-validity hypotheses.
Public computational endpoints use checked evaluators and return a domain error
instead of exposing finite fallback bounds.

```lean
#check LeanCert.Validity.IntegrationDyadic.integratePartitionDyadic
#check LeanCert.Validity.IntegrationDyadic.integratePartitionDyadicChecked_fst
#check LeanCert.Validity.IntegrationDyadic.integratePartitionDyadicChecked_snd
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
#check verify_finiteIntegral_interval
```
```lean
#check verify_primeLambda_upper
```
Prime-limit lower bounds are intentionally hybrid: the finite arithmetic is
exact, but the lower side needs a mathematical tail proof. The bridge theorem
is:

```lean
#check primeLambda_lower_of_forall
```
The reusable odd-prime tail certificate is:

```lean
#check primeLambda_sandwich
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
#check verify_all_psi_le_mul
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
#check verify_all_theta_rel_error
```
### Analytic Number Theory Bridges

The ANT layer exposes small bridge Golden Theorems that compose with the
Chebyshev engines.

The shared interval helper used by these APIs is:

```lean
#check LeanCert.Cert.verify_rat_interval
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
#check weightedSumRat_eq_abelTransformRat
```
The first Chebyshev-to-Mertens bridge is finite:

```lean
#check verify_mertensLogSum_interval
```
Here `mertensLogSum N` is `∑ p ≤ N, log p / p`, and the checker uses the
existing Chebyshev theta logarithm envelopes.

The bounded Abel bridge has the reusable shape:

```lean
#check verify_abelBound_interval
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
#check LeanCert.Validity.verify_strictly_increasing
```
The approach uses automatic differentiation to compute interval bounds on derivatives:
1. Compute `dI := derivIntervalCore e I cfg` (interval containing all derivatives)
2. If `dI.lo > 0`, then f'(x) > 0 for all x ∈ I, so f is strictly increasing
3. If `dI.hi < 0`, then f'(x) < 0 for all x ∈ I, so f is strictly decreasing

The mathematical foundation is the Mean Value Theorem: if f' has consistent sign, then f is monotonic.

### Domain-aware automatic differentiation

`ADSupported` remains the fast, domain-free fragment.  For expressions that
contain reciprocal or logarithm nodes, use the computable checked API instead:

```text
derivIntervalChecked  : Expr → IntervalEnv → Nat → EvalConfig →
  EvalResult IntervalRat
gradientIntervalChecked : Expr → Box → EvalConfig →
  EvalResult (List IntervalRat)
derivIntervalDyadicChecked : Expr → IntervalDyadicEnv → Nat → DyadicConfig →
  EvalResult IntervalDyadic
gradientIntervalDyadicChecked : Expr → IntervalDyadicEnv → Nat → DyadicConfig →
  EvalResult (List IntervalDyadic)
derivIntervalDyadicCheckedOfRat : Expr → IntervalEnv → Nat → DyadicConfig →
  EvalResult IntervalDyadic
gradientIntervalDyadicCheckedOfRat : Expr → IntervalEnv → Nat → DyadicConfig →
  EvalResult (List IntervalDyadic)
```
The checker recursively validates syntax and the actual input box.  It accepts
`inv e` only when the computed enclosure of `e` excludes zero, and `log e`
only when that enclosure is strictly positive.  Failure is structured data
(`reciprocalContainsZero`, `logNonpositive`, or a nested/unsupported failure),
not a finite fallback interval.

The derivative API's Golden Theorem does not require a separate syntactic
support proof: successful checked computation carries the support and domain
evidence.

```lean
#check derivIntervalChecked_correct
```
`evalWithDerivChecked_differentiableAt` additionally extracts the analytic
differentiability fact certified by the same successful run.  The current
checked fragment is `const`, `var`, `add`, `mul`, `neg`, `sin`, `cos`, `exp`,
`inv`, and `log`; other partial functions are rejected explicitly.

For full gradients, `gradientIntervalChecked_correct` returns a
`List.Forall₂` proof aligning coordinates `0, …, B.length - 1` with their
certified derivative intervals.

The Dyadic variants use the identical checked fragment and failure model while
performing dual addition and multiplication with Dyadic endpoints and outward
rounding at every operation. Their public success condition also certifies that
`cfg.precision ≤ 0`. The corresponding Golden Theorems are
`derivIntervalDyadicChecked_correct` and
`gradientIntervalDyadicChecked_correct`.

**Example:**
```lean
-- Prove exp is strictly increasing on [0, 1]
theorem exp_strictly_increasing :
    StrictMonoOn (fun x => Real.exp x) (Set.Icc 0 1) := by
  have h := LeanCert.Validity.verify_strictly_increasing (Expr.exp (Expr.var 0))
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

### Rational Backend

The Rational backend uses arbitrary-precision rationals. It guarantees exact
intermediate arithmetic but can suffer from denominator explosion on deep
expressions. Backend defaults depend on the entry point: public interval
evaluation uses expression-aware `auto` selection, global optimization selects
Dyadic in `auto` mode, and integration and root finding select Rational. The
semantic `leancert` tactic is a solver portfolio, not a single backend.

See [Interval Backend Selection](backend-selection.md) for the authoritative
operation-by-operation matrix.

### Dyadic Backend

Uses fixed-precision dyadic numbers (m · 2^e) to avoid denominator explosion:

```lean
#check LeanCert.Validity.verify_upper_bound_dyadic
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
#check verify_upper_bound_affine1
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

## Verification Routes

Verification route and arithmetic backend are independent choices. The same
semantic tactic can use rational, dyadic, or affine certificates and then close
the resulting checker equality through one of three routes:

| Route | Equality proof | Trust profile |
|---|---|---|
| `native` | native evaluation | Includes Lean's native compiler trust |
| `kernel` | kernel reduction | No `Lean.ofReduceBool` or `Lean.trustCompiler` |
| `auto` | calibrated choice between the two | Uses kernel reduction only for computations within the configured gates |

Select a route per invocation:

```lean
example : Real.log 5 < 1.61 := by
  interval_decide (trust := kernel)
```

or set the file-level default:

```lean
set_option leancert.trust "kernel"
```

See [Verification Status](verification-status.md) for the exact option syntax,
automatic-route gates, and audit commands.

## The Certificate Workflow

1. **Formulate the goal in Lean**: expression, domain, and target claim
2. **Run the checker**: prove `check... = true` using the selected verification route
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
def sqrtTwoInterval : IntervalRat := ⟨1, 2, by norm_num⟩

def sqrtTwoExpr : Expr :=
  Expr.add (Expr.mul (Expr.var 0) (Expr.var 0)) (Expr.neg (Expr.const 2))

example : ∃ x ∈ sqrtTwoInterval,
    Expr.eval (fun _ => x) sqrtTwoExpr = 0 := by
  unfold sqrtTwoExpr
  interval_roots

example : ∃! x, x ∈ sqrtTwoInterval ∧
    Expr.eval (fun _ => x) sqrtTwoExpr = 0 := by
  unfold sqrtTwoExpr
  interval_unique_root
```

### ML Safety: Neural Network Verification (`examples/NeuralNet.lean`)

Demonstrates interval propagation through neural networks:

```lean
#check LeanCert.ML.Distillation.SequentialNet.forwardInterval
#check LeanCert.ML.Distillation.verify_equivalence
```

### Control Theory: Lyapunov Stability (`examples/Lyapunov.lean`)

Proves energy dissipation for a damped harmonic oscillator:

```lean
example :
    ∀ v ∈ Set.Icc (-1:ℝ) 1, -2/5 * v * v ≤ (0 : ℝ) := by
  intro v ⟨hlo, hhi⟩
  nlinarith [sq_nonneg v]
```

**Key technique**: ordinary interval evaluation treats repeated occurrences
of `v` independently, so `v * v` over `[-1,1]` encloses to `[-1,1]` rather
than the exact range `[0,1]`. Splitting the domain restores the sign
information needed here.

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
  leancert
```

### Physics: Projectile Motion (`examples/Projectile.lean`)

Proves bounds on projectile dynamics with air resistance:

```lean
-- Drag acceleration: F_drag/m = k·v² ≤ 8.33 m/s²
theorem drag_accel_upper :
    ∀ v ∈ Set.Icc (0:ℝ) 50, 1/300 * v * v ≤ (25/3 : ℚ) := by
  leancert

-- Net acceleration with gravity and drag
theorem net_accel_lower :
    ∀ v ∈ Set.Icc (0:ℝ) 50, (7/5 : ℚ) ≤ 49/5 - 1/300 * v * v := by
  leancert

-- Exponential velocity decay
theorem exp_decay_lower :
    ∀ t ∈ Set.Icc (-1:ℝ) 0, (36/100 : ℚ) ≤ Real.exp t := by
  leancert
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
| **Repeated-variable dependency** (`v * v` encloses to `[-1,1]` instead of the exact `[0,1]`) | Split domain and prove separately on `[0,1]` and `[-1,0]` |
| **Rational cast errors** (`(2/5 : ℚ)` in expressions) | Use plain fractions: `2/5` without type annotation |
| **Taylor overflow on wide intervals** (sin/cos) | Use narrower intervals or accept looser bounds |
| **Division has a domain** (`1/x` bounds) | Use a checked evaluator/checker; intervals containing zero are rejected |
| **Discovery command syntax** | Use `#bounds (fun x => ...) on [a, b]` with integer endpoints |
