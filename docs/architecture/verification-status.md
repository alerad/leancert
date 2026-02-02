# Verification Status

LeanCert aims for full formal verification. This page documents what is **fully proved** versus what contains `sorry` (unfinished proofs).

## Fully Verified

The following components have complete proofs with no `sorry`:

### Interval Arithmetic (FTIA)

The Fundamental Theorem of Interval Arithmetic is proved for all basic operations:

- Addition, subtraction: $x \in I_1, y \in I_2 \implies x + y \in I_1 + I_2$
- Multiplication: $x \in I_1, y \in I_2 \implies x \cdot y \in I_1 \cdot I_2$
- Division: $x \in I_1, y \in I_2, 0 \notin I_2 \implies x / y \in I_1 / I_2$
- Power: $x \in I \implies x^n \in I^n$

### Transcendental Functions

Rigorous bounds via Taylor series with verified remainder terms:

| Function | Theorem | Location |
|----------|---------|----------|
| $e^x$ | `mem_expInterval` | `Core/IntervalReal.lean` |
| $\sin x$ | `mem_sinInterval` | `Core/IntervalReal.lean` |
| $\cos x$ | `mem_cosInterval` | `Core/IntervalReal.lean` |
| $\log x$ | `mem_logInterval` | `Core/IntervalReal.lean` |
| $\sinh x$ | `mem_sinhInterval` | `Core/IntervalReal.lean` |
| $\cosh x$ | `mem_coshInterval` | `Core/IntervalReal.lean` |
| $\tanh x$ | `mem_tanhInterval` | `Core/IntervalReal.lean` |
| $\arctan x$ | `mem_atanInterval` | `Engine/Eval/Core.lean` |
| $\text{arsinh}(x)$ | `mem_arsinhInterval` | `Engine/Eval/Core.lean` |
| $\text{atanh}(x)$ | `mem_atanhInterval` | `Engine/Eval/Core.lean` |
| $\sqrt{x}$ | `mem_sqrtIntervalTight` | `Core/IntervalRat/Transcendental.lean` |
| $\text{erf}(x)$ | `mem_erfInterval` | `Engine/Eval/Core.lean` |
| $\text{sinc}(x)$ | `sinc_evalSet_correct` | `Engine/TaylorModel/Trig.lean` |

### Extended Interval Arithmetic

Standard interval arithmetic fails when dividing by an interval containing zero. LeanCert's **Extended Arithmetic** returns a union of intervals, preserving soundness even across singularities.

- **Theorem**: `evalExtended_correct_core`
- **Behavior**: 1 / [-1, 1] → (-∞, -1] ∪ [1, ∞)
- **Status**: Verified for core expressions

This enables robust handling of expressions like 1/x near x = 0.

### Taylor Series

The core Taylor remainder bounds are fully proved:

```lean
theorem taylor_remainder_bound (f : ℝ → ℝ) (n : ℕ) (a x : ℝ) ...
```

This is the foundation for all transcendental function bounds.

### Taylor Models

Taylor Models combine polynomial approximation with rigorous remainder bounds. The `fromExpr?` function in `Engine/TaylorModel/Expr.lean` converts expressions to verified Taylor Models.

**All functions are now fully enabled:**

| Function | Status | Theorem |
|----------|--------|---------|
| `exp`, `log` | ✅ Verified | `tmExp_correct`, `tmLog_correct` |
| `sin`, `cos` | ✅ Verified | `tmSin_correct`, `tmCos_correct` |
| `sinh`, `cosh`, `tanh` | ✅ Verified | `sinh_evalSet_correct`, etc. |
| `atan` | ✅ Verified | `mem_atanInterval` (interval-based) |
| `arsinh`, `atanh` | ✅ Verified | `tmAsinh_correct`, `atanh_evalSet_correct` |
| `sqrt` | ✅ Verified | `mem_sqrtIntervalTight` (interval-based) |
| `erf` | ✅ Verified | `mem_erfInterval` (interval-based) |
| `sinc` | ✅ Verified | `sinc_evalSet_correct` |

The main correctness theorem `fromExpr_evalSet_correct` proves that for any supported expression, the Taylor Model's evaluation set contains the true function value.

### Automatic Differentiation

Forward-mode AD with verified value and derivative bounds:

- `evalDual_val_correct`: Value component is correct
- `evalDual_der_correct`: Derivative component is correct

### Global Optimization

Branch-and-bound with formal guarantees:

- `globalMinimize_lo_correct`: Lower bound is valid
- `globalMaximize_hi_correct`: Upper bound is valid

### Root Finding

- **Bisection**: `verify_sign_change` proves existence via IVT
- **Newton**: `verify_unique_root_core` proves uniqueness via contraction

### Integration

- `integrateInterval_correct`: Riemann sum bounds contain the true integral (general n partitions)
- `integrateAdaptive_correct`: Adaptive integration with error-driven subdivision
- Both rational and dyadic backends are fully verified (see Dyadic Integration below)

### Dyadic Backend

The high-performance dyadic interval evaluator is fully verified:

- `evalIntervalDyadic_correct`: Dyadic evaluation produces sound intervals for `ExprSupportedCore`
- `evalIntervalDyadic_correct_withInv`: Extended correctness for `ExprSupportedWithInv` (includes `inv`, `log`, `atan`, `arsinh`, `atanh`, `sinc`, `erf`)
- `IntervalDyadic.mem_add`, `mem_mul`, `mem_neg`: FTIA for dyadic operations
- `IntervalDyadic.roundOut_contains`: Outward rounding preserves containment
- `atanhComputable` / `mem_atanhComputable`: Computable atanh interval via Taylor series endpoint evaluation

The dyadic backend avoids rational denominator explosion by using fixed-precision arithmetic:

| Expression | Rational Denominator | Dyadic Mantissa |
|------------|---------------------|-----------------|
| `exp(exp(x))` | ~200 digits | 17 digits |
| `exp(exp(exp(x)))` | ~2000 digits | 18 digits |

See `LeanCert/Test/BenchmarkBackends.lean` for performance comparisons.

### Dyadic Integration

High-performance integration using the dyadic backend, enabling verified integral bounds for complex expressions where rational arithmetic would be prohibitively slow:

- `integrateInterval1Dyadic_correct`: Single-interval dyadic integration correctness
- `integratePartitionDyadic_correct`: Partition-based dyadic integration with uniform partitioning
- `integratePartitionDyadic_bound_correct`: Upper/lower bound extraction from partition results

The dyadic integration module (`Validity/IntegrationDyadic.lean`) is a drop-in replacement for rational `integratePartitionWithInv` that uses `evalIntervalDyadic` instead of `evalInterval?`. Since `evalIntervalDyadic` is total (returns wide bounds on domain violations rather than `none`), the integration functions are also total — domain violations manifest as wide bounds that cause the checker to return `false`, which is safe for the `native_decide` workflow.

### Bernstein Polynomial Enclosure

Tight polynomial bounds via verified Bernstein basis conversion (`Engine/TaylorModel/Core.lean`):

- `boundPolyBernstein_correct`: Main enclosure theorem — polynomial values on an interval are contained in the min/max of Bernstein coefficients
- `bernstein_partition_of_unity`: Bernstein basis functions sum to 1
- `bernstein_nonneg`: Bernstein basis functions are nonneg on [0, 1]
- `monomial_bernstein_expansion`: Monomial-to-Bernstein conversion identity

This enables tighter polynomial range bounds than naive interval evaluation, which is critical for Taylor model remainder estimation.

### Computable Polynomial Taylor Models

Dyadic polynomial Taylor models (`Engine/CompPoly.lean`) avoiding rational coefficient explosion:

- `DyPoly`: Polynomial with `Dyadic` coefficients
- `DyTM`: Taylor model combining `DyPoly` + `IntervalDyadic` remainder
- Computable evaluation and integration operations using fixed-precision arithmetic throughout

### Neural Network Verification

The ML module provides verified interval propagation for neural networks:

- `mem_forwardInterval`: Soundness of dense layer propagation
- `mem_relu`, `mem_sigmoid`: Activation function soundness
- `relu_relaxation_sound`: DeepPoly ReLU triangle relaxation
- `sigmoid_relaxation_sound`: DeepPoly sigmoid monotonicity bounds

**Transformer Components:**

- `mem_scaledDotProductAttention`: Soundness of Q×K^T + Softmax + V
- `mem_layerNormInterval`: Soundness of Layer Normalization
- `mem_geluInterval`: Soundness of GELU activation
- `forwardQuantized_sound`: Soundness of integer-quantized split-sign inference

See `LeanCert/ML/` for the full implementation.

### Kernel Verification (Dyadic)

Bridge theorems for kernel-level verification via `decide`:

- `verify_upper_bound_dyadic`: Connects Dyadic boolean check to Real semantic bounds
- `verify_lower_bound_dyadic`: Lower bound variant
- `evalIntervalDyadic_correct`: Dyadic evaluation is sound w.r.t Real operations

These enable the `certify_kernel` tactic to produce proofs verified purely by the Lean kernel, removing the compiler from the trusted computing base.

## Incomplete (Contains `sorry`)

These features work computationally but have gaps in formal proofs:

| Component | Issue | Impact |
|-----------|-------|--------|
| `sinc` derivative bound | `sinc_deriv_bound` for n≥2 | Very Low - only affects Taylor precision for sinc |

The `sinc_deriv_bound` lemma bounds higher derivatives of sinc for Taylor remainder estimation. The proof requires Leibniz rule under the integral (sinc(x) = ∫₀¹ cos(tx) dt), which is deferred. The interval-based sinc evaluation still works correctly.

## Finding Sorries

To audit the codebase yourself:

```bash
grep -r "sorry" --include="*.lean" LeanCert/ | grep -v "no sorry"
```

Current count: **0 declarations** using `sorry` in the default build target. The examples directory contains deliberate `sorry`s for downstream API ergonomics (e.g., `Li2Bounds.lean` provides sorry'd lemmas alongside verified proofs in `Li2Verified.lean`).

## What This Means

**For typical use cases** (polynomials, `sin`, `cos`, `exp`, `log`, `sqrt`, `atan`, `atanh`, `erf`, optimization, root finding, integration):

> The verification is complete. Proofs generated by LeanCert are accepted by the Lean kernel with no axioms beyond standard Mathlib foundations.

**For the dyadic backend** (neural networks, deep expressions, integration of complex integrands):

> All operations including `atanh` are now fully verified. The dyadic integration path (`IntegrationDyadic.lean`) provides sound integral bounds with 10-50x speedup over rational arithmetic for transcendental-heavy expressions.
