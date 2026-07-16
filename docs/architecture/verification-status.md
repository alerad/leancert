# Verification Status

LeanCert aims for full formal verification in its production/default library.
Legacy examples and prototype interface files are separate from that guarantee
and may contain placeholders while their verified counterparts are developed.

## Production Verification Status

The following production components have complete proofs with no Lean proof
placeholders in the default LeanCert library path:

## Proof Template Verification Status

Proof templates package reusable certificate structure.  Some templates have
executable checkers; others organize proof obligations that must be supplied by
project-specific mathematics.

| Template | Status | Trust boundary |
|---|---|---|
| `TableCert` | Verified generic traversal and row-soundness lifting | Generated rows are untrusted until the row checker succeeds |
| `AsympEnv` | Verified semantic lower/upper envelope consequences and algebra | Projects supply the certificate proof for the underlying summatory estimate |
| `PointwiseEnvelope` | Verified pointwise lower/upper consequences and basic algebra | Projects supply the pointwise error proof on the domain |
| Exact product-integral certificates | Exact rational finite product-integral checkers and soundness theorems | Finite checker data is trusted only through the boolean/exact checker |
| ConstantFactory exact observers | Verified finite observer identity for disjoint base/perturbation data | Disjointness and finite observer checker obligations must be discharged |
| ConstantFactory interval banks | Verified interval observer theorem from kernel-bank correctness | Kernel interval bank correctness is supplied by exact or analytic certificates |
| `ContourShiftCert` | Verified orientation/limit algebra for stable finite residue data | Rectangle identities, residue values, and decay/convergence proofs are supplied by the project |

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

### Strict Partial Evaluators

Application code should use the authoritative checked façade
`LeanCert.evalInterval`, whose successful results are covered by the
backend-independent theorem `LeanCert.evalInterval_correct`. It supports the
Rational, Dyadic, and Affine backends through one structured `EvalResult` API.

The following strict primitives remain useful to backend implementers. Real-
endpoint evaluation exposes only strict `Option` results. Refined evaluation
also provides a total wrapper, but that wrapper requires an `ExprSupported`
proof and obtains its value from the strict evaluator; it has no fallback
branches:

- `evalIntervalReal?`
- `evalIntervalReal1?`
- `evalIntervalReal?_correct`
- `evalIntervalReal1?_correct`
- `evalIntervalRefined?`
- `evalIntervalRefined1?`
- `evalIntervalRefined?_correct`
- `evalIntervalRefined1?_correct`
- `evalIntervalAffine?`
- `evalAffineToInterval?`

These return `none` for unsupported partial operations such as `inv`, `log`, and
`atanh`, so callers cannot accidentally treat a fallback interval as a
certificate. The affine backend still has a legacy total interface; new code
should use its strict variants.

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

### Runtime Optimization Boundary

LeanCert contains optimized candidate implementations for interval
multiplication:

- `IntervalRat.mulFast`
- `IntervalDyadic.mulFast`

These are not attached as native replacements in the production path. Compiled
certificate checks execute the same `mul` definitions that the kernel proofs
reason about. The retained safety-net theorems:

```lean
IntervalRat.mem_mulFast
IntervalDyadic.mem_mulFast
```

prove that the optimized implementations preserve interval containment if they
are used by a future explicitly-audited backend.

### Meta-Level Evaluation Boundary

Some tactics still use Lean meta-level evaluation while elaborating user input or
building diagnostics. Current uses are limited to extracting already-elaborated
certificate data, AST values, intervals, or diagnostic search inputs; final proof
terms are still produced through the relevant certificate soundness theorems.

The shared numeral parser exposes this boundary explicitly:

```lean
LeanCert.Meta.Numeral.unsafeToRatByEval?
```

New proof-producing code should prefer structural parsers such as
`toRatLeaf?`, `toRatFolded?`, and `peelCast?`, and reserve meta-level evaluation
for candidate generation or diagnostics.

## Placeholder Boundary

The default LeanCert library and production import paths are intended to be
placeholder-free. Public Li2 and BKLNW example interfaces now re-export verified
certificate theorems rather than lightweight placeholder theorem bodies. Some
legacy example/prototype files under `LeanCert/Examples` and top-level
`examples` may still contain sketches; these are not production imports.

For production work, prefer the verified heavy certificate files and the default
LeanCert library imports. Do not build downstream formalizations on prototype
example files that advertise placeholder interfaces.

## Auditing Placeholders

The current CI soundness guard checks the production LeanCert tree and excludes
legacy example/test prototype directories. To reproduce the production-style
source scan manually:

```bash
rg -n '^\s*sorry\s*$|sorryAx|mkSorry|admit' LeanCert \
  -g '!LeanCert/Examples/**' \
  -g '!LeanCert/Test/**'
```

The core theorem audit is:

```bash
lake env lean Tests/AxiomAudit.lean
```

These enforce two invariants (both run in CI by `soundness-guard.yml`):

1. **Exact axiom pinning**: the flagship correctness theorems
   (`evalIntervalCore_correct`, `MathConst.mem_interval`, the golden theorems
   for the rational, dyadic, and affine backends, root finding, and certified
   integration) depend on exactly `[propext, Classical.choice, Quot.sound]`,
   checked with `#guard_msgs in #print axioms`.
2. **Whole-library axiom sweep**: a `run_meta` pass walks the entire compiled
   environment and fails if *any* axiom is minted inside the `LeanCert`
   namespace. Each library-internal `native_decide` would mint a
   `<decl>._native.native_decide.ax_*` axiom, so this catches compiler-trust
   creep anywhere in the library — including private lemmas, which
   per-theorem pinning cannot see.

To inspect legacy example placeholders as well, run a repo-wide textual search
over Lean files and review hits manually; documentation comments can mention the
word without introducing a proof placeholder.

## Trust Model: Where `native_decide` Is Allowed

A LeanCert proof has two components with different trust jobs:

```
user's theorem
  = golden_theorem            -- the lift: check = true → semantic Prop
    applied to
    h_check : check ... = true  -- usually by native_decide
```

- **Library theorems (the lifts) are axiom-free.** Every golden theorem and
  every `mem_*`/`*_correct` theorem is proved from the three standard axioms
  only. This is enforced by the audits above; a regression is a CI failure.
- **The certificate check is the one place compiler trust may enter — by the
  user's choice.** Discharging `h_check` with `native_decide` adds exactly one
  per-declaration compiler-trust axiom to *that* proof, visible in its
  `#print axioms`. Users who want a compiler-free proof can discharge the same
  boolean with kernel `decide` where feasible, or re-check it externally; the
  golden theorem applies unchanged.

In short: `native_decide` is the supported engine for *running* certificates,
never a dependency of the theorems that give certificates their *meaning*.

## What This Means

**For typical use cases** (polynomials, `sin`, `cos`, `exp`, `log`, `sqrt`, `atan`, `atanh`, `erf`, optimization, root finding, integration):

> The verification is complete. LeanCert's correctness theorems are accepted by
> the Lean kernel with no axioms beyond standard Mathlib foundations
> (`propext`, `Classical.choice`, `Quot.sound`) — enforced by CI. A proof you
> generate adds at most one compiler-trust axiom, for the `native_decide`
> certificate check you chose to run natively (none, if you use `decide`).

**For the dyadic backend** (neural networks, deep expressions, integration of complex integrands):

> All operations including `atanh` are now fully verified. The dyadic integration path (`IntegrationDyadic.lean`) provides sound integral bounds with 10-50x speedup over rational arithmetic for transcendental-heavy expressions.
