# LeanCert

[![License](https://img.shields.io/badge/License-Apache%202.0-blue.svg)](LICENSE)
[![Documentation](https://img.shields.io/badge/docs-leancert.io-brightgreen.svg)](https://docs.leancert.io)

**Numerical computation produces suggestions. LeanCert produces theorems.**

LeanCert is a Lean 4 library for certified numerical reasoning. It provides proof-producing tactics and certificate APIs for interval bounds, global optimization, root existence and uniqueness, integration bounds, Chebyshev function certificates, analytic-number-theory finite certificates, exact q-product/product-integral certificates, and neural-network interval verification.

## What LeanCert Provides

* Verified interval bounds for real-valued expressions
* Proof automation for inequalities over intervals
* Root existence and uniqueness tactics
* Exact Bézout certificates for polynomial separability and simple roots
* Global minimum and maximum certificates
* Definite integral bound certificates
* Dyadic and rational arithmetic backends
* Chebyshev `ψ` and `θ` finite-range certificates
* Analytic-number-theory certificates for Abel transforms, Euler products, Dirichlet truncations, Mertens-style sums, and asymptotic envelopes
* Exact q-product/product-integral certificates and prime-limit sandwich bounds
* Neural-network and transformer interval verification tools
* Lean-only workflows, with Python and bridge tooling split into separate repositories

## Installation

Add LeanCert to your `lakefile.toml`:

```toml
[[require]]
name = "leancert"
git = "https://github.com/alerad/leancert"
rev = "main"
```

Then run:

```bash
lake update
```

LeanCert targets the Lean/mathlib version pinned by `lean-toolchain`.

To check compatibility in a larger project:

```bash
lake exe check-compat
```

## Quick Start

Prove a simple bound over an interval:

```lean
import LeanCert.Tactic.IntervalAuto

example : forall x in Set.Icc (0 : Real) 1, Real.exp x <= 3 := by
  certify_bound
```

Use a larger Taylor depth for tighter transcendental bounds:

```lean
import LeanCert.Tactic.IntervalAuto

example : forall x in Set.Icc (0 : Real) 1, Real.exp x <= 2.72 := by
  certify_bound 20
```

Use the dyadic backend for faster verification on deeper expressions:

```lean
import LeanCert.Tactic.DyadicAuto

example : forall x in Set.Icc (0 : Real) 1,
    Real.cos (Real.sin (Real.cos x)) <= 1 := by
  certify_kernel
```

Programmatic interval evaluation uses a single backend selector. `auto` is
Dyadic-first for evaluation and global optimization, while operations that do
not yet have a certified Dyadic implementation (root finding and integration)
use Rational. See [Interval Backend Selection](docs/architecture/backend-selection.md).

```lean
import LeanCert

open LeanCert

def unit : IntervalRat := ⟨0, 1, by norm_num⟩

def preciseDyadic : EvalOptions := {
  backend := .dyadic
  precisionOptions := { dyadicExponent := -80, taylorDepth := 12 }
}

#eval evalInterval (.exp (.var 0)) [unit]
#eval evalInterval (.exp (.var 0)) [unit] { backend := .affine }
#eval evalInterval (.exp (.var 0)) [unit] preciseDyadic
```

`LeanCert.evalInterval_correct` is the backend-independent golden theorem for
every successful result. Domain and configuration failures are returned as
structured `EvalError` values rather than permissive intervals.
Clients needing native results can use `LeanCert.Backend.Rational.eval`,
`LeanCert.Backend.Dyadic.eval`, or `LeanCert.Backend.Affine.eval`; each has a
local `eval_correct` theorem and the same checked failure discipline.

## Discovery Workflow

LeanCert includes editor commands for exploring bounds before committing to a theorem.

```lean
import LeanCert.Discovery.Commands

#bounds (fun x => x^2 + Real.sin x) on [0, 1]
#find_min (fun x => x^2 + Real.sin x) on [0, 1]
#find_max (fun x => Real.exp x - x^2) on [0, 1]
```

Then turn the discovered estimate into a Lean theorem:

```lean
import LeanCert.Tactic.IntervalAuto

example : forall x in Set.Icc (0 : Real) 1,
    x^2 + Real.sin x <= 2 := by
  certify_bound
```

## Root Finding

Prove that a root exists:

```lean
import LeanCert.Tactic.Discovery

example : exists x in Set.Icc (1 : Real) 2, x^2 - 2 = 0 := by
  interval_roots
```

Prove uniqueness using Newton contraction:

```lean
import LeanCert.Tactic.Discovery

example : exists! x in Set.Icc (1 : Real) 2, x^2 - 2 = 0 := by
  interval_unique_root
```

## Choosing a Tactic

| Goal                                       | Tactic                 |
| ------------------------------------------ | ---------------------- |
| `forall x in I, f x <= c`                  | `certify_bound`        |
| `forall x in I, c <= f x`                  | `certify_bound`        |
| Kernel-oriented dyadic bound               | `certify_kernel`       |
| Multivariate bound                         | `multivariate_bound`   |
| Root existence                             | `interval_roots`       |
| Root uniqueness                            | `interval_unique_root` |
| No roots on an interval                    | `root_bound`           |
| Point inequality, such as `Real.pi < 3.15` | `interval_decide`      |
| Counterexample search                      | `interval_refute`      |
| Minimum certificate                        | `interval_minimize`    |
| Maximum certificate                        | `interval_maximize`    |
| Integral bound                             | `interval_integrate`   |
| Expand finite sums                         | `finsum_expand`        |
| Simplify vector indexing                   | `vec_simp`             |

See the full tactics guide in the documentation for examples and troubleshooting.

## Certificate APIs

LeanCert also exposes domain-specific certificate APIs for more structured proofs.

### Chebyshev Certificates

```lean
import LeanCert.Engine.ChebyshevPsi
import LeanCert.Engine.ChebyshevTheta
```

These modules certify finite-range bounds for the Chebyshev functions `ψ` and `θ`.

Example:

```lean
import LeanCert.Engine.ChebyshevPsi

open Chebyshev (psi)
open LeanCert.Engine.ChebyshevPsi

example :
    forall N : Nat, 0 < N -> N <= 20 ->
      psi (N : Real) <= (3 : Real) * N := by
  exact verify_all_psi_le_mul 20 20 3 (by native_decide)
```

### Analytic Number Theory Certificates

```lean
import LeanCert.ANT
import LeanCert.ANT.Asymp
```

The ANT layer includes finite certificates for:

* step sums
* Abel transforms
* Euler and log products
* Dirichlet truncations
* harmonic and prime harmonic sums
* Mertens-style prime sums
* asymptotic main-term/error envelopes
* Stieltjes-Abel and Dirichlet-hyperbola transforms

### QProduct Certificates

```lean
import LeanCert.QProduct
```

`LeanCert.QProduct` certifies exact finite product integrals of the form

```text
F S = ∫ u in 0..1, ∏ n ∈ S, (1 - u^n)
```

by expanding the product into a signed polynomial and integrating exactly over `ℚ`.

Example:

```lean
import LeanCert.QProduct

open LeanCert.QProduct

example : finiteIntegralRat ({2, 3} : Finset Nat) = 7 / 12 := by
  native_decide

example : F ({2, 3} : Finset Nat) = ((7 / 12 : Rat) : Real) := by
  rw [finiteIntegralRat_correct]
  have h : finiteIntegralRat ({2, 3} : Finset Nat) = 7 / 12 := by
    native_decide
  exact_mod_cast h
```

The q-product module also includes prime-indexed limit certificates, including the formal theorem:

```lean
primeLambda_gt_half : (1 : Real) / 2 < primeLambda
```

## Neural Network Verification

```lean
import LeanCert.ML.Network
```

LeanCert includes verified interval propagation and DeepPoly-style relaxations for machine-learning models.

Supported components include:

* dense feedforward layers
* ReLU and sigmoid activations
* GELU
* transformer attention
* layer normalization
* residual connections
* affine arithmetic for tighter layer-normalization bounds
* optimized interval propagation backends

The ML modules are intended for robustness, safety, and model-equivalence verification workflows.

## Architecture

LeanCert follows a certificate-driven architecture:

1. Reify a mathematical expression into `LeanCert.Core.Expr`, or use tactic-level native syntax.
2. Run a computable checker using rational, dyadic, affine, or domain-specific arithmetic.
3. Apply a Golden Theorem that lifts the successful check to a semantic theorem over real numbers.
4. Finish with a short Lean proof script.

In simplified form:

```text
computable certificate data
+ boolean or exact checker
+ Golden Theorem
= theorem over Real
```

This design keeps computation executable while the final claim remains a Lean theorem.

## Verification Status

Most core LeanCert components are fully verified, including:

* fundamental interval arithmetic
* bounds for `exp`, `sin`, `cos`, `log`, `sqrt`, `atan`, `atanh`, `erf`, and related functions
* Taylor-model correctness
* automatic differentiation soundness
* global optimization certificates
* root existence and uniqueness certificates
* rational and dyadic integration certificates
* dyadic interval evaluation
* neural-network interval propagation soundness
* Chebyshev, ANT, and q-product certificate bridges

The documentation contains a detailed verification-status page, including any known proof gaps.

## Documentation

The full documentation is available at:

```text
https://docs.leancert.io
```

Useful starting points:

* Quickstart
* Choosing Tactics
* Tactics Reference
* Discovery Mode
* Troubleshooting
* Certificate Overview
* Golden Theorems
* Verification Status
* Neural Network Verification

## Repository Split

This repository is Lean-only.

The Python SDK and bridge binaries live in separate repositories:

* Python SDK: `https://github.com/alerad/leancert-python`
* Bridge binaries / JSON-RPC executable: `https://github.com/alerad/leancert-bridge`

## License

Apache 2.0. See [`LICENSE`](LICENSE).
