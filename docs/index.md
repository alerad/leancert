# LeanCert

LeanCert is a Lean 4 library for certified numerical computation and proof-producing tactics.

## What You Get

- Verified interval bounds
- Proof automation for inequalities and root claims
- Global optimization and integration certificates
- Chebyshev function certificates
- Analytic-number-theory certificate bridges for Abel summation, Euler products, prime-power extensionality, and explicit-PNT envelope transfers
- Exact q-product/product-integral certificates
- Table, slab, and contour-shift certificate frameworks
- Dyadic and rational backends for different performance/precision tradeoffs

## Quick Lean Example

```lean
import LeanCert.Tactic.IntervalAuto

example : forall x in Set.Icc (0 : Real) 1, Real.sin x <= 1 := by
  certify_bound
```

## Install

Add LeanCert as a Lake dependency:

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

## Documentation Map

| Guide | Description |
|-------|-------------|
| [Quickstart](quickstart.md) | First Lean proofs with LeanCert |

## Tactics

| Guide | Description |
|-------|-------------|
| [Choosing Tactics](tactics/choosing-tactics.md) | Pick the right tactic quickly |
| [Tactics Reference](tactics/tactics.md) | Main proving tactics |
| [Discovery Mode](tactics/discovery.md) | Explore bounds and extrema interactively |
| [Troubleshooting](tactics/troubleshooting.md) | Common failures and fixes |
| [End-to-End Example](tactics/end-to-end-example.md) | Discovery to theorem workflow |

## Certificate APIs

| Guide | Description |
|-------|-------------|
| [Certificate Overview](certificates/overview.md) | Domain-specific certificate families |
| [Chebyshev Certificates](certificates/chebyshev.md) | Certified `ψ` and `θ` finite-range bounds |
| [ANT Certificates](certificates/ant.md) | Step sums, Abel transforms, Euler products, and Mertens-style finite sums |
| [Asymptotic Envelopes](certificates/ant-asymp.md) | Summatory and pointwise error envelopes, slab inequalities, Stieltjes transforms, and hyperbola kernels |
| [QProduct Certificates](certificates/qproduct.md) | Exact product-integral and prime-limit certificates |
| [ConstantFactory Certificates](certificates/constants.md) | Observer-generated q-product constants from finite perturbation sums |
| [Contour-Shift Certificates](certificates/contour-shift.md) | Rectangle, horizontal-vanishing, and limit-passing contour-shift certificates |

## ML

| Guide | Description |
|-------|-------------|
| [Neural Networks](ml/neural-networks.md) | Neural network interval verification |
| [Distillation](ml/distillation.md) | Distillation and model-certificate workflows |

## Architecture

| Document | Description |
|----------|-------------|
| [Golden Theorems](architecture/golden-theorems.md) | Why the checkers imply theorems |
| [Table Certificates](architecture/table-certificates.md) | Generic finite-table checking infrastructure |
| [Root Finding](architecture/root-finding.md) | Existence and uniqueness flow |
| [Verification Status](architecture/verification-status.md) | Proven components and known gaps |

## Split Repositories

This repo is Lean-only.
The Python package and bridge release pipeline were moved out of this repo.

- Python SDK: `https://github.com/alerad/leancert-python`
- Bridge binaries: `https://github.com/alerad/leancert-bridge`
