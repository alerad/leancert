# LeanCert

LeanCert is a Lean 4 library for certified numerical computation and
proof-producing certificate workflows.

Downstream users should begin with the [supported public API](reference/public-api.md).

LeanCert is organized around proof intent:

1. **Direct automation** closes concrete bounds, roots, optimizations, and
   integral goals over explicit expressions.
2. **Proof templates** package reusable certificate strategies such as table
   checking, main-term/error envelopes, perturbation observers, product-integral
   identities, and contour-shift bookkeeping.
3. **Domain libraries** provide specialized mathematics, especially analytic
   number theory and q-product certificates, built on top of the templates.
4. **Architecture and trust** explains checkers, Golden Theorems, arithmetic
   backends, and verification status.

## What Kind Of Proof Are You Building?

| I have... | Go to |
|---|---|
| A concrete inequality over an interval | [Direct Automation → Bounds](direct/bounds.md) |
| A root existence, uniqueness, or no-root claim | [Direct Automation → Roots](direct/roots.md) |
| A global minimum or maximum problem | [Direct Automation → Optimization and Discovery](direct/optimization-discovery.md) |
| A certified partial derivative or gradient enclosure | [Direct Automation → Checked Automatic Differentiation](direct/checked-ad.md) |
| A definite integral bound | [Direct Automation → Integration](direct/integration.md) |
| Generated finite rows to verify | [Proof Templates → Table Certificates](proof-templates/table-certificates.md) |
| A summatory function with a main term and error term | [Proof Templates → Asymptotic Envelopes](proof-templates/asymptotic-envelopes.md) |
| A real-variable approximation with an error radius | [Proof Templates → Pointwise Envelopes](proof-templates/pointwise-envelopes.md) |
| A constant built by perturbing a reusable base object | [Proof Templates → ConstantFactory](proof-templates/constant-factory.md) |
| A finite q-product integral | [Proof Templates → Exact Product-Integral Certificates](proof-templates/qproduct-finite-integrals.md) |
| A contour-shift identity | [Proof Templates → Contour Shift](proof-templates/contour-shift.md) |
| Chebyshev, Abel, Euler-product, Dirichlet, or Mertens certificates | [Domain Libraries → Analytic Number Theory](domains/ant/overview.md) |
| A neural-network or transformer verification problem | [ML Verification](ml/neural-networks.md) |

## Quick Lean Example

```lean
import LeanCert.Tactic

example : forall x in Set.Icc (0 : Real) 1, Real.sin x <= 1 := by
  leancert
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

| Section | Description |
|---|---|
| [Getting Started](choosing-proof-shape.md) | Choose the right proof path before selecting modules |
| [Direct Automation](direct/bounds.md) | Tactics and commands for direct numeric goals |
| [Proof Templates](proof-templates/overview.md) | Reusable certificate strategies and proof patterns |
| [Domain Libraries](domains/overview.md) | Domain-specific certificate packages |
| [Architecture and Trust](architecture/golden-theorems.md) | Why checkers imply theorems, and what is trusted |
| [Reference](reference/imports.md) | Imports, tactics, and certificate API references |

## Split Repositories

This repo is Lean-only.
The Python package and bridge release pipeline were moved out of this repo.

- Python SDK: `https://github.com/alerad/leancert-python`
- Bridge binaries: `https://github.com/alerad/leancert-bridge`
