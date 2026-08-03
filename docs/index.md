# LeanCert

LeanCert is a certified numerical-computation system with two first-class
interfaces: a Lean 4 library for proving theorems directly and a Python SDK
for constructing exact claims, orchestrating numerical search, and producing
checked evidence.

| I want to... | Start here |
|---|---|
| Prove numerical theorems in Lean | [Lean quickstart](quickstart.md) |
| Check exact claims from Python | [Python quickstart](python/quickstart.md) |
| Understand what is trusted | [Trust model](architecture/trust-model.md) |
| Rebuild Python-produced evidence independently | [Export and verification](python/evidence/export.md) |

Both interfaces reach LeanCert's checked numerical engines. Python may search
for candidate bounds, cutoffs, or Krawczyk data, but search never authorizes a
successful result: an advertised checker must accept the exact payload.

Downstream packages can register checked enclosure rules for their own unary
real functions without modifying LeanCert's internal expression datatype.

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
| A numerical theorem and I want LeanCert to choose the method | [Direct Automation → Using `leancert`](direct/leancert.md) |
| A concrete inequality over an interval | [Direct Automation → Bounds](direct/bounds.md) |
| A root existence, uniqueness, or no-root claim | [Direct Automation → Roots](direct/roots.md) |
| A global minimum or maximum problem | [Direct Automation → Optimization and Discovery](direct/optimization-discovery.md) |
| A certified partial derivative or gradient enclosure | [Direct Automation → Checked Automatic Differentiation](direct/checked-ad.md) |
| A definite integral bound | [Direct Automation → Integration](direct/integration.md) |
| A bound that should hold for every sufficiently large natural number | [Direct Automation → Eventual Bounds](direct/eventual-bounds.md) |
| A project-specific unary function with its own checked enclosure | [Reference → Downstream Enclosure Extensions](reference/extensions.md) |
| Generated finite rows to verify | [Proof Templates → Table Certificates](proof-templates/table-certificates.md) |
| A summatory function with a main term and error term | [Proof Templates → Asymptotic Envelopes](proof-templates/asymptotic-envelopes.md) |
| A real-variable approximation with an error radius | [Proof Templates → Pointwise Envelopes](proof-templates/pointwise-envelopes.md) |
| A constant built by perturbing a reusable base object | [Proof Templates → ConstantFactory](proof-templates/constant-factory.md) |
| A finite q-product integral | [Proof Templates → Exact Product-Integral Certificates](proof-templates/qproduct-finite-integrals.md) |
| A contour-shift identity | [Proof Templates → Contour Shift](proof-templates/contour-shift.md) |
| A limit enclosed by truncations and computable tails | [Proof Templates → Directed Limits](proof-templates/directed-limits.md) |
| A removable `0/0` singularity controlled by derivative data | [Proof Templates → Wall Quotients](proof-templates/wall-quotients.md) |
| Chebyshev, Abel, Euler-product, Dirichlet, or Mertens certificates | [Domain Libraries → Analytic Number Theory](domains/ant/overview.md) |
| A neural-network or transformer verification problem | [ML Verification](ml/neural-networks.md) |

## Quick Lean Example

```lean
import LeanCert.Tactic

example : ∀ x ∈ Set.Icc (0 : ℝ) 1, Real.sin x ≤ 1 := by
  leancert
```

## Quick Python Example

Install the self-contained SDK wheel and prove a bound without installing Lean:

```bash
pip install leancert
```

```python
import leancert as lc
from leancert import ast

x = ast.var("x")
result = lc.prove(x**2 <= 1, where={x: (0, 1)})

if isinstance(result, lc.Verified):
    print(result.claim_id)
```

The wheel bundles the matching LeanCert Bridge. A verified result retains its
semantic claim identity, checked certificate, and exact build provenance.

## Install

Add LeanCert as a Lake dependency:

```toml
[[require]]
name = "leancert"
git = "https://github.com/alerad/leancert"
rev = "main"
```

For reproducible proofs, pin a tested LeanCert release tag instead of `main`.
Use `main` only when intentionally following unreleased changes.

Then run:

```bash
lake update
```

## Documentation Map

| Section | Description |
|---|---|
| [Getting Started](choosing-interface.md) | Choose Python or Lean, then prove a first claim |
| [Python SDK](python/index.md) | Exact claims, typed outcomes, evidence export, and numerical workflows |
| [Direct Automation](direct/leancert.md) | Start with `leancert`; use dedicated tactics as advanced controls |
| [Proof Templates](proof-templates/overview.md) | Reusable certificate strategies and proof patterns |
| [Domain Libraries](domains/overview.md) | Domain-specific certificate packages |
| [Architecture and Trust](architecture/golden-theorems.md) | Why checkers imply theorems, and what is trusted |
| [Reference](reference/imports.md) | Imports, tactics, and certificate API references |

## LeanCert Repositories

The documentation covers one product family delivered through three
repositories:

- **Core:** [`alerad/leancert`](https://github.com/alerad/leancert) contains
  the Lean definitions, checkers, and soundness theorems.
- **Python SDK:** [`alerad/leancert-python`](https://github.com/alerad/leancert-python)
  contains the semantic Python API, orchestration, result types, and exporters.
- **Bridge:** [`alerad/leancert-bridge`](https://github.com/alerad/leancert-bridge)
  packages the versioned checked interface used by SDK wheels.

Repository separation controls releases and licensing; it does not divide the
user documentation into disconnected products.
