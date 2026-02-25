# LeanCert

LeanCert is a Lean 4 library for certified numerical computation and proof-producing tactics.

## What You Get

- Verified interval bounds
- Proof automation for inequalities and root claims
- Global optimization and integration certificates
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
| [Discovery Mode](discovery.md) | Explore bounds and extrema interactively |
| [Tactics Reference](tactics.md) | Main proving tactics |
| [Choosing Tactics](choosing-tactics.md) | Pick the right tactic quickly |
| [End-to-End Example](end-to-end-example.md) | Discovery to theorem workflow |

## Architecture

| Document | Description |
|----------|-------------|
| [Golden Theorems](architecture/golden-theorems.md) | Why the checkers imply theorems |
| [Root Finding](architecture/root-finding.md) | Existence and uniqueness flow |
| [Verification Status](architecture/verification-status.md) | Proven components and known gaps |

## Split Repositories

This repo is Lean-only.
The Python package and bridge release pipeline were moved out of this repo.

- Python SDK: `https://github.com/alerad/leancert-python`
- Bridge binaries: `https://github.com/alerad/leancert-bridge`
