# LeanCert

[![License](https://img.shields.io/badge/License-Apache%202.0-blue.svg)](LICENSE)
[![Documentation](https://img.shields.io/badge/docs-leancert.io-brightgreen.svg)](https://docs.leancert.io)

Numerical computation produces suggestions. LeanCert produces theorems.

LeanCert is a Lean 4 library for certified numerical reasoning: interval bounds, global optimization, root existence/uniqueness, integration bounds, and exact product-integral certificates with proof-producing tactics.

## Installation

Add to your `lakefile.toml`:

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

## Quick Usage

```lean
import LeanCert.Tactic.IntervalAuto

example : forall x in Set.Icc (0 : Real) 1, Real.exp x <= 3 := by
  certify_bound
```

## Architecture

LeanCert follows a certificate-driven structure:

1. Reification to `LeanCert.Core.Expr`
2. Computation in interval/taylor engines
3. Certification through Golden Theorems

It also includes specialized exact-arithmetic certificate modules such as
`LeanCert.QProduct` for finite q-product/product-integral invariants and
prime-indexed limit bounds.

## Checking Mathlib Compatibility

LeanCert targets the Lean/mathlib version pinned by `lean-toolchain`.

```bash
lake exe check-compat
```

## Split Repositories

This repository is Lean-only.
The former in-repo Python and bridge packaging/workflows were split into
dedicated repositories.

- Python SDK: `https://github.com/alerad/leancert-python`
- Bridge binaries (JSON-RPC executable): `https://github.com/alerad/leancert-bridge`

## License

Apache 2.0. See `LICENSE`.
