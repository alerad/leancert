# LeanCert

[![Lean Action CI](https://github.com/alerad/leancert/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/alerad/leancert/actions/workflows/lean_action_ci.yml)
[![Soundness Guard](https://github.com/alerad/leancert/actions/workflows/soundness-guard.yml/badge.svg)](https://github.com/alerad/leancert/actions/workflows/soundness-guard.yml)
[![License](https://img.shields.io/badge/License-Apache%202.0-blue.svg)](LICENSE)
[![Documentation](https://img.shields.io/badge/docs-leancert.io-brightgreen.svg)](https://docs.leancert.io)
[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.21681348.svg)](https://doi.org/10.5281/zenodo.21681348)

**Certified numerics for Lean 4.**

LeanCert turns numerical certificates into theorems about real-valued
expressions. Its `leancert` tactic handles point inequalities, quantified
bounds on boxes, root existence and uniqueness, global bounds, finite sums,
and definite integrals. The library also exposes the checked interval,
optimization, root-finding, and integration APIs underneath the tactic.

## Four proofs

```lean
import LeanCert.Tactic

-- A transcendental constant inequality.
example : Real.log 2 < 7 / 10 := by
  leancert

-- One proof covers every real x in the interval.
example : ∀ x ∈ Set.Icc (0 : ℝ) 1,
    Real.exp x * Real.cos x ≤ 3 := by
  leancert

-- Existence and uniqueness, certified by interval and Newton arguments.
example : ∃! x, x ∈ Set.Icc (1 : ℝ) 2 ∧ x ^ 2 - 2 = 0 := by
  leancert

-- Polynomial integrals are normalized and checked exactly over ℚ.
example : (∫ x in (0 : ℝ)..1, x ^ 2) = 1 / 3 := by
  leancert
```

These are ordinary Lean theorems, not tests against sampled floating-point
values. The exact snippets above are compiled in CI.

## Install and prove something

LeanCert currently tracks the Lean and Mathlib versions in
[`lean-toolchain`](lean-toolchain) and [`lakefile.toml`](lakefile.toml). Add it
to a Lake project:

```toml
[[require]]
name = "leancert"
git = "https://github.com/alerad/leancert"
rev = "main"
```

Then update dependencies:

```bash
lake update
```

Create `Main.lean`:

```lean
import LeanCert.Tactic

example : Real.exp 1 < 3 := by
  leancert
```

Check it with:

```bash
lake env lean Main.lean
```

For a reproducible development or release, pin `rev` to a commit or tag rather
than `main`.

## What is actually verified?

LeanCert separates finding a certificate, checking it, and interpreting it.

```text
 goal in Lean
      │
      ▼
 reify expression ──► search for interval/root/integral certificate
                              │
                              │  untrusted candidate data
                              ▼
                    executable certificate checker
                              │
                              │  proof that check = true
                              ▼
                  proved soundness / “golden” theorem
                              │
                              ▼
                       theorem in Lean
```

Search, heuristics, and candidate generation do not need to be trusted: a bad
candidate fails the checker. The checker is connected to the mathematical
claim by proved soundness theorems. CI audits the production golden theorems
for dependencies beyond Lean/Mathlib's standard foundations.

There are two ways to prove the closed proposition `check = true`:

| Mode | Certificate check | Trust added by the generated proof |
| --- | --- | --- |
| `native` (default) | `native_decide` | Lean kernel plus compiler/runtime |
| `kernel` | `decide +kernel` | Lean kernel only; never falls back |
| `auto` | kernel first, native when gated or unsuccessful | Reports native fallback |

Choose the route per proof:

```lean
import LeanCert.Tactic

example : Real.log 2 < 7 / 10 := by
  leancert (trust := kernel)
```

Or set it for a section or file with
`set_option leancert.trust "kernel"`. Numerical backend selection
(Rational/Dyadic/Affine) is independent of this verification choice.

See the authoritative [trust model](https://docs.leancert.io/architecture/trust-model/)
and the compiled [curated showcase](https://docs.leancert.io/showcase/).

## Why not `norm_num`, `positivity`, or a basic interval tactic?

These tools are complementary:

| Tool | Best at | What LeanCert adds |
| --- | --- | --- |
| `norm_num` | Exact normalization of concrete algebraic/numeric goals | Certified enclosures for transcendental expressions and quantified real domains |
| `positivity` | Deriving that an expression is nonnegative or positive | Quantitative upper/lower bounds, not just a sign |
| Basic interval tactics | Propagating enclosures through a supported expression | A semantic front door spanning bounds, subdivision/optimization, roots, sums, and integrals |

LeanCert itself uses ordinary algebraic automation for side conditions. Its
distinctive role is proof-producing numerical search plus a checked
certificate bridge to the final proposition. Run `leancert?` when you want to
see which dedicated solver the router selected.

## What is in the library?

The main verified numerical path includes:

- Rational, Dyadic, and Affine interval evaluation
- Algebraic operations and supported transcendental functions including
  `exp`, `log`, `sin`, `cos`, `sqrt`, `atan`, `atanh`, and `erf`
- Checked automatic differentiation and global bound certificates
- Root existence, exclusion, and Newton-style uniqueness certificates
- Exact rational polynomial integration and certified partition integration
- Domain-specific Chebyshev, analytic-number-theory, q-product, table, and
  neural-network certificate infrastructure

For programmatic use, start with the stable `LeanCert` APIs:

- `LeanCert.evalInterval` and `LeanCert.evalInterval_correct`
- `LeanCert.API.Bounds`
- `LeanCert.API.Optimization`
- the checked AD, root, and integration APIs described in the
  [documentation](https://docs.leancert.io)

## Honest limitations

- `leancert` is automation over a supported expression and goal fragment, not
  a general decision procedure for real analysis.
- Interval dependency and coarse enclosures can make a true tight bound
  inconclusive. Increasing Taylor depth, subdividing, or choosing a dedicated
  tactic may help, but success is not guaranteed.
- Root existence by sign change misses even-multiplicity/tangent roots.
  Uniqueness additionally needs the hypotheses certified by the Newton
  contraction argument.
- Exact integral equality automation is for rational polynomials. Other
  supported integrands use certified partitions and are generally suited to
  inequalities or enclosures rather than symbolic antiderivatives.
- Partial functions require a certified valid domain; for example, logarithm
  intervals must be positive and a denominator interval must exclude zero.
- Kernel verification can be slower or exceed resources on large
  certificates. The faster default native route explicitly adds trust in
  Lean's compiler/runtime.
- Some high-level frameworks require mathematical premises supplied by the
  downstream project. In particular, theorem names in experimental optimized
  ML components should not be read as end-to-end model soundness without
  checking their exact statements.
- The production imports are placeholder-free, but
  `LeanCert.Examples.Li2Bounds` contains two explicitly allowlisted
  compatibility placeholders. Their statements are matched in CI against the
  separately built verified implementation; do not use that lightweight
  interface as a trust-free production dependency.

See [Verification Status](https://docs.leancert.io/architecture/verification-status/),
[Choosing Tactics](https://docs.leancert.io/tactics/choosing-tactics/), and
[Troubleshooting](https://docs.leancert.io/direct/troubleshooting/) for the
full support matrix and audit details.

## Releases and citation

Archived releases are available from Zenodo:

- `v4.32.2.1`: [10.5281/zenodo.21681348](https://doi.org/10.5281/zenodo.21681348)
- `v4.32.1`: [10.5281/zenodo.21633981](https://doi.org/10.5281/zenodo.21633981)

When citing LeanCert, use the DOI for the exact version used in the proof
development.

## License

Apache 2.0. See [`LICENSE`](LICENSE).
