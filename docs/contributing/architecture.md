# Contributor architecture

LeanCert is organized by responsibility. Put a declaration in the narrowest
layer that owns its contract rather than in whichever module is most
convenient to import.

| Layer | Owns | Stability |
| --- | --- | --- |
| `LeanCert/Core` | mathematical datatypes, expressions, intervals, and foundational definitions | internal foundation |
| `LeanCert/Engine` | checked evaluators, certificate checkers, and Golden Theorems | advanced; selected APIs are re-exported |
| `LeanCert/API` | stable checked programmatic entry points | stable |
| `LeanCert/Tactic` | `leancert`, dedicated tactics, routing, diagnostics, and proof construction | stable front door; internals may evolve |
| `LeanCert/CertifiedBounds` | reusable, named certified numerical results | stable |
| `LeanCert/ANT`, `LeanCert/QProduct` | supported domain umbrellas | stable |
| `LeanCert/Examples` | demonstrations and showcase material | examples, not declaration ownership |
| `LeanCert/Test` | regression, protocol, import-isolation, and public-message tests | test-only |
| `LeanCert/Benchmark` | compiled benchmark runner | measurement-only |

## Public and internal imports

Downstream developments should begin with `LeanCert`, `LeanCert.Tactic`, a
`LeanCert.API.*` module, `LeanCert.CertifiedBounds`, or a documented domain
umbrella. Direct `LeanCert.Engine.*` imports are appropriate for expert
extension work, but do not carry a general source-compatibility promise.

See [Supported Public API](../reference/public-api.md) for the exact boundary
and [Compatibility surfaces](../reference/compatibility.md) for forwarding
imports retained for downstream users.

## Where new work belongs

- Add a checked numerical primitive and its correctness theorem under
  `Engine`, then expose a stable wrapper through `API` only when its contract
  is ready.
- Add reusable pre-certified facts under `CertifiedBounds`, not `Examples`.
- Add presentation examples under `LeanCert/Examples` and wire supported ones
  into the `Examples` or `Showcase` Lake target.
- Add every test module to `FunctionalTests`; `scripts/check_test_wiring.py`
  rejects unwired test files.
- Keep benchmarks out of correctness tests and register reusable workloads
  with the compiled benchmark runner.
- Preserve deprecated names through a small forwarding module or alias with a
  documented canonical replacement.

## Tactic changes

The semantic router should return proof-bearing results and structured
execution metadata. Strategy, numerical backend, and verification route are
separate concepts. Failed speculative attempts must not leak proof state or
telemetry. Prefer typed identifiers over matching user-facing display text.

Changes to a router path should normally include:

1. a protocol or structural report test;
2. a successful public tactic example;
3. a representative failure diagnostic;
4. trust-mode coverage when a Boolean certificate is closed;
5. compilation of every proof recipe printed to the user.

## Validation

The [CI promises](../architecture/ci-promises.md) page maps each workflow to
its local command. Run the smallest relevant tier while developing, then the
complete affected tiers before opening a pull request. Changes to proof
boundaries or native verification also require the soundness tier.
