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

See [Supported Public API](../reference/public-api.md) for the exact boundary.

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
- Remove superseded internal names when their callers migrate; public additions
  should have one canonical owner from the start.

## Downstream enclosure extensions

Unary real enclosure rules defined outside LeanCert register through
`LeanCert.Tactic.Extension`. A registration stores declaration metadata in a
persistent environment extension; it must not add downstream functions to
`LeanCert.Core.Expr` or hard-code them in the router.

The candidate generator is untrusted and returns
`Except EnclosureCandidateFailure IntervalRat`. The registered checker and
soundness theorem are the checked boundary. The attribute validates the exact
theorem schema and rejects definitions, axioms, and theorems depending on
`sorry`. Keep registry construction independent of the semantic router so
downstream packages can declare rules through a lightweight import.

Execution of a registered rule is a tactic strategy and therefore follows the
typed transactional requirements below. When registered calls occur inside an
ordinary supported expression, execution first produces a membership proof for
each maximal registered subterm. Those results become proof-carrying variables
in a separately reified core expression; `evalIntervalCore_correct` composes
their enclosures. Do not splice unchecked candidate values directly into a
semantic bridge.

Adaptive execution retries only typed rejected or inconclusive results. Each
retained child is a complete theorem over its child interval, and a generic
predicate-level bisection theorem combines the children. Domain obstructions,
unsupported syntax, and verification failures remain terminal. Failed or
exhausted recursion must restore the complete caller tactic state.

## Tactic changes

Every semantic-router extension returns
`Except AttemptFailure SolverExecution`. Expected unsupported inputs,
rejections, domain obstructions, and exhausted searches must not use
exceptions. Strategy, numerical backend, and verification route are separate
concepts. Failed speculative attempts must restore the complete tactic state
and must not leak proof assignments or telemetry. Prefer typed identifiers over
matching user-facing display text.

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
