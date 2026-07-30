# CI promises

LeanCert's checks are split by the promise they make. A green workflow has a
specific meaning; it is not one undifferentiated “build passed” signal.

| Tier | Workflow | Local equivalent | Promise |
| --- | --- | --- | --- |
| **Core** | `Core` | `lake build LeanCert DownstreamInterface DownstreamPatterns` | The stable library, isolated public APIs, and downstream compatibility contracts compile. |
| **Functional** | `Functional` | `lake build FunctionalTests` plus the repository Python tests | Every wired regression module and public executable smoke test passes. |
| **Docs** | `Docs` | `python3 scripts/check_docs_snippets.py` and `mkdocs build --strict` | README and canonical documentation snippets compile, links/navigation resolve, and the site builds strictly. |
| **Soundness** | `Soundness Guard` | `lake env lean Tests/AxiomAudit.lean` and `lake env lean Tests/TrustManifest.lean` | Unauthorized axioms, `sorry`, synthetic holes, and changes to the exported trust manifest are rejected. |
| **Showcase** | `Showcase` | `lake build Examples Showcase` | Supported examples and the small announcement-quality success and failure demonstrations compile exactly as published. |
| **Heavy** | `Heavy` | See [Benchmarks](benchmarks.md) and the targets below | Expensive certificates compile and the benchmark surface remains executable. |

All tiers run on pull requests. `Heavy` also runs weekly and on `main`; its
benchmark smoke result is uploaded as a workflow artifact. The committed
baselines remain the reviewable calibration records, while CI artifacts show
that the harness still executes on the current revision.

## Heavy targets

The expensive certificate check is:

```sh
lake build \
  Li2Verified \
  BKLNW_a2_reflective \
  ChebyshevPsiTest \
  ChebyshevThetaTest \
  TableTest
```

The benchmark smoke check is:

```sh
lake build Benchmarks leancert-bench
lake exe leancert-bench \
  --suite smoke --samples 3 --warmups 1 --format jsonl
```

These tiers deliberately separate correctness from timing. Benchmark
regressions do not change whether a checked theorem is accepted by Lean.
