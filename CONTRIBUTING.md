# Contributing to LeanCert

Thank you for helping improve LeanCert. Start with the
[contributor architecture guide](docs/contributing/architecture.md), which
explains module ownership, supported public boundaries, test placement, and
the CI tiers.

The usual local checks are:

```sh
lake build LeanCert LeanCert.Tactic
lake build FunctionalTests
lake build Examples Showcase
python3 scripts/check_docs_snippets.py
mkdocs build --strict
```

Run the soundness checks when changing theorem boundaries, verification, or
generated proofs:

```sh
lake env lean Tests/AxiomAudit.lean
lake env lean Tests/TrustManifest.lean
```

Performance changes should include the relevant command and environment
metadata described in the
[benchmark guide](docs/architecture/benchmarks.md). Expensive certificate and
benchmark jobs also run in the `Heavy` GitHub Actions workflow.
