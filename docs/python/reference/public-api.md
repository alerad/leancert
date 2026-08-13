# Python Public API

This inventory is organized by authority rather than presenting every package
attribute as equally stable.

## Semantic proving

Use these for new proof-oriented code:

- `leancert.prove`;
- `ProveConfig`, `SystemRootConfig`, `EventualConfig`, and `IntegralConfig`;
- `leancert.ast` claim, expression, domain, encoding, digest, and validation APIs;
- typed outcomes including `Verified`, `Rejected`, `Inconclusive`,
  `Unsupported`, `DomainObstruction`, `VerifiedSystemRoot`, and
  `VerifiedEventualBound`, `VerifiedRootExistence`, `VerifiedUniqueRoot`,
  `VerifiedRootExclusion`, `VerifiedIntegralEquality`, and
  `VerifiedIntegralBound`; and
- `Verified*.export_lean_project()`.

## Programmatic numerical toolkit

The context-managed `leancert.Solver` exposes checked numerical operations and
legacy compatibility workflows:

- `eval_interval`, `find_bounds`, `verify_bound`, `verify_bound_or_raise`;
- `find_roots`, `find_unique_root`, `integrate`;
- `compute_lipschitz_bound`, `diagnose_bound_failure`; and
- adaptive verification and witness synthesis.

See [Solver Toolkit](solver.md) and [Result Types](results.md).

## Evidence and installation

- `verify_exported_projects`, `discover_exported_projects`;
- `diagnose`, `DoctorReport`, `DoctorCheck`; and
- `leancert doctor` and `leancert verify`.

## Modeling and ML helpers

- legacy expressions such as `var`, `sin`, `cos`, `exp`, and `log`;
- `Interval`, `Box`, `normalize_domain`, and `to_fraction`;
- `simplify` and `expand`; and
- network types plus `forward_interval` and `verify_nn_bounds`.

Quantifier synthesis, adaptive internals, and bug-report triage are publicly
callable but experimental. Import less-prominent helpers from their defining
modules rather than relying on incidental root-package attributes. The
presence of a name on `leancert` is not itself a proof-authority claim.

The Lean-facing API is documented separately under
[Supported Public API](../../reference/public-api.md).
