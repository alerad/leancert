# Bounds And Inequalities

For ordinary numerical inequalities, start with [`leancert`](leancert.md).
Use this page when you need the dedicated controls for an interval or box.

Typical goals:

```text
∀ x ∈ I, f x ≤ c
∀ x ∈ I, c ≤ f x
∀ x ∈ I, f x ≤ g x
```
Primary workflow:

```text
leancert
leancert?
```

Advanced controls:

```text
certify_bound
interval_bound_subdiv
multivariate_bound
```
These tactics use the configured certificate-verification route. For example,
`certify_bound (trust := kernel)` is strict and never falls back to
compiler/runtime verification, while `certify_bound (trust := auto)` tries
kernel verification first and reports any native fallback.

For ergonomic raw Lean goals, start with `leancert`. Use `certify_bound` when
you intentionally want the dedicated single-variable interval engine, including
explicit Taylor-depth selection.
`certify_bound` is a numerical portfolio rather than a promise of one fixed
backend: it tries a checked Dyadic path and can fall back to Rational interval
evaluation. Verification mode is independent of that numerical selection.
Subdivision and global optimization are strategies, not backends.

`interval_bound_subdiv depth maxDepth` is transactional: it evaluates
candidate boxes to decide where to split, then closes one fixed Boolean
certificate for each retained leaf. If the configured depth is exhausted or
the expression has a domain obstruction, the original proof state is restored.
`leancert?` reports the configured and deepest depths, boxes examined,
certified leaves, checker, Golden Theorem, and verification usage.

Minimal example:

```lean
import LeanCert.Tactic

example : ∀ x ∈ Set.Icc (0 : ℝ) 1, Real.exp x ≤ 3 := by
  leancert
```

Discovery commands can help find a candidate bound before formalizing it.  See
[Optimization and Discovery](optimization-discovery.md).

For the full tactic reference, see [Reference → Tactics](../reference/tactics.md).

For troubleshooting failed interval proofs, see [Troubleshooting](troubleshooting.md).
