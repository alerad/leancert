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
These tactics use the configured certificate-verification route independently
of their numerical backend. See the [Trust model](../architecture/trust-model.md)
and [Backend selection](../architecture/backend-selection.md) for those two
axes.

For ergonomic raw Lean goals, start with `leancert`. Use `certify_bound` when
you intentionally want the dedicated single-variable interval engine, including
explicit Taylor-depth selection.
`certify_bound` is a numerical portfolio rather than a promise of one fixed
backend. Subdivision and global optimization are strategies, not backends.

`interval_bound_subdiv depth maxDepth` splits candidate boxes and certifies
every retained leaf. `leancert?` reports its configured and deepest depths,
boxes examined, certified leaves, and verification usage. See the
[verification-status table](../architecture/verification-status.md) for the
precise checker boundary and failure semantics.

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
