# Bounds And Inequalities

Use this path when the goal is a concrete inequality over an interval or box.

Typical goals:

```text
∀ x ∈ I, f x ≤ c
∀ x ∈ I, c ≤ f x
∀ x ∈ I, f x ≤ g x
```
Main tactics and commands:

```text
leancert
certify_bound
multivariate_bound
```
These tactics use the configured certificate-verification route. For example,
`certify_bound (trust := kernel)` is strict and never falls back to
compiler/runtime verification, while `certify_bound (trust := auto)` tries
kernel verification first and reports any native fallback.

For ergonomic raw Lean goals, start with `leancert`. Use `certify_bound` when
you intentionally want the dedicated single-variable interval engine, including
explicit Taylor-depth selection.
Verification mode is independent of the rational, dyadic, or affine backend
chosen by the interval solver.

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
