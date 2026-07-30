# Optimization And Discovery

For ordinary extremum and existential-bound goals, start with
[`leancert`](leancert.md). Use this page when you need direct control over
optimization or candidate discovery.

Typical goals:

```text
∃ M, ∀ x ∈ I, f x ≤ M
∀ x ∈ I, m ≤ f x
```
Primary workflow:

```text
leancert
leancert?
```

Advanced controls:

```text
interval_minimize
interval_maximize
```
Programmatic search APIs:

```text
findGlobalMin
findGlobalMax
```
The tactic goals above certify global lower or upper bounds. They do not, by
themselves, state that a bound is attained. Use `interval_argmin` or
`interval_argmax` when the theorem explicitly asks for an optimizing point.

Global optimization and subdivision are strategies, not numerical backends.
The `native`, `kernel`, and `auto` settings control certificate verification,
not the optimization arithmetic. Until runtime telemetry identifies a concrete
backend, a report should describe the selected strategy or backend policy
rather than infer one.

Discovery mode is useful when you do not yet know the bound or extremum.  See
the existing [Discovery Mode](../tactics/discovery.md) reference for command
syntax and examples.
