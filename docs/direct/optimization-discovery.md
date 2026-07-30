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

`leancert?` reports discovery and certification separately. Discovery reports
the iterations actually used, final certified gap, tolerance, and remaining
boxes from the retained optimizer run. Certification reports the checker,
Golden Theorem, and verification route used to close the bound. The optimizer
and checker are not rerun to produce this report. For a direct `opt_bound`
certificate, only configured limits are reported because that checked API does
not expose an execution trace.

A gap larger than the configured tolerance is reported as
`Within requested tolerance: false`. It does not invalidate an existential
bound: the discovered witness is still accepted only after its bound is
independently certified. The tolerance measures discovery quality, not proof
soundness or tactic success.

Discovery mode is useful when you do not yet know the bound or extremum.  See
the existing [Discovery Mode](../tactics/discovery.md) reference for command
syntax and examples.
