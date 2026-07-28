# Optimization And Discovery

Use this path when the proof needs a certified global minimum, maximum, or a
candidate bound found by search.

Typical goals:

```lean
∃ M, ∀ x ∈ I, f x ≤ M
∀ x ∈ I, m ≤ f x
```

Tactics:

```lean
interval_minimize
interval_maximize
```

Programmatic search APIs:

```lean
findGlobalMin
findGlobalMax
```

The tactic goals above certify global lower or upper bounds. They do not, by
themselves, state that a bound is attained. Use `interval_argmin` or
`interval_argmax` when the theorem explicitly asks for an optimizing point.

Discovery mode is useful when you do not yet know the bound or extremum.  See
the existing [Discovery Mode](../tactics/discovery.md) reference for command
syntax and examples.
