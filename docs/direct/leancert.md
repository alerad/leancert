# Using `leancert`

`leancert` is LeanCert's primary interface for numerical proofs. State the
mathematical theorem in ordinary Lean syntax and start with:

```lean
import LeanCert.Tactic

example : Real.log 2 < 7 / 10 := by
  leancert

example : ∀ x ∈ Set.Icc (0 : ℝ) 1, x ^ 2 ≤ 1 := by
  leancert
```

The tactic recognizes the semantic shape of the goal, selects a bounded
portfolio of certified strategies, and accepts only a proof term that has been
validated against the original goal. It is silent when it succeeds.

## Inspecting a proof

Use `leancert?` when you want to inspect a successful strategy:

```lean
import LeanCert.Tactic

example : ∃ x ∈ Set.Icc (1 : ℝ) 2, x ^ 2 = 2 := by
  leancert?
```

It proves the same goal as `leancert` and reports the recognized theorem shape,
winning strategy, numerical computation, certificate checker and verifier, and
effective verification route. Static backend policy and observed runtime
metadata remain distinct; reports never infer a checker, verifier, or backend
that the winning strategy did not retain.

When ordinary `leancert` does not close a goal, retrying with `leancert?`
requests the detailed diagnosis and attempted-strategy ledger. Enable the
router and solver traces when filing an internal-error report or when the
public diagnosis does not expose enough implementation detail:

```lean
set_option trace.LeanCert.router true in
set_option trace.LeanCert.solver true in
example : Real.log 2 < 7 / 10 := by
  leancert
```

For certificate-route decisions, use:

```lean
set_option trace.leancert.verification true in
example : Real.log 2 < 7 / 10 := by
  leancert (trust := auto)
```

## Recognized theorem shapes

The router currently recognizes:

- closed point inequalities;
- universally quantified univariate interval bounds;
- multivariate bounds over interval boxes;
- root existence, uniqueness, and exclusion;
- existential lower and upper bounds;
- attained minima and maxima;
- finite-sum equalities and inequalities;
- exact rational-polynomial integral equalities;
- supported definite-integral inequalities through one retained partition
  search followed by a fixed-candidate certificate;
- fixed-cutoff and existential eventual upper bounds for supported
  reciprocal-power tails over `Nat`;
- closed LeanCert Boolean checker propositions;
- conjunctions whose children are themselves recognized.

The parser accepts interval membership and root or optimizer predicates in
either conjunction order. Comparisons in which both sides depend on the
quantified variables are normalized to a difference bound and transported back
to the user's theorem.

## Router options

`leancert` and `leancert?` accept the same inline options:

```lean
import LeanCert.Tactic

example : ∀ x ∈ Set.Icc (0 : ℝ) 1, x * (1 - x) ≤ (27 / 100 : ℚ) := by
  leancert (budget := 6) (taylorDepth := 10) (subdivisions := 8)
    (maxIterations := 1000) (trust := auto)
```

| Option | Default | Meaning |
| --- | ---: | --- |
| `budget` | `6` | Maximum cumulative portfolio cost; it is not Lean's heartbeat limit |
| `taylorDepth` | `10` | Initial Taylor-model depth passed to numerical strategies |
| `subdivisions` | `4` | Maximum bisection depth for subdivision |
| `maxIterations` | `1000` | Iteration limit for global-optimization strategies |
| `trust` | project option | Certificate-verification policy: `kernel`, `native`, or `auto` |

An inline `trust` value overrides `set_option leancert.trust`. Non-default
options that made a proof succeed should be retained in the final proof.

## Reading reports correctly

LeanCert keeps three ideas separate:

1. **Strategy** is the proof algorithm, such as exact normalization,
   subdivision, root sign change, or partition integration.
2. **Numerical backend** is the arithmetic implementation, such as Rational,
   Dyadic, or Affine interval evaluation. A portfolio policy such as
   Dyadic-first with Rational fallback is not an observed backend.
3. **Certificate verification** is how a successful executable check is
   discharged: `kernel`, `native`, or the `auto` policy.

Certificate rejection and verification failure are different outcomes. A
checker that conclusively evaluates to `false` is an expected, resumable
solver result. Failure to reduce, compile, or evaluate the checker is an
infrastructure error and stops routing. In `auto` mode, a conclusive `false`
kernel result never falls back to native verification.

In particular, subdivision and optimization are strategies, not numerical
backends. Selecting `(trust := kernel)` does not select Rational, Dyadic, or
Affine arithmetic.

For example, a successful subdivision report has this shape:

```text
LeanCert recognized: univariate interval bound

Selected strategy:
  recursive interval subdivision
  Taylor depth 10; maximum recursive depth 8

Numerical computation:
  Rational interval evaluation

Certificate verification:
  requested auto → used kernel (several checks)

Subdivision:
  Taylor depth: 10
  Configured maximum depth: 8
  Deepest depth used: 5
  Boxes examined: 27
  Certified leaves: 14

Suggested proof:
  by
    leancert (subdivisions := 8) (trust := auto)

Advanced control:
  by
    interval_bound_subdiv 10 8 (trust := auto)
```

If `auto` uses native verification, the report distinguishes a
cost-gate decision from a failed kernel attempt. A strategy may close several
certificates, so its observed route can also be mixed. The suggested proof
preserves the requested policy (`auto` above), rather than replacing it with
the route observed in one execution.

Subdivision's search enclosures are candidates, not proofs. Search evaluates a
box to decide whether to retain or bisect it; every retained leaf then closes
one fixed checker through the configured verification route. Exhaustion is a
resumable inconclusive result, while a domain obstruction or internal transport
failure stops the portfolio. All non-successes restore the complete tactic
state.

Likewise, a verbose failure report has this shape:

```text
LeanCert recognized: quantified univariate bound

Attempts:
  direct interval certificate — inconclusive
  subdivision — did not establish the requested bound

Next steps:
  check the statement, inspect the domain, or tune the relevant router option
```

Exact checker names and numerical details vary by the selected strategy.

## Advanced controls

Dedicated tactics remain available when you intentionally want to control one
algorithm:

- `certify_bound` and `interval_bound_subdiv` for interval bounds;
- `multivariate_bound` and `opt_bound` for box bounds and optimization;
- `interval_roots`, `interval_unique_root`, and `root_bound` for roots;
- `eventual_bound` for fixed or discovered reciprocal-power tail bounds;
- `interval_minimize`, `interval_maximize`, `interval_argmin`, and
  `interval_argmax` for extrema;
- `finsum_bound` for finite sums;
- `integral_exact` for rational-polynomial integral equalities.

Start with `leancert`; use the dedicated control recommended by `leancert?`
when you need its parameters or when debugging a particular strategy. See the
[tactics reference](../reference/tactics.md) for the exact syntax supported by
each dedicated tactic. Router-recommended certificate tactics accept an inline
`(trust := ...)`. Exact proof construction such as `integral_exact` does not
consult the trust option.

## Conjunctions and disjunctions

LeanCert recursively routes conjunctions:

```lean
import LeanCert.Tactic

example :
    (∀ x ∈ Set.Icc (0 : ℝ) 1, x ^ 2 ≤ 1) ∧
    (∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ x ^ 2) := by
  leancert
```

Normalization may also use `forall_and` to expose independently solvable child
theorems. Every child must be recognized and proved. Successful `leancert?`
reports summarize the child strategies; failure identifies the child's ordinal
and recognized theorem shape.

Disjunctions are intentionally not routed. Choosing between `P ∨ Q` is a
logical branch-selection problem rather than numerical goal classification.
Prove the appropriate branch explicitly and invoke `leancert` inside it.

## When a goal fails

Failures fall into a few useful categories:

- the statement is false and LeanCert has certified counterexample evidence;
- the goal shape is unsupported;
- the expression or numerical domain is unsupported;
- a supported operation has a domain obstruction;
- all applicable strategies were valid but inconclusive;
- proof construction encountered an internal invariant failure.

Use `leancert?` first. Narrow an invalid domain or loosen a bound when the
diagnosis is mathematical; tune `taylorDepth`, `subdivisions`, or
`maxIterations` only for a supported but inconclusive computation. Traces are
appropriate for an internal error or when filing a reproducible issue, not as
the first response to a false statement.

See [Troubleshooting](troubleshooting.md) for detailed guidance and the
dedicated pages for [bounds](bounds.md), [roots](roots.md),
[optimization](optimization-discovery.md), and [integration](integration.md).
