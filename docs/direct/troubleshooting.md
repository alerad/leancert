# Troubleshooting direct automation

Use `leancert` as the normal entry point. If it succeeds but you want to inspect
the selected strategy, use `leancert?`. If it fails, the current router reports
what it recognized and why it could not construct a proof. The messages below
are grouped by those public diagnostics, rather than by internal checker
implementation details.

## The statement is false

When LeanCert can certify a violating point, it reports:

```text
leancert: the statement is false.
Certified counterexample: ...
```

This is evidence about the theorem, not a precision failure. Inspect the point
and change the claim or its domain. `interval_refute` is also useful while
exploring:

```lean expect-error: Counter-example FOUND
example : ∀ x ∈ Set.Icc (-2 : ℝ) 2, x * x ≤ 3 := by
  interval_refute
```

The diagnostic tactic never proves a false proposition.

## Unsupported goal shape

`leancert: unsupported goal shape` means the proposition did not match a
semantic form routed by LeanCert. Supported front-door shapes include point and
interval inequalities, multivariate bounds, root theorems, extrema,
existential bounds, finite sums, definite integrals, closed LeanCert checker
propositions, and conjunctions of supported propositions.

Reformulate the statement into one of those shapes or use the appropriate
programmatic certificate API. Increasing Taylor depth or subdivision cannot
change the logical shape. Router traces are useful when extending the parser:

```lean
set_option trace.LeanCert.router true in
example : ∀ x ∈ Set.Icc (0 : ℝ) 1, x ≤ 1 := by
  leancert
```

## Unsupported expression

If the goal shape is recognized but a function cannot be reified, the message
identifies the unsupported expression or remaining head symbol. First unfold a
small wrapper definition or rewrite the expression using supported real
operations. If that is inappropriate, use an explicit `LeanCert.Core.Expr` and
the lower-level API.

Do not increase the numerical depth until reification succeeds: no numerical
backend has run yet.

## Unsupported or invalid domain

Current numerical solvers generally require closed intervals with rational
endpoints. The router distinguishes unsupported interval topology, symbolic or
non-rational endpoints, unsupported carriers, and empty witness domains.

- For a universal theorem over an empty interval, normalization may prove the
  result vacuously.
- For root or optimizer existence, an empty interval cannot contain a witness.
- For partial operations, narrow the interval or establish the required
  positivity/nonzero condition. Examples include `log x`, `1 / x`, and
  `Real.atanh x`.

More Taylor terms do not repair a domain obstruction.

## No strategy closed the goal

This means the router recognized the theorem and exhausted the applicable
portfolio within its cost budget. Common causes are a true bound with too
little margin, an interval that needs subdivision, or an insufficient Taylor
depth.

Try inspection first:

```lean
example : ∀ x ∈ Set.Icc (0 : ℝ) 1, Real.exp x ≤ 3 := by
  leancert?
```

Then adjust one relevant control, for example:

```lean
example : ∀ x ∈ Set.Icc (0 : ℝ) 1, Real.exp x ≤ 3 := by
  leancert (taylorDepth := 20) (subdivisions := 8)
```

Dedicated tactics such as `certify_bound`, `interval_bound_subdiv`, or
`multivariate_bound` remain available when direct control is useful. Treat a
failed Boolean certificate as either numerical inconclusiveness or a false
candidate until a certified counterexample distinguishes the cases.

## Auto verification used native execution

Certificate verification and numerical evaluation are independent choices.
Rational, Dyadic, and Affine are numerical backends; `kernel`, `native`, and
`auto` are certificate-verification policies.

With `auto`, LeanCert tries or selects kernel verification when the configured
cost gate permits it and otherwise uses the native route. Enable the
verification trace for the detailed decision:

```lean
set_option trace.leancert.verification true in
example : ∀ x ∈ Set.Icc (0 : ℝ) 1, Real.cos x ≤ 1 := by
  leancert (trust := auto)
```

Use `(trust := kernel)` when kernel-only checking is required. A numerical
failure will not normally be fixed by changing the verification policy.

## A conjunction child failed

LeanCert recursively routes `P ∧ Q` (and may use `forall_and` normalization to
expose child theorems). Every child must be independently recognized and
proved. A failure therefore identifies a problem with one child, not with
conjunction introduction itself. Isolate that child and run `leancert?` on it.

Disjunction routing is intentionally unsupported: choosing which proposition
to prove is a logical search decision rather than numerical routing.

## Internal preparation or proof-construction error

An `internal preparation failure`, proof-artifact validation failure, or
transport failure indicates a LeanCert implementation problem rather than an
ordinary inconclusive enclosure. Reproduce it with:

```text
set_option trace.LeanCert.router true
set_option trace.leancert.verification true
```

Report the theorem, Lean/LeanCert revisions, full diagnostic, and relevant
trace. Do not work around an artifact-validation failure by weakening the trust
route.

## Advanced and older-release diagnostics

Dedicated tactics and older LeanCert releases may expose lower-level messages
that the semantic router now summarizes.

### A Boolean certificate evaluated to false

Older output may contain:

```text
native_decide evaluated that the proposition is false
```

Current certificate closure may instead report that `native_decide failed on
certificate check`, while bound tactics usually provide a tactic-specific
inconclusive message. The meaning is only that this candidate certificate did
not close the goal. Loosen a marginal bound, increase an applicable depth, use
subdivision, or check the statement with `interval_refute`.

### Reflected expression transport failed

Older releases could expose:

```text
could not unify ... Expr.eval ... with the goal
```

Current bound tactics report that the reflected expression could not be proved
equal to the user's expression. Unfold small definitions, simplify coercions,
or use an explicit `Expr` with a low-level tactic.

### Discovery command decimal parsing

The command syntax for discovery intervals accepts integer endpoints:

```text
Cannot parse as integer: 3.14159
```

Use integer command bounds, or define a rational interval for tactic/API use.
This restriction does not describe the shared tactic-side numeral parser,
which accepts many elaborated rationals, casts, negations, divisions, and
decimals.

### Optimization gap warning

An optimization-gap warning means a discovered certified bound is valid but
looser than the requested search tolerance. Increase `maxIterations` or Taylor
depth only when a tighter result is needed; the warning does not invalidate the
proof.

## Generated tables

For many-row certificate failures, inspect audit helpers such as
`TableCert.failingIndices` or `InequalityTableCert.failingIndices` rather than
debugging rows one at a time.
