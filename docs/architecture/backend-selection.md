# Interval Backend Selection

LeanCert exposes one authoritative checked evaluation façade:
`LeanCert.evalInterval` with `LeanCert.EvalOptions`. Its implementation
dispatches through an internal backend selector; there is no second public
general evaluator to choose between. JSON callers use the ordinary
`eval_interval`, `check_bound`, `global_min`, and `global_max` methods with a
`backend` field.

The public `IntervalOutcome` contains only the backend-independent rational
enclosure and the concrete backend used. Backend-native results are available
through the checked `LeanCert.Backend.Rational`, `.Dyadic`, and `.Affine` APIs.

Supported selector values are `auto`, `rational`, `dyadic`, and `affine`.

Backend selection and certificate verification are independent axes:

| Axis | `auto` means | Configured by |
| --- | --- | --- |
| Evaluation backend | Inspect the operation/expression and select a certified numerical backend | `EvalOptions.backend` |
| Verification route | Try kernel verification, then report and use native verification if required | `leancert.trust` or `(trust := auto)` |

Changing the verification route does not change the numerical backend, and
changing the numerical backend does not grant permission to use compiler
trust. Programmatic `evalInterval` does not import or expose tactic-side trust
configuration.

The detailed capability matrix below is rendered from
`LeanCert.backendCapabilities`. CI checks that every operation/backend pair has
one row and that its engine claim agrees with the executable dispatcher.

| Operation | Backend | Engine | Public API | Tactic | Automatic | Expression fragment | Configuration | Result | Domain checked | Note |
|---|---|---|---|---|---|---|---|---|---|---|
| interval evaluation | Rational | supported | supported | supported | supported | arbitrary checked Expr | fixed Taylor depth 10 | IntervalRat | yes | — |
| interval evaluation | Dyadic | supported | supported | supported | supported | arbitrary checked Expr | Taylor depth, precision | IntervalDyadic → IntervalRat | yes | — |
| interval evaluation | Affine | supported | supported | unavailable | supported | arbitrary checked Expr | Taylor depth, maximum noise symbols | AffineForm → IntervalRat | yes | some transcendental nodes conservatively concretize to intervals |
| checked derivative | Rational | supported | supported | not planned | supported | domain-aware AD (including inv/log) | Taylor depth | DerivativeOutcome | yes | — |
| checked derivative | Dyadic | supported | supported | not planned | supported | domain-aware AD (including inv/log) | Taylor depth, precision | DerivativeOutcome | yes | — |
| checked derivative | Affine | not planned | not planned | not planned | not planned | none | — | none | no | — |
| checked gradient | Rational | supported | supported | not planned | supported | domain-aware AD (including inv/log) | Taylor depth | GradientOutcome | yes | — |
| checked gradient | Dyadic | supported | supported | not planned | supported | domain-aware AD (including inv/log) | Taylor depth, precision | GradientOutcome | yes | — |
| checked gradient | Affine | not planned | not planned | not planned | not planned | none | — | none | no | — |
| global optimization | Rational | supported | supported | unavailable | unavailable | arbitrary checked Expr | fixed Taylor depth 10 | GlobalResult | yes | — |
| global optimization | Dyadic | supported | supported | supported | supported | arbitrary checked Expr | Taylor depth, precision | GlobalResult | yes | — |
| global optimization | Affine | supported | supported | unavailable | unavailable | arbitrary checked Expr | Taylor depth, maximum noise symbols | GlobalResult | yes | — |
| partition integration | Rational | supported | supported | supported | supported | arbitrary checked Expr | fixed Taylor depth 10, partitions | IntegralOutcome | yes | — |
| partition integration | Dyadic | supported | supported | unavailable | unavailable | arbitrary checked Expr | Taylor depth, precision, partitions | IntegralOutcome | yes | — |
| partition integration | Affine | not planned | not planned | not planned | not planned | none | — | none | no | — |
| root existence | Rational | supported | supported | supported | supported | checked continuous expressions | fixed Taylor depth 10 | sign-change certificate | yes | — |
| root existence | Dyadic | unavailable | unavailable | unavailable | unavailable | none | — | none | no | — |
| root existence | Affine | not planned | not planned | not planned | not planned | none | — | none | no | — |
| root uniqueness | Rational | supported | supported | supported | supported | ADSupported | Taylor depth | Newton/Krawczyk certificate | yes | — |
| root uniqueness | Dyadic | unavailable | unavailable | unavailable | unavailable | none | — | none | no | — |
| root uniqueness | Affine | not planned | not planned | not planned | not planned | none | — | none | no | — |

For interval evaluation, `auto` chooses Affine for exact repeated-subexpression
cancellation, Rational for ordinary algebraic expressions, and Dyadic for
nonlinear expressions or syntax whose cumulative rational-denominator size
exceeds the configured internal budget. Global optimization remains Dyadic by
default; integration and roots remain Rational. Automatic selection does not
fall through after a domain error. An explicit unsupported backend is rejected
rather than silently changed.

Every successful evaluation comes from a checked evaluator and records the
concrete backend in its result. Reciprocal intervals containing zero,
nonpositive logarithm domains, invalid `atanh` domains, and invalid Dyadic
rounding precision return structured errors. Total evaluators whose unsupported
branches use fallback values live under `LeanCert.Internal.*` and are
implementation details. The golden
theorem `LeanCert.evalInterval_correct` proves that every successful public
result encloses the real expression value, independently of which backend was
selected.

Checked automatic differentiation uses the independent `ADOptions` selector.
`evalWithDerivative` and `evalGradient` return backend-independent Rational
enclosures and record both the requested and selected backend. Backend-native
entry points remain available for advanced callers. See [Checked Automatic
Differentiation](../direct/checked-ad.md).

Checked partition integration similarly exposes `integrateUniform` with
`IntegrationOptions`. Explicit Rational and Dyadic selection is supported;
automatic selection deliberately remains Rational until the integration
benchmark suite demonstrates a stable Dyadic crossover.

```lean
import LeanCert

open LeanCert

def unit : IntervalRat := ⟨0, 1, by norm_num⟩

def preciseDyadic : EvalOptions := {
  backend := .dyadic
  precisionOptions := { dyadicExponent := -80, taylorDepth := 12 }
}

#eval evalInterval (.exp (.var 0)) [unit]
#eval evalInterval (.exp (.var 0)) [unit] { backend := .affine }
#eval evalInterval (.exp (.var 0)) [unit] preciseDyadic
```

The current Core public JSON facade removed the historical
`eval_interval_dyadic` and `eval_interval_affine` methods; use `eval_interval`
with the `backend` selector. The published Python SDK 1.0 compatibility client
still uses native Dyadic/Affine operation names when negotiating its released
Bridge contract. Those names are a Python/Bridge compatibility surface, not
additional Lean public APIs. Global
optimization uses `LeanCert.GlobalOptOptions`, which composes the same
`EvalOptions` with independent `SearchOptions`:

```lean
def unit : IntervalRat := ⟨0, 1, by norm_num⟩

def optimizationOptions : GlobalOptOptions := {
  evaluation := { backend := .affine }
  search := { maxIterations := 2000, tolerance := 1 / 10000,
              useMonotonicity := true }
}

#eval globalMinimize (.mul (.var 0) (.var 0)) [unit] optimizationOptions
```

The public `GlobalResult` contains only stable summary data: lower and upper
bounds, the best box, and the iteration count. Resumable priority-queue state
remains part of the advanced engine API.

Despite the historical `globalMinimize` and `globalMaximize` names, their
Golden Theorems certify global lower and upper bounds respectively; they do
not claim that `bestBox` contains an attained optimizer.

At the Lean API level, division-capable guided optimization and
counterexample search now return `EvalResult`: `globalMinimizeGuidedDiv`,
`globalMaximizeGuidedDiv`, `findViolationDiv`, and `findViolationLowerDiv` can
report a domain failure. The former total `CoreDiv` helpers were removed
because their return type could not distinguish a certified enclosure from a
finite heuristic fallback.

## Options

The common JSON options are:

```json
{
  "backend": "auto",
  "taylorDepth": 10,
  "precision": -53,
  "maxNoiseSymbols": 0
}
```

`precision` must be nonpositive when Dyadic evaluation is selected, because
the correctness theorem for outward conversion requires that condition.
`maxNoiseSymbols` is used only by Affine evaluation. The unused
`roundAfterOps` option was removed: Dyadic arithmetic rounds outward after
each arithmetic operation, exactly as its evaluator and proof specify.

`taylorDepth` configures the Dyadic and Affine evaluators. The checked Rational
evaluator currently has a fixed verified depth of 10; Rational evaluation,
optimization, integration, bisection, and candidate-certification requests
with another value are rejected as invalid configuration rather than silently
ignoring the option. For the verified computable core, checked Rational
evaluation uses the tight Taylor/reduced-range evaluator. Other syntax falls
back to the general checked Rational evaluator, retaining structured domain
errors and the backend-independent correctness contract.

Checked global optimization supports `useMonotonicity`. For the differentiable
`const/var/add/mul/neg/exp/sin/cos` fragment, a computable interval-AD gradient
may fix monotone coordinates to the minimizing endpoint. The checked loop's
invariant carries a representative point in the pruned box and a proof that its
objective value is no larger than the original point. Expressions outside that
AD fragment remain certified and simply receive no monotonicity reduction.

Checked branch-and-bound computes its lower bound from the current partition
of terminal and active boxes. Subdivision can therefore tighten dependency-
sensitive expressions; the root enclosure is not retained as a permanent
lower bound. Dispatcher-level min/max theorems connect every successful
Rational, Dyadic, or Affine result to the real semantics.
