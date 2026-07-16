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

| Operation | `auto` backend | Explicit alternatives |
|---|---|---|
| Interval evaluation and bound checks | Dyadic | Rational, Dyadic, Affine |
| Global optimization | Dyadic | Rational, Dyadic, Affine |
| Integration | Rational | Rational |
| Root finding | Rational | Rational |

`auto` chooses the fastest backend with a certified implementation for the
requested operation. It does not fall through after a domain error. An
explicit unsupported backend is rejected rather than silently changed.

Every successful evaluation comes from a checked evaluator and records the
concrete backend in its result. Reciprocal intervals containing zero,
nonpositive logarithm domains, invalid `atanh` domains, and invalid Dyadic
rounding precision return structured errors. Total evaluators whose unsupported
branches use fallback values live under `LeanCert.Internal.*` and are
implementation details. The golden
theorem `LeanCert.evalInterval_correct` proves that every successful public
result encloses the real expression value, independently of which backend was
selected.

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

The historical `eval_interval_dyadic` and `eval_interval_affine` JSON methods
were removed; use `eval_interval` with the `backend` selector. Global
optimization uses `LeanCert.GlobalOptOptions`, which composes the same
`EvalOptions` with independent `SearchOptions`:

```lean
def optimizationOptions : GlobalOptOptions := {
  evaluation := { backend := .affine }
  search := { maxIterations := 2000, tolerance := 1 / 10000,
              useMonotonicity := true }
}

#eval globalMinimize (.mul (.var 0) (.var 0)) [unit] optimizationOptions
```

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
ignoring the option.

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
