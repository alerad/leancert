# Supported downstream API

LeanCert provides three stable umbrella imports for downstream developments:

```lean
import LeanCert.Tactic
import LeanCert.CertifiedBounds
import LeanCert.ANT
```

The stable checked programmatic imports are:

```lean
import LeanCert.API.Eval
import LeanCert.API.Backend
import LeanCert.API.Optimization
import LeanCert.API.Bounds
```

`Eval` provides the backend-independent checked dispatcher and structured
errors. `Backend` retains backend-native result types. `Optimization` provides
checked branch-and-bound enclosures. `Bounds` provides computable,
support-free Boolean bound certificates and their Golden Theorems.

These imports are contract-tested in isolation and may not import tactic,
ANT, ML, Chebyshev, or example modules. The tactic trust policy remains under
`LeanCert.Tactic`; it is not re-exported by the programmatic modules.

The proof-facing boundary is intentionally Boolean:

```lean
import LeanCert.API.Bounds

open LeanCert LeanCert.Core

def positive : IntervalRat := ⟨1, 2, by norm_num⟩
def logarithm : Expr := .log (.var 0)

example (h : API.Bounds.checkUpperBound logarithm positive 1 = true) :
    ∀ x ∈ positive, Expr.eval (fun _ => x) logarithm ≤ 1 := by
  simpa using (API.Bounds.verifyUpperBound h)
```

`API.Bounds` is currently and explicitly Dyadic-backed. Its checker includes
domain and precision validity, so its Golden Theorems require no separate
support or domain premise. Raw `check... = true` is part of the contract:
tactic clients may close that certificate using kernel, native, or automatic
verification without changing the numerical backend.

`LeanCert.Tactic` exposes supported proof automation, including the semantic
`leancert` / `leancert?` front door and the dedicated `interval_auto`,
`interval_decide`, `certify_bound`, root, optimization, and finite-sum tactics.

`LeanCert.CertifiedBounds` exposes pre-verified numerical results under:

- `LeanCert.CertifiedBounds.Li2`;
- `LeanCert.CertifiedBounds.BKLNW`;
- `LeanCert.CertifiedBounds.Chebyshev`.

The Li₂ namespace includes the symmetric integrand and its basic bounds as
well as the certified `li(2)` value and numerical enclosure.

`LeanCert.ANT` exposes reusable analytic-number-theory certificate machinery
and explicit-PNT compiler schemas.

Names under these namespaces carry the downstream stability promise: statement
changes and removals require a compatibility period and must pass the
PrimeNumberTheoremAnd-derived interface and behavioral pattern suites.

Historical `LeanCert.Examples.Li2Bounds` and `LeanCert.Examples.BKLNW_*`
imports continue to compile. Their legacy certificate declarations are
deprecated with machine-readable replacements. Direct `LeanCert.Engine.*`
imports remain available for implementation-level work, but downstream proofs
should prefer the stable certified-bounds aliases where one exists.

## Semantic tactic API migration

The semantic-router release consolidated tactic-era entry points. Some
spellings remain as deprecated compatibility aliases:

| Deprecated or removed | Canonical replacement |
| --- | --- |
| `interval_bound` | `leancert`, or `certify_bound` for explicit engine control |
| `certify_kernel*`, `fast_bound*` | `certify_bound (trust := kernel)` or `certify_bound (trust := auto)`, with an explicit depth when needed |
| `interval_integrate` | state an ordinary integral equality/inequality and use `leancert` |
| `#minimize`, `#maximize` | `#find_min`, `#find_max` |
| `import LeanCert.Discovery.Types` | `import LeanCert.Validity.Types` |
| `LeanCert.Meta.reify` | `LeanCert.Meta.reifyWithReport` |
| `LeanCert.Meta.toRat?` and related numeric aliases | `LeanCert.Meta.Numeral.toRat?` and the corresponding `Numeral` function |

The removed `LeanCert.Tactic.LeanCert.Types` and
`LeanCert.Tactic.LeanCert.Transaction` modules were internal implementation
details. Solver extensions use
`LeanCert.Tactic.LeanCert.Solver.Protocol`, consume a proof-bearing
`PreparedGoal`, return typed `AttemptOutcome` values, and hand back validated
`ProofArtifact`s. Existing dedicated tactics enter this protocol through an
internal adapter while their numerical engines are migrated to consume prepared
payloads directly; this adapter is not a public compatibility API.

## Checked automatic differentiation

The aggregate `LeanCert` import also exposes the checked AD boundary:

- `derivIntervalChecked` and `derivIntervalChecked1` for one coordinate;
- `gradientIntervalChecked` for every coordinate of a list-backed box;
- `evalWithDerivChecked_der_correct` and `derivIntervalChecked_correct` as the
  semantic soundness theorems;
- `gradientIntervalChecked_correct` for coordinate-aligned full-gradient
  soundness;
- `evalWithDerivChecked_differentiableAt` for extracting differentiability.

These APIs support `inv` and `log` when their interval arguments prove the
required domain conditions. They return `EvalResult`; application code should
not substitute the internal total evaluator.

For deep expressions where rational denominators would grow, the same boundary
is available through `evalDualDyadicChecked`,
`derivIntervalDyadicChecked`, and `gradientIntervalDyadicChecked`. The Dyadic
API takes an `IntervalDyadicEnv` plus `DyadicConfig`, rejects positive
`precision`, and returns Dyadic enclosures. Its Golden Theorems have the same
shape and require no separate support or domain proof. Callers that already
have rational boxes can use `derivIntervalDyadicCheckedOfRat` and
`gradientIntervalDyadicCheckedOfRat`; conversion and its containment proof are
part of their Golden Theorems. The backend selector in `EvalOptions` does not
dispatch AD calls; select one of these checked boundaries explicitly. See
[Checked Automatic Differentiation](../direct/checked-ad.md) for a copy-paste
example, the entry-point decision table, supported syntax, error behavior, and
benchmark command.
