# Supported downstream API

Public modules are grouped by support level:

| Level | Meaning |
| --- | --- |
| **Stable** | supported contract, covered by import and behavioral tests |
| **Advanced** | supported expert interface whose lower-level details may evolve |
| **Internal** | implementation module with no downstream stability promise |

The stable front doors are `LeanCert`, `LeanCert.Tactic`,
`LeanCert.API.Eval`, `LeanCert.API.Backend`, `LeanCert.API.Bounds`,
`LeanCert.API.Optimization`, and selected domain umbrellas including
`LeanCert.ANT` and `LeanCert.QProduct`.

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

`API.Bounds.checkUpperBoundBox` and `checkLowerBoundBox` use the public checked
evaluator over a list-shaped box. Their structured result retains the enclosure,
the concrete backend selected, and whether that enclosure proves the requested
bound; evaluator and domain failures remain `EvalError` values. The matching
verification theorems lift a retained successful result without rerunning the
evaluator.

The one-dimensional `checkUpperBound`, `checkLowerBound`, and `checkBounds`
functions are explicitly Dyadic-backed Boolean certificates. They include
domain and precision validity, so their Golden Theorems require no separate
support or domain premise. Raw `check... = true` is part of that contract:
tactic clients may close the certificate using kernel, native, or automatic
verification without changing the numerical backend.

`LeanCert.Tactic` exposes supported proof automation, including the semantic
`leancert` / `leancert?` front door and the dedicated `interval_auto`,
`interval_decide`, `certify_bound`, root, optimization, and finite-sum tactics.
`LeanCert.Tactic.Extension` exposes the typed, persistent registry for
downstream unary enclosure rules. Registration validates a candidate, checker,
and soundness theorem. The semantic `leancert` front door can execute imported
rules for unary interval bounds and compose their checked enclosures through
ordinary supported expressions, with checked adaptive subdivision for rejected
or inconclusive candidates. See [Downstream enclosure extensions](extensions.md).

`LeanCert.CertifiedBounds` exposes stable numerical-result interfaces under:

- `LeanCert.CertifiedBounds.Li2`;
- `LeanCert.CertifiedBounds.BKLNW`;
- `LeanCert.CertifiedBounds.Chebyshev`.

The BKLNW and Chebyshev declarations are linked directly to their checked proof
terms. `CertifiedBounds.Li2` is instead a lightweight statement interface: its
two allowlisted placeholder theorems have statement-identical proofs built by
the separate `Li2Verified` target, but the public constants are not
kernel-linked to those proofs. See
[Verification Status](../architecture/verification-status.md) for the precise
trust boundary.

`LeanCert.ANT` exposes reusable analytic-number-theory certificate machinery
and explicit-PNT compiler schemas.

Names under these namespaces carry the downstream stability promise and are
covered by the PrimeNumberTheoremAnd-derived interface and behavioral pattern
suites. Direct `LeanCert.Engine.*` imports remain available for
implementation-level work, but downstream proofs should prefer a stable
certified-bounds alias where one exists.

For historical names removed after their deprecation period, see
[Removed APIs and migration](compatibility.md).

## Semantic tactic API

Use `leancert` for portfolio routing and `certify_bound` when explicit interval
engine control is desired. Trust is selected uniformly with
`(trust := kernel)`, `(trust := native)`, or `(trust := auto)`.

The removed `LeanCert.Tactic.LeanCert.Types` and
`LeanCert.Tactic.LeanCert.Transaction` modules were internal implementation
details. Solver extensions use
`LeanCert.Tactic.LeanCert.Solver.Protocol`. Portfolio strategies return
`Except AttemptFailure SolverExecution`; the sole protocol runner isolates the
attempt, validates the resulting proof artifact, and converts it to an
`AttemptOutcome`. Expected unsupported, rejected, exhausted, and domain cases
must be returned as typed failures rather than exceptions. Dedicated tactic
syntax calls the same typed family cores and translates failures only at the
user-facing elaborator boundary.

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
