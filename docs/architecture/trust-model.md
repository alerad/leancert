# Trust model

LeanCert separates numerical computation from proof verification:

```text
mathematical goal
→ semantic classification
→ certified numerical checker
→ Boolean/result certificate
→ Golden Theorem
→ Lean proof
```

Search and candidate generation may be untrusted. They cannot establish a
theorem by themselves: the retained result must pass an executable checker,
and a proved Golden Theorem connects that check to the user's proposition.

## Kernel, native, and auto

`leancert.trust` controls how LeanCert proves a closed certificate proposition
such as `check certificate = true`. It does **not** choose Rational, Dyadic, or
Affine arithmetic.

| Mode | Verification | Additional trust |
| --- | --- | --- |
| `kernel` | kernel reduction through `decide +kernel` | none beyond Lean's kernel and foundations |
| `native` | compiled evaluation through `native_decide` | Lean compiler and runtime |
| `auto` | kernel when practical, otherwise native | exactly the route reported by `leancert?` |

```lean
import LeanCert.Tactic

example : Real.log 2 < 7 / 10 := by
  leancert (trust := kernel)
```

`auto` reports whether it used kernel or native verification and, when known,
why native execution was selected. Multiple retained checks are aggregated.

## Arithmetic backends

Rational, Dyadic, and Affine describe numerical representation and enclosure
algorithms. Kernel and native describe how a resulting proposition is
evaluated. A Dyadic certificate may be checked through either route.

`leancert?` distinguishes a backend observed at runtime from a portfolio
policy. A policy is not presented as the backend that actually ran.

## Qualifications

Primary tactic paths and checked APIs use checker/Golden-Theorem boundaries.
Every semantic-router strategy uses a transactional typed result and reports
only execution metadata observed on its retained successful path. Exact and
normalization strategies may correctly retain zero Boolean-certificate checks.
Exact polynomial integration constructs an ordinary kernel proof, so its trust
selection is not applicable.

The lightweight downstream Li₂ interface intentionally separates its
statement module from the expensive verification target. CI builds
that target and checks statement identity. See the
[production verification table](verification-status.md) for all subsystem
qualifications.

## Continuous audit

The [Soundness Guard workflow](https://github.com/alerad/leancert/actions/workflows/soundness-guard.yml)
runs on every push and pull request. It rejects unauthorized axioms, `sorry`
uses, and synthetic proof holes, then checks the exported trust manifest and
representative Golden Theorems. Its README badge links to public run history;
reviewers do not need to recreate CI locally.
