# Python Quickstart

!!! info "Capability status"
    **Stability:** Stable · **Authority:** Checked Bridge ·
    **Standalone replay:** Supported for verified bounds, system roots, and
    eventual bounds

## Install and diagnose

```bash
python -m pip install leancert
leancert doctor
```

A healthy release reports the bundled binary, Bridge Contract, replay support,
checked adaptive capability, and release provenance.

## Prove an exact claim

```python
from fractions import Fraction

import leancert as lc
from leancert import ast

x = ast.var("x")
claim = x**2 <= Fraction(9, 4)

result = lc.prove(
    claim,
    where={x: (Fraction(-3, 2), Fraction(3, 2))},
)

if isinstance(result, lc.Verified):
    print("verified:", result.claim_id)
    print("Lean:", result.provenance.lean_version)
else:
    print(type(result).__name__, result.reason)
```

This proves one proposition for every real input in the closed interval. It is
not a sample-based test.

## Inspect the evidence

For a bound result, each requested direction has its own checked evidence:

```python
if isinstance(result, lc.Verified):
    for check in result.checks:
        print(check.direction, check.enclosure)
        print(check.replay_certificate.checker)
```

## Export it

```python
if isinstance(result, lc.Verified):
    export = result.export_lean_project("verified-bound", verify=True)
    print(type(export).__name__)
```

`verify=True` creates the pinned project and asks Lake to build its explicit
target. Use `leancert verify verified-bound` to audit it again later. Exported
projects do not rerun Python search.

## Never collapse non-success into `False`

```python
result = lc.prove(x - x <= -1, where={x: (0, 1)})
assert isinstance(result, lc.Inconclusive)
```

LeanCert distinguishes failure to establish a claim from a checked
counterexample. Continue with [typed outcomes](proving/outcomes.md).
