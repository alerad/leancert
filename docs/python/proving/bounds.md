# Exact Bounds Without Floating-Point Ambiguity

!!! info "Capability status"
    **Stability:** Stable · **Authority:** Checked Bridge ·
    **Standalone replay:** Yes

Python's `0.1 + 0.2` example is harmless in ordinary numerical work but an
ambiguous foundation for a formal claim. LeanCert therefore rejects floats at
the semantic boundary and requires the intended exact number.

## The exact claim

```python
import leancert as lc
from leancert import ast

x = ast.var("x")
three_halves = ast.rational("1.5")

result = lc.prove(
    ast.sin(x) ** 2 <= 1,
    where={x: (-three_halves, three_halves)},
)

if isinstance(result, lc.Verified):
    print("checked:", result.claim_id)
```

The decimal spelling `"1.5"` denotes exactly `3/2`. The result covers every
real number in `[-3/2, 3/2]`; no input grid is sampled.

## The deliberate failure mode

```python
lc.prove(
    ast.sin(x) <= 0.5,
    where={x: (0, 1)},
)
```

This raises `InexactFloatError` before a Bridge request is sent. Write
`ast.rational("0.5")` or `Fraction(1, 2)` to state the intended proposition.

## Two-sided bounds

```python
from fractions import Fraction

result = lc.prove(
    ast.all_of(x >= -1, x <= 1),
    where={x: (Fraction(-1), Fraction(1))},
)
```

Each direction is checked exactly once and retained as separate evidence.

## Export the receipt

```python
if isinstance(result, lc.Verified):
    exported = result.export_lean_project("verified-bound", verify=True)
    print(type(exported).__name__)
```

The exported project contains the normalized claim, fixed checker payload,
certificate, provenance, Lean source, toolchain pin, and integrity manifest.
It can be rebuilt without rerunning Python search. An offline rebuild requires
the pinned Lean toolchain and dependencies to have been cached or vendored.
