# Proving a Bound All the Way to Infinity

!!! info "Capability status"
    **Stability:** Stable for nonnegative rational reciprocal-power tails ·
    **Authority:** Checked Bridge · **Standalone replay:** Yes

A finite numerical grid cannot establish a proposition for every sufficiently
large natural number. LeanCert's eventual-bound route searches for a cutoff
and checks one exact certificate for the complete infinite tail.

```python
from fractions import Fraction

import leancert as lc
from leancert import ast

n = ast.var("n", sort=ast.NATURAL)
claim = ast.eventually(
    Fraction(5) / n**2 <= Fraction(1, 100),
    variable=n,
)

result = lc.prove(claim)

if isinstance(result, lc.VerifiedEventualBound):
    print(f"proved for every n >= {result.cutoff}")
```

For this claim the checked cutoff is `23`: every natural `n >= 23` satisfies
`5 / n² <= 1/100`.

## Discovery is not the proof

Python may use exponential search followed by refinement to discover the
smallest accepted cutoff within its search budget. The exported evidence
retains the final cutoff, coefficient, exponent, and bound—not the search
procedure.

Supply an explicit cutoff or control the search budget when needed:

```python
result = lc.prove(
    ast.eventually(
        Fraction(5) / n**2 <= Fraction(1, 100),
        variable=n,
        cutoff=23,
    ),
    config=lc.ProveConfig(eventual=lc.EventualConfig(max_checks=100)),
)
```

## Supported shape

The stable route covers nonnegative rational multiples of reciprocal natural
powers against an exact rational upper bound. A valid but unsupported general
asymptotic expression returns `UnsupportedEventualBound`; it is not sampled and
reported as proof.

## Export

```python
if isinstance(result, lc.VerifiedEventualBound):
    result.export_lean_project("verified-tail", verify=True)
```

The exported theorem covers the entire natural-number tail.
