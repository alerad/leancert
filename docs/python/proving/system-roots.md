# Proving a Unique Nonlinear-System Root

!!! info "Capability status"
    **Stability:** Stable · **Authority:** Checked Bridge ·
    **Standalone replay:** Yes · **Current maximum dimension:** 4

An approximate solver can suggest a zero. LeanCert can instead certify that a
whole box contains exactly one zero of a square nonlinear system.

Consider

\[
x^2 + y - 2 = 0, \qquad x + y^2 - 2 = 0.
\]

The point `(1, 1)` is a root, but the claim below is stronger: it states that
there is no second root hiding anywhere in the surrounding rational box.

```python
from fractions import Fraction

import leancert as lc
from leancert import ast

x, y = ast.var("x"), ast.var("y")

claim = ast.unique_system_root(
    (x**2 + y - 2, x + y**2 - 2),
    variables=(x, y),
    within=ast.box({
        x: (Fraction(9, 10), Fraction(11, 10)),
        y: (Fraction(9, 10), Fraction(11, 10)),
    }),
)

result = lc.prove(claim)

if isinstance(result, lc.VerifiedSystemRoot):
    print("unique root certified in", result.certificate.box)
    print("rational center:", result.certificate.center)
```

## Why the search remains untrusted

Python searches for a center and approximate inverse Jacobian. Users may also
supply candidates produced by NumPy or SciPy:

```python
candidate = lc.KrawczykCandidate.from_arrays(center, inverse_jacobian)
config = lc.ProveConfig(
    system_root=lc.SystemRootConfig(candidate=candidate),
)
result = lc.prove(claim, config=config)
```

Float candidates are rationalized and treated only as proposals. Success is
authorized by exact rational `LeanCert.Engine.krawczykCheck` evidence. A
well-formed but inadequate candidate returns `CandidateRejected`, which is
neither verification nor proof that no root exists.

## Export

```python
if isinstance(result, lc.VerifiedSystemRoot):
    result.export_lean_project("verified-system-root", verify=True)
```

The project reconstructs the fixed Krawczyk certificate, kernel-reduces its
checker, applies the corresponding soundness theorem, and asserts kernel trust
on the resulting theorem.
