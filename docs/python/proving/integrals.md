# Exact Integral Equalities and Checked Bounds

!!! info "Capability status"
    **Stability:** Stable · **Authority:** Checked Bridge ·
    **Standalone replay:** Yes · **Bridge contract:** 2.6+

LeanCert keeps two mathematically different integration claims separate:

1. exact equality for a rational polynomial; and
2. a certified lower or upper bound obtained from interval integration.

## Exact equality

```python
from fractions import Fraction

import leancert as lc
from leancert import ast

x = ast.var("x")
area = ast.integral(x**2, x, 0, 1)

result = lc.prove(ast.eq(area, Fraction(1, 3)))

if isinstance(result, lc.VerifiedIntegralEquality):
    print("exactly", result.bound)
    result.export_lean_project("integral-one-third", verify=True)
```

This is not numerical quadrature rounded to `1/3`. The Bridge recognizes an
exact rational polynomial, computes its rational antiderivative, and checks the
endpoint value with `QPoly.checkExactIntegral`.

An interval enclosure is never used to certify equality. A non-polynomial
equality is `UnsupportedIntegral`; a wrong polynomial value is
`IntegralCandidateRejected` and carries no certificate.

## One-sided bounds

```python
upper = lc.prove(area <= Fraction(1, 2))
lower = lc.prove(Fraction(1, 4) <= area)

if isinstance(upper, lc.VerifiedIntegralBound):
    print("checked enclosure:", upper.enclosure)
    print("fixed partitions:", upper.certificate.partitions)
```

Python and the Bridge may search over increasing uniform partition counts. The
search is candidate generation only. Success is authorized by rerunning the
chosen count through the fixed lower- or upper-bound checker. The certificate
retains that count, not the discovery procedure.

Configure the bounded search without changing proof authority:

```python
config = lc.ProveConfig(
    integral=lc.IntegralConfig(
        start_partitions=16,
        max_partitions=4096,
    ),
)

result = lc.prove(ast.integral(ast.exp(x), x, 0, 1) <= 2, config=config)
```

Partition exhaustion returns `InconclusiveIntegral`. An expression outside the
currently supported globally continuous fragment returns `UnsupportedIntegral`.
A failed interval-domain check returns `IntegralDomainObstruction`.

## Evidence boundary

The replay payload contains only:

- the lowered exact integrand;
- ordered rational endpoints;
- equality, lower-bound, or upper-bound relation;
- the exact rational target; and
- the accepted partition count for an inequality.

Export rebuilds the fixed checker and corresponding Golden Theorem in a pinned
Lean project. It does not rerun partition discovery.

