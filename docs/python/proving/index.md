# Checked Proving with `prove()`

`leancert.prove()` is the stable front door for semantic claims. It:

1. closes free variables with exact domains;
2. normalizes the claim;
3. computes a stable semantic identity;
4. negotiates an advertised Bridge capability;
5. validates the typed response and its authority; and
6. returns a result whose class expresses the outcome.

```python
import leancert as lc
from leancert import ast

x = ast.var("x")
result = lc.prove(ast.sin(x) <= 1, where={x: (0, 1)})
```

## Stable checked families

- [Exact one- and two-sided bounds](bounds.md)
- [Scalar-root existence, uniqueness, and exclusion](scalar-roots.md)
- [Unique nonlinear-system roots](system-roots.md)
- [Exact integral equalities and checked bounds](integrals.md)
- [Eventual reciprocal-power bounds](eventual-bounds.md)

Valid semantic claims outside these routes return a typed `Unsupported`
outcome where possible. They are not silently weakened or sent to an unrelated
discovery API.

## Effort controls

```python
result = lc.prove(
    claim,
    where={x: (0, 1)},
    config=lc.ProveConfig(taylor_depth=16),
)
```

`ProveConfig` controls effort accepted by the negotiated checker schema. It is
not a request to replace the advertised checker or verification route.

## Exact claims versus approximate candidates

The proposition and its domain remain exact. Some workflows, such as nonlinear
system roots, may accept NumPy/SciPy values as **untrusted candidate data**.
Those values are deterministically rationalized, and a poor candidate can only
be rejected; it cannot mint a successful result.
