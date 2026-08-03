# Exact Mathematical Modeling

`leancert.ast` is an immutable, bridge-independent meaning layer. Constructing
an AST does not run a solver and never sets a `verified` flag.

!!! info "Capability status"
    **Stability:** Stable schema v1 · **Authority:** Deterministic semantic
    model · **Proof status:** No AST object is a proof by itself

## Exact values

Semantic claims accept exact integers, `Fraction`, `Decimal`, and decimal
strings through `ast.rational`:

```python
from decimal import Decimal
from fractions import Fraction
from leancert import ast

a = ast.rational("0.1")
b = ast.rational(Decimal("0.2"))
c = ast.rational(Fraction(3, 10))

assert ast.semantically_equal(a + b, c)
```

Python floats are rejected because the SDK cannot infer which decimal value a
binary approximation was intended to mean:

```python
from leancert import ast

ast.rational(0.1)  # raises InexactFloatError
```

## Symbols have identity

```python
x = ast.var("x")
n = ast.var("n", sort=ast.NATURAL)
```

Variables are identified by a namespace/name `SymbolId`; their display name is
metadata. This prevents accidental capture when claims are normalized or
serialized.

## Domains close claims

```python
from leancert import ast

x = ast.var("x")
open_claim = ast.sin(x) <= 1
closed_claim = ast.close_claim(open_claim, where={x: (0, 1)})
```

`close_claim` requires exact coverage of every free variable. The canonical
encoding uses binder depths, so alpha-renaming a bound variable does not change
the claim's meaning.

Use `ast.interval(lo, hi)` and `ast.box(...)` when a first-class semantic
domain is clearer than tuple shorthand. The older `leancert.Interval` and
`leancert.Box` types belong to the programmatic `Solver` compatibility API;
they are not interchangeable with semantic AST domains without an explicit
legacy conversion.

## Canonical bytes and semantic digests

```python
payload = ast.encode_canonical(closed_claim)
digest = ast.semantic_digest(closed_claim)
round_trip = ast.decode_canonical_strict(payload)

assert ast.alpha_equivalent(closed_claim, round_trip)
```

A semantic digest commits to the AST schema version, normalization version,
canonical semantic bytes, and resolved external declaration identities.
Annotations and source spans do not affect it.

## Built-in and external functions

The semantic AST includes arithmetic, transcendental and special functions,
vectors, integrals, derivatives, root claims, and eventual claims. Definite
integrals are constructed explicitly:

```python
from leancert import ast

x = ast.var("x")
area = ast.integral(x**2, x, 0, 1)
```

Contract 2.6 routes exact rational-polynomial integral equalities and checked
one-sided integral bounds through `prove()`. Other integral shapes and
derivative expressions still have stable AST meaning without necessarily
having a negotiated checker. In general, presence in the AST does **not**
guarantee that the current Bridge supports every claim shape.

External functions require package, revision, semantic, and declaration
identity before they can receive an authoritative semantic digest.

## Legacy expressions

`lc.var("x")` constructs the pre-1.0 programmatic expression type. Use
`ast.legacy_expression`, `ast.legacy_interval`, `ast.legacy_box`, or
`ast.legacy_bound_claim` when migrating intentionally. Conversion is not
verification.

For programmatically generated legacy expressions, see
[Simplification](modeling/simplification.md). For advanced semantic-AST
inspection and rewrites, see [AST Utilities](reference/ast-utilities.md).
