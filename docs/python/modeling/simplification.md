# Simplifying Programmatic Expressions

`leancert.simplify()` and `leancert.expand()` operate on the legacy
programmatic `Expr` type. They can expose cancellation before interval
evaluation and thereby reduce dependency over-approximation.

!!! info "Capability status"
    **Stability:** Compatibility API · **Authority:** Untrusted symbolic
    preprocessing · **Standalone replay:** No

```python
import leancert as lc

x = lc.var("x")
raw = x * 100 + 5 - x * 100
reduced = lc.simplify(raw)

print(raw)
print(reduced)  # 5
```

`simplify()` folds constants, removes identities, propagates zero, collects
polynomial terms, and recursively simplifies supported transcendental
arguments. `expand()` distributes polynomial products before collection.

This is a search-quality optimization, not evidence. Submit the resulting
expression to a checked operation for an authoritative enclosure or proof
outcome.

!!! warning "Partial expressions"
    Algebraic identities can require domain assumptions. In particular, the
    compatibility simplifier currently rewrites `x / x` to `1`; that identity
    is valid only where `x != 0`. Do not use simplification to bypass domain
    checks, and prefer the semantic AST plus checked proving path for new
    safety-critical claims.

The semantic `leancert.ast` layer has separate normalization and canonical
encoding. `lc.simplify()` does not accept semantic AST nodes and does not alter
a semantic claim digest.
