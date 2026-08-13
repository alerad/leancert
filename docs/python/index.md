# Python SDK

The LeanCert Python SDK turns exact mathematical claims into typed, checked
outcomes. It combines Python's modeling and search ecosystem with LeanCert's
small, explicit certificate checkers.

```python
import leancert as lc
from leancert import ast

x = ast.var("x")
result = lc.prove(ast.sin(x) <= 1, where={x: (0, 1)})

match result:
    case lc.Verified():
        print("checked", result.claim_id)
    case lc.Inconclusive(reason=reason):
        print("not proved", reason)
    case _:
        print(type(result).__name__)
```

## Three layers, deliberately separated

1. **Semantic claims** use immutable, exact `leancert.ast` objects and the
   stable `leancert.prove()` front door.
2. **Checked numerical tools** expose interval evaluation, optimization,
   scalar roots, integration, automatic differentiation, and neural-network
   propagation through the programmatic `Solver` API.
3. **Search and diagnostics** include adaptive splitting, candidate
   generation, sampling, and proof sketches. These tools help find evidence;
   they do not silently promote heuristic success into proof.

Start with the first layer. Move to the numerical toolkit only when you need
control below `prove()`.

## What is stable in v1

- Exact one- and two-sided bounds over closed rational boxes
- Unique nonlinear-system roots checked with exact rational Krawczyk data
- Scalar-root existence, uniqueness, and exclusion on exact rational intervals
- Exact polynomial integral equalities and checked one-sided integral bounds
- Eventual reciprocal-power bounds over natural-number tails
- Typed non-success outcomes
- Stable semantic claim digests
- Complete Bridge build provenance
- Standalone Lean-project export for every stable checked result family
- Independent artifact verification with stable CLI exit codes

See the [capability status matrix](capabilities.md) before relying on adaptive,
quantifier-synthesis, neural-network, or legacy APIs.

## Installation

```bash
pip install leancert
leancert doctor
```

Supported wheels include the matching Bridge binary, so ordinary SDK use does
not require a local Lean installation. Rebuilding exported projects does
require Lake and access to the pinned Lean dependencies.

## Next steps

- [Prove a first claim](quickstart.md)
- [Model exact mathematics](modeling.md)
- [Understand typed outcomes](proving/outcomes.md)
- [Export independently rebuildable evidence](evidence/export.md)
