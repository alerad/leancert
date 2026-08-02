# AST Utilities

The semantic AST includes deterministic traversal, transformation, validation,
and capability-analysis helpers for tooling authors.

```python
from leancert import ast

x = ast.var("x")
claim = ast.close_claim(ast.sin(x) <= 1, where={x: (-1, 1)})

print(ast.node_count(claim), ast.max_depth(claim))
print(ast.free_variables(claim))
requirements = ast.infer_requirements(claim)
ast.validate_ast(claim)
```

Inspection helpers include `walk`, `children`, `fold`, `node_count`,
`max_depth`, `free_variables`, `bound_variables`, `collect_functions`,
`collect_constants`, `collect_external_functions`, and `contains_node_type`.
They do not contact Bridge.

`transform`, `map_expressions`, `substitute`, and `rename_symbol` return new
immutable nodes. Validate and re-close transformed claims before proving them;
a syntactic rewrite is not evidence of semantic equivalence.

`infer_requirements` summarizes features a checker must support, while
`check_capabilities` compares requirements with an advertised capability set.
This is preflight analysis, not verification. The negotiated operation and
returned typed outcome remain authoritative.

Canonical encoding, strict decoding, normalization, alpha equivalence, and
semantic digests are covered in [Exact Mathematical Modeling](../modeling.md).
