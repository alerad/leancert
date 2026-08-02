# Python Capability Status

LeanCert Python contains stable checked interfaces, lower-level numerical
tools, compatibility APIs, and experimental orchestration. This matrix states
which layer is allowed to authorize a success.

| Surface | Stability | Authority | Standalone replay | Preferred use |
|---|---|---|---:|---|
| `prove()` exact bounds | Stable | Checked Bridge | Yes | Default bound API |
| Unique nonlinear-system roots | Stable | Checked Bridge | Yes | Default system-root API |
| Eventual reciprocal-power bounds | Stable | Checked Bridge | Yes | Default supported tail API |
| Typed non-success outcomes | Stable | Checked Bridge/SDK validation | N/A | Always inspect the type |
| Semantic AST and claim digests | Stable v1 schema | Deterministic SDK semantics | Included in exports | Modeling and identity |
| `eval_interval`, `find_bounds` | Legacy/programmatic | Checked numerical operation | No | Exploration and advanced control |
| Scalar roots and integration | Legacy/programmatic | Checked numerical operation | No | Advanced numerical workflows |
| Checked derivative enclosures | Programmatic | Checked numerical operation | No | Sensitivity and Lipschitz analysis |
| Adaptive leaf verification | Experimental | Checked Bridge per leaf | No unified replay | Difficult bound search |
| Adaptive split selection | Experimental | Search heuristic | No | Candidate domain decomposition |
| NN forward enclosures | Programmatic | Checked numerical operation | No | ReLU-network bounds |
| PyTorch/Transformer conversion | Experimental | Untrusted conversion/code generation | Depends on downstream build | Candidate model export |
| Quantifier synthesis | Experimental/mixed | Varies by operation | Usually no | Witness discovery |
| Monte Carlo and bug triage | Diagnostic | None | No | Finding examples, never proof |
| Legacy proof-sketch rendering | Legacy | None until separately compiled | No | Human inspection only |

## Authority vocabulary

**Kernel-replayable** means an exported fixed certificate can be rebuilt as a
pinned Lean project and checked with `#assert_trust kernel`.

**Checked Bridge** means the negotiated LeanCert checker accepted the exact
request payload. It does not mean Python search became trusted.

**Checked numerical operation** means the Bridge returned a rigorous numerical
result, but the Python result family does not currently export the complete
standalone replay project promised by the v1 semantic API.

**Search heuristic** and **diagnostic** outputs may propose candidates or find
concrete violations. They cannot authorize `Verified`.

## Compatibility APIs

The pre-1.0 `lc.var`, `Solver`, and numerical result classes remain useful.
New proof-oriented code should begin with `leancert.ast` and `leancert.prove`.
The two expression systems are intentionally not accepted interchangeably;
explicit adapters preserve the migration boundary.
