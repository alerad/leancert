# Scalar Root Existence, Uniqueness, and Exclusion

!!! info "Capability status"
    **Stability:** Stable · **Authority:** Checked Bridge ·
    **Standalone replay:** Yes · **Bridge contract:** 2.5+

A numerical root finder proposes points. LeanCert instead checks a complete
rational interval against one of three theorem-backed claims:

```python
import leancert as lc
from leancert import ast

x = ast.var("x")

exists = lc.prove(ast.root_exists(x, variable=x, within=(-1, 1)))
unique = lc.prove(ast.unique_root(x, variable=x, within=(-1, 1)))
excluded = lc.prove(ast.root_excluded(x + 2, variable=x, within=(-1, 1)))
```

The successful result types are `VerifiedRootExistence`,
`VerifiedUniqueRoot`, and `VerifiedRootExclusion`. Their fixed checkers are,
respectively:

- sign change plus continuity;
- interval-Newton contraction; and
- interval exclusion of zero.

No root search or subdivision is trusted by this API. The supplied interval is
the complete candidate. `ScalarRootCandidateRejected` means that interval did
not satisfy the selected checker; it does not prove the opposite claim.

## Independently replay it

```python
if isinstance(unique, lc.VerifiedUniqueRoot):
    unique.export_lean_project("verified-unique-root", verify=True)
```

The generated theorem reconstructs the exact expression and interval,
kernel-reduces the fixed checker, applies its Golden Theorem, and finishes with
`#assert_trust kernel`.

