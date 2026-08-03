# Export and Independently Verify Evidence

!!! info "Capability status"
    **Stability:** Stable · **Exportable families:** checked bounds, unique
    system roots, and eventual bounds · **Trust class:** Kernel

A replayable Python result retains the complete fixed checker input. Exporting
turns it into a small pinned Lean project:

```python
import leancert as lc
from leancert import ast

x = ast.var("x")
result = lc.prove(x**2 <= 1, where={x: (0, 1)})

if isinstance(result, lc.Verified):
    export = result.export_lean_project("verified-bound", verify=True)
    print(type(export).__name__)
```

The directory contains:

```text
verified-bound/
├── LeanCertExport.lean
├── artifact.json
├── certificate.json
├── claim.json
├── provenance.json
├── lakefile.toml
├── lean-toolchain
└── README.md
```

## Verify later or elsewhere

```bash
leancert verify verified-bound
leancert verify exported-proofs/ --require-trust kernel
leancert verify exported-proofs/ --format json
```

Verification checks the integrity envelope and semantic claim digest before it
invokes Lake. It runs the exported project's explicit target and does not rerun
numerical search.

## Reproducible is not automatically air-gapped

The project pins its Lean toolchain and LeanCert source revision. A machine
still needs those dependencies, either from the network, an existing cache, or
a separately prepared vendor/archive process. Copying only the export directory
to a pristine offline machine is not sufficient by itself.

## Atomic and typed failures

Project creation occurs through a temporary sibling directory. Build rejection,
missing tooling, and resource limits leave no partial project at the requested
destination and return distinct result types.

The verification CLI uses stable exit codes:

| Code | Meaning |
|---:|---|
| `0` | Every discovered artifact rebuilt successfully |
| `1` | Lean rejected at least one theorem |
| `2` | An artifact or command argument was malformed |
| `3` | Required verification infrastructure was unavailable |
| `4` | A rebuild exceeded its resource limit |

## What is not exportable

Legacy numerical `Certificate` objects, adaptive checked-leaf records, and
generated proof sketches are not silently treated as replayable v1 artifacts.
The result type explicitly reports when export is unsupported.
