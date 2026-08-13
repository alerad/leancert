# Programmatic Artifact Verification

The independent rebuild used by `leancert verify` is also a Python API.

```python
import leancert as lc

projects = lc.discover_exported_projects(["./proof-artifacts"])
report = lc.verify_exported_projects(
    [str(path) for path in projects],
    require_trust="kernel",
    timeout=900,
    fail_fast=True,
)

for artifact in report.artifacts:
    print(artifact.path, artifact.status, artifact.claim_id)

raise SystemExit(int(report.exit_code))
```

Discovery accepts project directories, parent trees, or an `artifact.json`
path. It skips common build and virtual-environment directories and does not
follow symlinked directories.

`verify_exported_projects()` validates manifests and digests before invoking
`lake build`. Statuses distinguish `verified`, `verification_failed`,
`invalid_artifact`, `infrastructure_failure`, and `resource_limit`.
`VerificationExitCode` maps these classes to stable process codes. A report is
verified only when it contains at least one artifact and every artifact passes.

## Programmatic doctor

```python
import leancert as lc

report = lc.diagnose()
for check in report.checks:
    print(check.name, check.ok, check.detail)
```

`diagnose()` checks binary discovery, handshake/contract compatibility,
replayable-bound support, checked-adaptive support, and release provenance.
Health is installation evidence, not a mathematical proof result.
