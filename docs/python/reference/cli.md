# CLI and Diagnostics

## `leancert doctor`

```bash
leancert doctor
leancert doctor --json
leancert doctor --bridge /absolute/path/to/lean_bridge
```

The diagnostic checks:

- binary discovery;
- Bridge Contract compatibility;
- replayable bound support;
- the checked adaptive route; and
- release source/environment provenance.

The command exits `0` only when every required check is healthy.

## `leancert verify`

```bash
leancert verify verified-bound
leancert verify exports/ --require-trust kernel
leancert verify exports/ --timeout 1200 --fail-fast
leancert verify exports/ --format json
```

Directories are searched recursively for `leancert-export/1` manifests while
build directories are skipped. Verification checks artifact integrity before
running the pinned Lake target.

| Exit | Meaning |
|---:|---|
| `0` | All artifacts rebuilt |
| `1` | Lean rejected an exported theorem |
| `2` | Invalid artifact or command usage |
| `3` | Missing verification infrastructure |
| `4` | Resource limit exceeded |

Machine-readable reports include artifact paths, claim identities, trust
classes, outcomes, timing, and captured build output.
