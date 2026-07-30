# Showcase benchmark

This harness measures each public showcase theorem in a separate warm Lean
process. It intentionally includes import and elaboration overhead because it
models a reviewer copying one example into a downstream file.

Run:

```bash
python3 scripts/bench-showcase/run.py --runs 3
```

To refresh the checked-in toolchain baseline:

```bash
python3 scripts/bench-showcase/run.py --runs 3 \
  --output scripts/bench-showcase/baselines/v4.32.2.json
```

The baseline records all samples, the median/range, platform, toolchain,
commit, and dirty-worktree status. It is orientation data rather than a
cross-machine performance guarantee.
