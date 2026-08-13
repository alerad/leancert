# bench-trust: external verification-route benchmarks

Compile-level benchmarks for the kernel vs native certificate-verification
routes (`leancert.trust`). This lives *outside* Lean because the quantities
of interest — full `lake env lean` wall time, peak RSS, cold vs warm builds —
cannot be measured reliably from inside one Lean process (imports alone cost
~4s, and `decide +kernel` caches aux lemmas per module).

## Usage

```sh
# prepare a fresh worktree (Mathlib cache plus both imported LeanCert roots)
lake update
lake exe cache get
lake build LeanCert LeanCert.Tactic

# full matrix, appends two runs per cell to the JSONL file
python3 scripts/bench-trust/run.py

# selected families, custom output
python3 scripts/bench-trust/run.py --families point,finsum --out /tmp/r.jsonl

# custom repetitions
python3 scripts/bench-trust/run.py --runs 3 --out /tmp/r.jsonl
```

Families: `point` (end-to-end `interval_decide` via `leancert.trust`),
`integration` (partitioned integration checker), `subdiv` (per-subinterval
bound checks), `finsum` (dyadic finite sums), and `optimization`
(branch-and-bound certificates). Each family also emits a `route=none`
import-only baseline row — subtract it for marginal cost.

Committed reference runs live in `baselines/` (one per toolchain); `results/`
is scratch and gitignored. When changing the verification engine, run the
matrix before and after and compare against the baseline.

The runner appends rather than truncating. Use a new output path for each
session unless combining sessions is intentional.

## Calibration summary (v4.32.2, Apple M1 Max, 2026-08-06)

From `baselines/v4.32.2.jsonl`, using two consecutive compilations per cell.
The figures below are mean marginal wall time over that family's import-only
baseline; differences of a few tenths of a second can be run-to-run noise.

| family | scale | kernel | native |
|---|---:|---:|---:|
| point | 10 `interval_decide` log bounds | approximately baseline | approximately baseline |
| integration | 500 partitions | +3.58s | +0.67s |
| subdivision | 64 subinterval checks | +2.74s | +0.79s |
| finite sum | 1,000 terms | +0.82s | approximately baseline |
| finite sum | 10,000 terms | **+40.85s** | +0.13s |
| optimization | 50 iterations | approximately baseline | approximately baseline |

The finite-sum measurements justify routing large sums away from kernel
reduction. The 500-partition gate keeps a still-manageable kernel route
available. Optimization showed no meaningful route crossover through 50
iterations, so the 100-iteration gate is a conservative policy threshold
rather than an empirically located crossover.

The committed v4.32.2 run records `git_dirty: false` at exact Core revision
`907489ffcae7f42093e3eb13d9c13ee49472ff5d`. All 70 rows succeeded. The
older `v4.32.1.jsonl` remains historical calibration data.
