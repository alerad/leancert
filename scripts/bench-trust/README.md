# bench-trust: external verification-route benchmarks

Compile-level benchmarks for the kernel vs native certificate-verification
routes (`leancert.trust`). This lives *outside* Lean because the quantities
of interest — full `lake env lean` wall time, peak RSS, cold vs warm builds —
cannot be measured reliably from inside one Lean process (imports alone cost
~4s, and `decide +kernel` caches aux lemmas per module).

## Usage

```sh
# full matrix, appends JSONL rows
python3 scripts/bench-trust/run.py

# selected families, custom output
python3 scripts/bench-trust/run.py --families point,finsum --out /tmp/r.jsonl
```

Families: `point` (end-to-end `interval_decide` via `leancert.trust`),
`integration` (partitioned integration checker), `subdiv` (per-subinterval
bound checks), `finsum` (dyadic finite sums). Each family also emits a
`route=none` import-only baseline row — subtract it for marginal cost.

Committed reference runs live in `baselines/` (one per toolchain); `results/`
is scratch and gitignored. When changing the verification engine, run the
matrix before and after and compare against the baseline.

## Calibration summary (v4.32.1, M-series, 2026-07)

From `baselines/v4.32.1.jsonl`, marginal wall time over each family's
import-only baseline (run-to-run noise is roughly ±0.5s):

| family      | scale                        | kernel      | native      |
|-------------|------------------------------|-------------|-------------|
| point       | 10 `interval_decide` log bounds (end-to-end) | ~parity with native (≲0.1s/goal both) | — |
| integration | 500 partitions               | ~+2.5s      | ~0          |
| subdiv      | 64 subintervals              | ~+2.6s      | ~+0.7s      |
| finsum      | 10^3 terms                   | ~+0.8s      | ~0          |
| finsum      | 10^4 terms                   | **~+35s, +1.5 GiB RSS** | ~0 |

Headline: for point inequalities — the dominant PNT+ usage — kernel
verification costs the same as native. The finsum kernel/native crossover
sits around 10^4 terms with superlinear growth; the auto-mode cost gates
should route sums ≲2×10^3 terms (and partition counts ≲500) to the kernel
and everything larger to native.
