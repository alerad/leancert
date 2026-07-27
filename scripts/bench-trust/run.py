#!/usr/bin/env python3
"""External compile-benchmark harness for LeanCert verification routes.

Measures what in-process benchmarks cannot: full `lake env lean` wall time
(cold and warm), peak RSS, and success/failure per (family, route, size)
cell. Used to calibrate the auto-mode cost gates and to catch performance
regressions when the verification engine changes.

Usage (from the repo root):
    python3 scripts/bench-trust/run.py [--out results.jsonl] [--families point,finsum]

Families:
    baseline     import-only files (subtract from other rows for marginal cost)
    point        end-to-end `interval_decide` log bounds via `leancert.trust`
    integration  checker-level partitioned integration (sin on [0,1])
    subdiv       checker-level per-subinterval bounds (x^2 + sin x on [0,1])
    finsum       checker-level dyadic finite sums (sum of k, 1..n)

Routes: kernel (`decide +kernel` / trust option), native (`native_decide`).

Each cell is compiled twice in a row: run 1 ("cold" — OS caches may still be
warm from a previous cell sharing imports) and run 2 ("warm"). Rows are
appended as JSONL.
"""

import argparse
import datetime
import json
import math
import pathlib
import re
import subprocess
import sys
import tempfile
import time

REPO = pathlib.Path(__file__).resolve().parents[2]
TIMEOUT_S = 420

# ---------------------------------------------------------------- templates

def point_file(route: str, n_lemmas: int) -> tuple[str, str]:
    header = "import LeanCert.Tactic\n\n"
    body = []
    for i, k in enumerate(range(2, 2 + n_lemmas)):
        # strict upper bound on log k with ~1% margin
        num = int(math.log(k) * 1000) + 12
        body.append(
            f'set_option leancert.trust "{route}" in\n'
            f"theorem bench_log_{i} : Real.log {k} < {num}/1000 := by interval_decide\n"
        )
    return header, "\n".join(body)


def integration_file(route: str, n_parts: int) -> tuple[str, str]:
    tac = "decide +kernel" if route == "kernel" else "native_decide"
    header = "import LeanCert.Validity.Integration\n\nopen LeanCert.Core LeanCert.Validity.Integration\n\nset_option maxHeartbeats 16000000\n\n"
    body = (
        f"example : ((integratePartitionChecked (.sin (.var 0)) ⟨0, 1, by norm_num⟩ {n_parts}).elim\n"
        f"    false (fun b => decide (b.lo ≤ 4597/10000 ∧ (4597/10000 : ℚ) ≤ b.hi))) = true := by\n"
        f"  {tac}\n"
    )
    return header, body


def subdiv_file(route: str, n_sub: int) -> tuple[str, str]:
    tac = "decide +kernel" if route == "kernel" else "native_decide"
    header = "import LeanCert.Validity.Bounds\n\nopen LeanCert.Core LeanCert.Validity\n\nset_option maxHeartbeats 16000000\n\n"
    body = []
    for k in range(n_sub):
        body.append(
            f"example : checkUpperBound (.add (.mul (.var 0) (.var 0)) (.sin (.var 0))) "
            f"⟨{k}/{n_sub}, {k + 1}/{n_sub}, by norm_num⟩ 2 {{ taylorDepth := 10 }} = true := by {tac}\n"
        )
    return header, "".join(body)


def finsum_file(route: str, n_terms: int) -> tuple[str, str]:
    tac = "decide +kernel" if route == "kernel" else "native_decide"
    target = n_terms * (n_terms + 1) // 2
    header = "import LeanCert.Engine.FinSumDyadic\n\nopen LeanCert.Core LeanCert.Engine\n\nset_option maxHeartbeats 16000000\n\n"
    body = (
        f"example : checkFinSumUpperBoundFull (.var 0) 1 {n_terms} {target} {{}} = true := by\n"
        f"  {tac}\n"
    )
    return header, body


MATRIX = {
    "point": {"gen": point_file, "sizes": [1, 10], "routes": ["kernel", "native", "auto"]},
    "integration": {"gen": integration_file, "sizes": [10, 50, 200, 500], "routes": ["kernel", "native"]},
    "subdiv": {"gen": subdiv_file, "sizes": [16, 64], "routes": ["kernel", "native"]},
    "finsum": {"gen": finsum_file, "sizes": [100, 1000, 10000], "routes": ["kernel", "native"]},
}

BASELINES = {
    "point": "import LeanCert.Tactic\n",
    "integration": "import LeanCert.Validity.Integration\n",
    "subdiv": "import LeanCert.Validity.Bounds\n",
    "finsum": "import LeanCert.Engine.FinSumDyadic\n",
}

# ---------------------------------------------------------------- execution

def compile_once(path: pathlib.Path) -> dict:
    start = time.monotonic()
    try:
        proc = subprocess.run(
            ["/usr/bin/time", "-l", "lake", "env", "lean", str(path)],
            cwd=REPO, capture_output=True, text=True, timeout=TIMEOUT_S,
        )
        wall = time.monotonic() - start
        rss = None
        m = re.search(r"(\d+)\s+maximum resident set size", proc.stderr)
        if m:
            rss = int(m.group(1)) / (1024 * 1024)  # bytes -> MiB on macOS
        # /usr/bin/time echoes lean's stderr too; lean errors appear on stdout
        ok = proc.returncode == 0
        first_error = None
        if not ok:
            for line in (proc.stdout + proc.stderr).splitlines():
                if "error" in line:
                    first_error = line.strip()[:300]
                    break
        return {"ok": ok, "wall_s": round(wall, 2), "max_rss_mib": round(rss, 1) if rss else None,
                "error": first_error}
    except subprocess.TimeoutExpired:
        return {"ok": False, "wall_s": TIMEOUT_S, "max_rss_mib": None, "error": "timeout"}


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", default=str(REPO / "scripts/bench-trust/results/latest.jsonl"))
    ap.add_argument("--families", default=",".join(MATRIX.keys()))
    args = ap.parse_args()

    out = pathlib.Path(args.out)
    out.parent.mkdir(parents=True, exist_ok=True)
    families = [f.strip() for f in args.families.split(",") if f.strip()]
    toolchain = (REPO / "lean-toolchain").read_text().strip()
    stamp = datetime.datetime.now(datetime.timezone.utc).isoformat(timespec="seconds")

    rows = []
    with tempfile.TemporaryDirectory() as td:
        tmp = pathlib.Path(td)

        def run_cell(family, route, size, source):
            f = tmp / f"{family}_{route}_{size}.lean"
            f.write_text(source)
            for run in (1, 2):
                res = compile_once(f)
                row = {"ts": stamp, "toolchain": toolchain, "family": family,
                       "route": route, "size": size, "run": run, **res}
                rows.append(row)
                with out.open("a") as fh:
                    fh.write(json.dumps(row) + "\n")
                status = "ok" if res["ok"] else f"FAIL ({res['error']})"
                print(f"  {family:12s} {route:7s} n={size:<6} run{run}: "
                      f"{res['wall_s']:7.2f}s  {res['max_rss_mib'] or '?':>7} MiB  {status}",
                      flush=True)

        for family in families:
            print(f"[{family}]", flush=True)
            run_cell(family, "none", 0, BASELINES[family])
            spec = MATRIX[family]
            for size in spec["sizes"]:
                for route in spec["routes"]:
                    header, body = spec["gen"](route, size)
                    run_cell(family, route, size, header + body)

    failures = [r for r in rows if not r["ok"]]
    print(f"\n{len(rows)} rows -> {out}; {len(failures)} failures")
    return 0


if __name__ == "__main__":
    sys.exit(main())
