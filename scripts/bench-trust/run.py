#!/usr/bin/env python3
"""External compile-benchmark harness for LeanCert verification routes.

Measures what in-process benchmarks cannot: full `lake env lean` wall time
(cold and warm), peak RSS, and success/failure per (family, route, size)
cell. Used to calibrate the auto-mode cost gates and to catch performance
regressions when the verification engine changes.

Usage (from the repo root):
    python3 scripts/bench-trust/run.py [--out results.jsonl] [--families point,finsum]

Families:
    point        end-to-end `interval_decide` log bounds via `leancert.trust`
    integration  checker-level partitioned integration (sin on [0,1])
    subdiv       checker-level per-subinterval bounds (x^2 + sin x on [0,1])
    finsum       checker-level dyadic finite sums (sum of k, 1..n)
    optimization checker-level global branch-and-bound certificates

Routes: kernel (`decide +kernel` / trust option), native (`native_decide`).

By default each cell is compiled twice in a row: run 1 ("cold-ish" — OS caches
may still be warm from a previous cell sharing imports) and run 2 ("warm").
`--runs` changes that count. Rows are appended as JSONL.
"""

import argparse
import datetime
import json
import math
import pathlib
import platform
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


def optimization_file(route: str, n_iters: int) -> tuple[str, str]:
    tac = "decide +kernel" if route == "kernel" else "native_decide"
    header = (
        "import LeanCert.Validity.Bounds\n\n"
        "open LeanCert.Core LeanCert.Validity\n\n"
        "set_option maxHeartbeats 16000000\n\n"
    )
    body = (
        "example : GlobalOpt.checkGlobalUpperBound\n"
        "    (.mul (.var 0) (.var 0))\n"
        "    [⟨-1, 1, by norm_num⟩]\n"
        "    1\n"
        f"    {{ maxIterations := {n_iters}, tolerance := 1/100000,\n"
        "      useMonotonicity := false, taylorDepth := 10 } = true := by\n"
        f"  {tac}\n"
    )
    return header, body


MATRIX = {
    "point": {"gen": point_file, "sizes": [1, 10], "routes": ["kernel", "native", "auto"]},
    "integration": {"gen": integration_file, "sizes": [10, 50, 200, 500], "routes": ["kernel", "native"]},
    "subdiv": {"gen": subdiv_file, "sizes": [16, 64], "routes": ["kernel", "native"]},
    "finsum": {"gen": finsum_file, "sizes": [100, 1000, 10000], "routes": ["kernel", "native"]},
    "optimization": {
        "gen": optimization_file, "sizes": [10, 25, 50], "routes": ["kernel", "native"]
    },
}

BASELINES = {
    "point": "import LeanCert.Tactic\n",
    "integration": "import LeanCert.Validity.Integration\n",
    "subdiv": "import LeanCert.Validity.Bounds\n",
    "finsum": "import LeanCert.Engine.FinSumDyadic\n",
    "optimization": "import LeanCert.Validity.Bounds\n",
}

# ---------------------------------------------------------------- execution

def timed_command(path: pathlib.Path) -> tuple[list[str], str]:
    """Return a platform-specific /usr/bin/time command and RSS unit."""
    if platform.system() == "Darwin":
        return ["/usr/bin/time", "-l", "lake", "env", "lean", str(path)], "bytes"
    if platform.system() == "Linux":
        return [
            "/usr/bin/time", "-f", "__LEANCERT_MAX_RSS_KIB__=%M",
            "lake", "env", "lean", str(path),
        ], "kib"
    return ["lake", "env", "lean", str(path)], "unavailable"


def compile_once(path: pathlib.Path) -> dict:
    start = time.monotonic()
    try:
        cmd, rss_unit = timed_command(path)
        proc = subprocess.run(
            cmd,
            cwd=REPO, capture_output=True, text=True, timeout=TIMEOUT_S,
        )
        wall = time.monotonic() - start
        rss = None
        if rss_unit == "bytes":
            m = re.search(r"(\d+)\s+maximum resident set size", proc.stderr)
            if m:
                rss = int(m.group(1)) / (1024 * 1024)
        elif rss_unit == "kib":
            m = re.search(r"__LEANCERT_MAX_RSS_KIB__=(\d+)", proc.stderr)
            if m:
                rss = int(m.group(1)) / 1024
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
    ap.add_argument("--runs", type=int, default=2,
                    help="compilations per cell (default: 2, interpreted as cold-ish then warm)")
    args = ap.parse_args()
    if args.runs < 1:
        ap.error("--runs must be positive")

    out = pathlib.Path(args.out)
    out.parent.mkdir(parents=True, exist_ok=True)
    families = [f.strip() for f in args.families.split(",") if f.strip()]
    unknown = sorted(set(families) - set(MATRIX))
    if unknown:
        ap.error(f"unknown families: {', '.join(unknown)}")
    toolchain = (REPO / "lean-toolchain").read_text().strip()
    stamp = datetime.datetime.now(datetime.timezone.utc).isoformat(timespec="seconds")
    revision = subprocess.run(
        ["git", "rev-parse", "HEAD"], cwd=REPO, capture_output=True, text=True, check=True
    ).stdout.strip()
    dirty = bool(subprocess.run(
        ["git", "status", "--porcelain"], cwd=REPO, capture_output=True, text=True, check=True
    ).stdout)
    cpu_model = platform.processor() or platform.machine()
    if platform.system() == "Darwin":
        cpu = subprocess.run(
            ["sysctl", "-n", "machdep.cpu.brand_string"],
            capture_output=True, text=True,
        )
        if cpu.returncode == 0 and cpu.stdout.strip():
            cpu_model = cpu.stdout.strip()
    environment = {
        "toolchain": toolchain,
        "git_revision": revision,
        "git_dirty": dirty,
        "os": platform.platform(),
        "architecture": platform.machine(),
        "cpu_model": cpu_model,
        "run_count": args.runs,
    }

    rows = []
    with tempfile.TemporaryDirectory() as td:
        tmp = pathlib.Path(td)

        def run_cell(family, route, size, source):
            f = tmp / f"{family}_{route}_{size}.lean"
            f.write_text(source)
            for run in range(1, args.runs + 1):
                res = compile_once(f)
                row = {
                    "schema": 2, "ts": stamp, **environment,
                    "family": family, "route": route, "size": size,
                    "run": run, "run_kind": "cold-ish" if run == 1 else "warm",
                    **res,
                }
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
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
