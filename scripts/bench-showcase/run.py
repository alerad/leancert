#!/usr/bin/env python3
"""Measure each curated showcase proof in an isolated Lean process."""

from __future__ import annotations

import argparse
import json
import platform
from pathlib import Path
import statistics
import subprocess
import tempfile
import time


ROOT = Path(__file__).resolve().parents[2]
CASES = {
    "point_log": """import LeanCert.Tactic
example : Real.log 2 < 7 / 10 := by leancert
""",
    "quantified_nonlinear": """import LeanCert.Tactic
example : ∀ x ∈ Set.Icc (0 : ℝ) 1, Real.exp x * Real.cos x ≤ 3 := by leancert
""",
    "multivariate_box": """import LeanCert.Tactic
example : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
    x + y ≤ (2 : ℚ) := by leancert
""",
    "unique_root": """import LeanCert.Tactic
example : ∃! x, x ∈ Set.Icc (1 : ℝ) 2 ∧ x ^ 2 - 2 = 0 := by leancert
""",
    "exact_integral": """import LeanCert.Tactic
example : (∫ x in (0 : ℝ)..1, x ^ 2) = 1 / 3 := by leancert
""",
    "qproduct_limit": """import LeanCert.QProduct
open LeanCert.QProduct
example : ((19 / 36 : ℚ) : ℝ) ≤ primeLambda ∧
    primeLambda ≤ ((7 / 12 : ℚ) : ℝ) :=
  LeanCert.Validity.verify_limit_interval
    primeLambda_le_shiftedTrunc shiftedTrunc_sub_tail_le_primeLambda
    1 (19 / 36) (7 / 12) (by native_decide)
""",
}


def git(*args: str) -> str:
    return subprocess.run(
        ["git", *args], cwd=ROOT, text=True, capture_output=True, check=True
    ).stdout.strip()


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--runs", type=int, default=3)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    if args.runs < 1:
        parser.error("--runs must be positive")

    rows = []
    with tempfile.TemporaryDirectory(prefix="leancert-showcase-bench-") as tmp:
        directory = Path(tmp)
        for name, source in CASES.items():
            path = directory / f"{name}.lean"
            path.write_text(source, encoding="utf-8")
            samples = []
            for _ in range(args.runs):
                started = time.perf_counter()
                subprocess.run(
                    ["lake", "env", "lean", str(path)],
                    cwd=ROOT,
                    check=True,
                    stdout=subprocess.DEVNULL,
                    stderr=subprocess.DEVNULL,
                )
                samples.append(time.perf_counter() - started)
            rows.append(
                {
                    "case": name,
                    "runs": args.runs,
                    "seconds": [round(value, 3) for value in samples],
                    "median_seconds": round(statistics.median(samples), 3),
                    "min_seconds": round(min(samples), 3),
                    "max_seconds": round(max(samples), 3),
                }
            )

    payload = {
        "schema": 1,
        "metric": "isolated warm end-to-end `lake env lean` wall time",
        "lean_toolchain": (ROOT / "lean-toolchain").read_text().strip(),
        "mathlib_revision": "v4.32.2",
        "git_commit": git("rev-parse", "HEAD"),
        "git_dirty": bool(git("status", "--porcelain")),
        "platform": platform.platform(),
        "machine": platform.machine(),
        "processor": platform.processor(),
        "cases": rows,
    }
    rendered = json.dumps(payload, indent=2) + "\n"
    if args.output:
        destination = args.output
        if not destination.is_absolute():
            destination = ROOT / destination
        destination.parent.mkdir(parents=True, exist_ok=True)
        destination.write_text(rendered, encoding="utf-8")
    else:
        print(rendered, end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
