#!/usr/bin/env python3
"""Reject reintroduction of retired solver-protocol compatibility APIs."""

from __future__ import annotations

from pathlib import Path
import re
import sys


ROOT = Path(__file__).resolve().parents[1]
PRODUCTION_ROOT = ROOT / "LeanCert" / "Tactic"

FORBIDDEN = (
    "legacyExceptionAdapter",
    "legacyInconclusive",
    "solveReported",
    "solveReportedResult",
    "StrategyId.legacy",
    "proveWithTactic",
    "proveWithTacticReported",
    "proveWithTacticReportedResult",
    "closeCertificateGoalReported",
    "closeCertificateGoal",
    "closeBridgeWithVerificationReported",
    "closeBridgeWithNativeDecide",
    "intervalArgmaxCoreReported",
    "intervalArgminCoreReported",
    "intervalRootsCoreReported",
    "intervalUniqueRootCoreReported",
    "optBoundCoreReported",
    "multivariateBoundCoreReported",
    "rootBoundCoreReported",
    "proveClosedExpressionBoundReported",
    "tryDyadicBoundReported",
    "intervalBoundCoreReported",
    "finSumBoundCoreReported",
    "integralExactCoreReported",
    "integralSearchCoreReported",
    "intervalBoundSubdivWithDepthReported",
    "intervalArgmaxCore",
    "intervalArgminCore",
    "intervalRootsCore",
    "intervalUniqueRootCore",
    "intervalMinimizeCore",
    "intervalMaximizeCore",
    "intervalMinimizeMvCore",
    "intervalMaximizeMvCore",
    "optBoundCore",
    "multivariateBoundCore",
    "rootBoundCore",
    "proveClosedExpressionBound",
    "finSumWitnessCore",
    "finSumWitnessAutoCore",
    "finSumBoundCore",
    "integralExactCore",
    "integralSearchCore",
    "intervalBoundSubdivWithDepth",
)


def violations(root: Path) -> list[tuple[Path, int, str]]:
    found: list[tuple[Path, int, str]] = []
    for path in sorted(root.rglob("*.lean")):
        for line_number, line in enumerate(
            path.read_text(encoding="utf-8").splitlines(), start=1
        ):
            for identifier in FORBIDDEN:
                token = re.escape(identifier)
                if re.search(
                    rf"(?<![A-Za-z0-9_]){token}(?![A-Za-z0-9_])",
                    line,
                ):
                    found.append((path, line_number, identifier))
    return found


def main() -> int:
    found = violations(PRODUCTION_ROOT)
    if found:
        print("Retired solver-protocol identifiers found:", file=sys.stderr)
        for path, line_number, identifier in found:
            relative = path.relative_to(ROOT)
            print(
                f"  - {relative}:{line_number}: {identifier}",
                file=sys.stderr,
            )
        return 1
    print("Solver protocol policy check passed.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
