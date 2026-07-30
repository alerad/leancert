"""Unit tests for the external trust benchmark harness.

These tests cover command construction and result parsing only.  The expensive
Lean calibration matrix remains an explicit release-validation step.
"""

from __future__ import annotations

import importlib.util
import pathlib
import types
import unittest
from unittest import mock


ROOT = pathlib.Path(__file__).resolve().parents[2]
RUNNER = ROOT / "scripts" / "bench-trust" / "run.py"
SPEC = importlib.util.spec_from_file_location("leancert_bench_trust", RUNNER)
assert SPEC is not None and SPEC.loader is not None
bench_trust = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(bench_trust)


class BenchTrustTests(unittest.TestCase):
    def test_platform_specific_time_commands(self) -> None:
        path = pathlib.Path("/tmp/example.lean")
        with mock.patch.object(bench_trust.platform, "system", return_value="Darwin"):
            command, unit = bench_trust.timed_command(path)
        self.assertEqual(command[:2], ["/usr/bin/time", "-l"])
        self.assertEqual(unit, "bytes")

        with mock.patch.object(bench_trust.platform, "system", return_value="Linux"):
            command, unit = bench_trust.timed_command(path)
        self.assertEqual(command[:3], ["/usr/bin/time", "-f",
                                      "__LEANCERT_MAX_RSS_KIB__=%M"])
        self.assertEqual(unit, "kib")

    def test_linux_rss_is_normalized_to_mib(self) -> None:
        proc = types.SimpleNamespace(
            returncode=0,
            stdout="",
            stderr="__LEANCERT_MAX_RSS_KIB__=2048\n",
        )
        with (
            mock.patch.object(
                bench_trust, "timed_command", return_value=(["fake"], "kib")
            ),
            mock.patch.object(bench_trust.subprocess, "run", return_value=proc),
        ):
            result = bench_trust.compile_once(pathlib.Path("/tmp/example.lean"))
        self.assertTrue(result["ok"])
        self.assertEqual(result["max_rss_mib"], 2)

    def test_optimization_family_generates_both_routes(self) -> None:
        _header, kernel = bench_trust.optimization_file("kernel", 25)
        _header, native = bench_trust.optimization_file("native", 25)
        self.assertIn("maxIterations := 25", kernel)
        self.assertIn("decide +kernel", kernel)
        self.assertIn("native_decide", native)
        self.assertIn("optimization", bench_trust.MATRIX)


if __name__ == "__main__":
    unittest.main()
