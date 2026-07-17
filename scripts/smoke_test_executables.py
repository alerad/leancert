#!/usr/bin/env python3
"""Build and exercise LeanCert's public command-line executables."""

import json
from pathlib import Path
import subprocess
import sys


ROOT = Path(__file__).resolve().parents[1]


def run(*args: str, input_text: str | None = None) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        args,
        cwd=ROOT,
        input=input_text,
        text=True,
        capture_output=True,
        check=True,
    )


def fail(message: str, process: subprocess.CompletedProcess[str] | None = None) -> int:
    print(message, file=sys.stderr)
    if process is not None:
        if process.stdout:
            print(f"stdout:\n{process.stdout}", file=sys.stderr)
        if process.stderr:
            print(f"stderr:\n{process.stderr}", file=sys.stderr)
    return 1


def main() -> int:
    try:
        run("lake", "build", "leancert", "lean_bridge", "check-compat", "leancert-bench")

        cli = run("lake", "exe", "leancert")
        expected_banner = "LeanCert - A Wolfram-Like, Proof-Producing Engine in Lean"
        if cli.stdout.strip() != expected_banner:
            return fail("Unexpected output from the leancert executable.", cli)

        bridge = run(
            "lake",
            "exe",
            "lean_bridge",
            input_text='{"id":1,"method":"ping","params":{}}\n',
        )
        bridge_response = json.loads(bridge.stdout)
        if bridge_response != {"id": 1, "result": "pong"}:
            return fail("The lean_bridge JSON-RPC ping returned an unexpected response.", bridge)

        compat = run("lake", "exe", "check-compat", "--", "--json")
        compat_response = json.loads(compat.stdout)
        if compat_response.get("compatible") is not True:
            return fail("The compatibility checker rejected the repository's Mathlib pin.", compat)
        if compat_response.get("expected_rev") != compat_response.get("found_commit"):
            return fail("The compatibility checker reported inconsistent resolved commits.", compat)

        benchmark = run(
            "lake", "exe", "leancert-bench",
            "--case", "x_minus_x.checked.auto",
            "--samples", "1", "--warmups", "0", "--format", "jsonl",
        )
        benchmark_sample = json.loads(benchmark.stdout)
        if benchmark_sample.get("backend_used") != "dyadic":
            return fail("The benchmark executable did not run its checked Auto smoke case.", benchmark)
    except subprocess.CalledProcessError as error:
        return fail(f"Executable smoke test command failed: {' '.join(error.cmd)}", error)
    except (json.JSONDecodeError, TypeError) as error:
        return fail(f"Executable smoke test returned invalid JSON: {error}")

    print("All public executables built and passed their smoke tests.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
