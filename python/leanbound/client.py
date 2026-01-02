# LeanBound v2 SDK - Client
# Copyright (c) 2024 LeanBound Contributors. All rights reserved.

"""
Low-level client for communication with the Lean kernel.

This module handles subprocess management and JSON-RPC protocol.
It should not be used directly by end users - use the Solver class instead.
"""

from __future__ import annotations
import json
import os
import subprocess
import shutil
from pathlib import Path
from typing import Optional, Any
from fractions import Fraction

from .exceptions import BridgeError
from .domain import Interval, Box


class LeanClient:
    """
    Low-level client for the Lean math kernel.

    Uses a subprocess to communicate with the compiled lean_bridge executable
    via JSON-RPC over stdin/stdout.

    This class manages the subprocess lifecycle and should be used as a
    context manager to ensure proper cleanup.

    Example:
        with LeanClient() as client:
            result = client.call('ping', {})
    """

    def __init__(self, binary_path: Optional[str] = None):
        """
        Initialize the client.

        Args:
            binary_path: Path to lean_bridge executable. If None, searches
                        for it in standard locations.
        """
        self.binary_path = self._find_binary(binary_path)
        self._process: Optional[subprocess.Popen] = None
        self._request_id = 0

    def _find_binary(self, binary_path: Optional[str]) -> str:
        """Find the lean_bridge binary."""
        if binary_path and os.path.isfile(binary_path):
            return binary_path

        # Try relative to this file (development mode)
        module_dir = Path(__file__).parent
        candidates = [
            # From python/leanbound_v2 -> .lake/build/bin
            module_dir.parent.parent / ".lake" / "build" / "bin" / "lean_bridge",
            module_dir.parent.parent.parent / ".lake" / "build" / "bin" / "lean_bridge",
            # From current working directory
            Path.cwd() / ".lake" / "build" / "bin" / "lean_bridge",
        ]

        for candidate in candidates:
            if candidate.is_file():
                return str(candidate)

        # Try PATH
        path_binary = shutil.which("lean_bridge")
        if path_binary:
            return path_binary

        raise FileNotFoundError(
            "Could not find lean_bridge binary. "
            "Please build it with 'lake build lean_bridge' or specify binary_path."
        )

    def _ensure_process(self) -> subprocess.Popen:
        """Ensure the subprocess is running."""
        if self._process is None or self._process.poll() is not None:
            self._process = subprocess.Popen(
                [self.binary_path],
                stdin=subprocess.PIPE,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                text=True,
                bufsize=1,
            )
        return self._process

    def call(self, method: str, params: dict[str, Any]) -> Any:
        """
        Make a JSON-RPC call to the bridge.

        Args:
            method: The RPC method name.
            params: Parameters for the method.

        Returns:
            The result from the bridge.

        Raises:
            BridgeError: If the call fails.
        """
        proc = self._ensure_process()

        self._request_id += 1
        request = {
            "id": self._request_id,
            "method": method,
            "params": params,
        }

        # Send request
        request_json = json.dumps(request)
        assert proc.stdin is not None
        proc.stdin.write(request_json + "\n")
        proc.stdin.flush()

        # Read response
        assert proc.stdout is not None
        response_line = proc.stdout.readline()
        if not response_line:
            stderr = proc.stderr.read() if proc.stderr else ""
            raise BridgeError(f"Bridge process died. stderr: {stderr}")

        response = json.loads(response_line)

        # Check for errors
        if "error" in response and response["error"] is not None:
            raise BridgeError(str(response["error"]))

        return response.get("result")

    def ping(self) -> str:
        """Test connection to the bridge."""
        return self.call("ping", {})

    def eval_interval(
        self,
        expr_json: dict,
        box_json: list[dict],
        taylor_depth: int = 10,
    ) -> dict:
        """Evaluate an expression over a box."""
        return self.call("eval_interval", {
            "expr": expr_json,
            "box": box_json,
            "taylorDepth": taylor_depth,
        })

    def global_min(
        self,
        expr_json: dict,
        box_json: list[dict],
        max_iters: int = 1000,
        tolerance: dict = {'n': 1, 'd': 1000},
        use_monotonicity: bool = True,
        taylor_depth: int = 10,
    ) -> dict:
        """Find global minimum."""
        return self.call("global_min", {
            "expr": expr_json,
            "box": box_json,
            "maxIters": max_iters,
            "tolerance": tolerance,
            "useMonotonicity": use_monotonicity,
            "taylorDepth": taylor_depth,
        })

    def global_max(
        self,
        expr_json: dict,
        box_json: list[dict],
        max_iters: int = 1000,
        tolerance: dict = {'n': 1, 'd': 1000},
        use_monotonicity: bool = True,
        taylor_depth: int = 10,
    ) -> dict:
        """Find global maximum."""
        return self.call("global_max", {
            "expr": expr_json,
            "box": box_json,
            "maxIters": max_iters,
            "tolerance": tolerance,
            "useMonotonicity": use_monotonicity,
            "taylorDepth": taylor_depth,
        })

    def check_bound(
        self,
        expr_json: dict,
        box_json: list[dict],
        bound: dict,
        is_upper_bound: bool,
        taylor_depth: int = 10,
    ) -> dict:
        """Check if a bound holds."""
        return self.call("check_bound", {
            "expr": expr_json,
            "box": box_json,
            "bound": bound,
            "isUpperBound": is_upper_bound,
            "taylorDepth": taylor_depth,
        })

    def integrate(
        self,
        expr_json: dict,
        interval_json: dict,
        partitions: int = 10,
        taylor_depth: int = 10,
    ) -> dict:
        """Compute integral bounds."""
        return self.call("integrate", {
            "expr": expr_json,
            "interval": interval_json,
            "partitions": partitions,
            "taylorDepth": taylor_depth,
        })

    def find_roots(
        self,
        expr_json: dict,
        interval_json: dict,
        max_iter: int = 1000,
        tolerance: dict = {'n': 1, 'd': 1000},
        taylor_depth: int = 10,
    ) -> dict:
        """Find roots using bisection."""
        return self.call("find_roots", {
            "expr": expr_json,
            "interval": interval_json,
            "maxIter": max_iter,
            "tolerance": tolerance,
            "taylorDepth": taylor_depth,
        })

    def verify_adaptive(
        self,
        expr_json: dict,
        box_json: list[dict],
        bound: dict,
        is_upper_bound: bool,
        max_iters: int = 1000,
        tolerance: dict = {'n': 1, 'd': 1000},
        taylor_depth: int = 10,
    ) -> dict:
        """
        Verify a bound using adaptive optimization.

        This method verifies f <= c (upper) or f >= c (lower) by
        minimizing c - f (for upper) or f - c (for lower) and checking
        if the minimum is >= 0.
        """
        return self.call("verify_adaptive", {
            "expr": expr_json,
            "box": box_json,
            "bound": bound,
            "isUpperBound": is_upper_bound,
            "maxIters": max_iters,
            "tolerance": tolerance,
            "taylorDepth": taylor_depth,
        })

    def find_unique_root(
        self,
        expr_json: dict,
        interval_json: dict,
        taylor_depth: int = 10,
    ) -> dict:
        """
        Find a unique root using Newton contraction.

        Checks if Newton iteration contracts, which proves both existence
        and uniqueness of a root in the interval.

        Returns a dict with:
          - unique: bool (True if unique root proven)
          - reason: str ('newton_contraction', 'no_contraction', 'newton_step_failed')
          - interval: dict with lo/hi (refined interval if Newton succeeded)
        """
        return self.call("find_unique_root", {
            "expr": expr_json,
            "interval": interval_json,
            "taylorDepth": taylor_depth,
        })

    def close(self) -> None:
        """Close the subprocess."""
        if self._process is not None:
            try:
                self._process.terminate()
                self._process.wait(timeout=5)
            except subprocess.TimeoutExpired:
                self._process.kill()
            finally:
                self._process = None

    def __enter__(self) -> LeanClient:
        """Context manager entry."""
        return self

    def __exit__(self, *args) -> None:
        """Context manager exit."""
        self.close()


def _parse_rat(data: dict) -> Fraction:
    """Parse a rational from kernel JSON."""
    return Fraction(data['n'], data['d'])


def _parse_interval(data: dict) -> Interval:
    """Parse an interval from kernel JSON."""
    return Interval(_parse_rat(data['lo']), _parse_rat(data['hi']))
