# LeanBound v2 SDK - Configuration
# Copyright (c) 2024 LeanBound Contributors. All rights reserved.

"""Configuration settings for LeanBound v2."""

from __future__ import annotations
from dataclasses import dataclass
from fractions import Fraction


@dataclass
class Config:
    """
    Configuration for verification requests.

    Attributes:
        taylor_depth: Depth of Taylor expansion for interval arithmetic.
                     Higher values give tighter bounds but are slower.
        max_iters: Maximum iterations for optimization/root finding.
        tolerance: Desired precision (as a fraction).
        use_monotonicity: Use monotonicity pruning in optimization.
        timeout_sec: Timeout in seconds.
    """
    taylor_depth: int = 10
    max_iters: int = 1000
    tolerance: Fraction = Fraction(1, 1000)
    use_monotonicity: bool = True
    timeout_sec: float = 60.0

    def __post_init__(self):
        # Convert tolerance to Fraction if given as float
        if isinstance(self.tolerance, float):
            self.tolerance = Fraction(self.tolerance).limit_denominator(10**12)

    @classmethod
    def low_precision(cls) -> Config:
        """Fast, lower precision configuration."""
        return cls(
            taylor_depth=5,
            max_iters=100,
            tolerance=Fraction(1, 100),
        )

    @classmethod
    def medium_precision(cls) -> Config:
        """Balanced precision/speed configuration (default)."""
        return cls()

    @classmethod
    def high_precision(cls) -> Config:
        """High precision configuration."""
        return cls(
            taylor_depth=20,
            max_iters=5000,
            tolerance=Fraction(1, 100000),
        )

    def to_kernel(self) -> dict:
        """Convert to kernel-compatible format."""
        return {
            'taylorDepth': self.taylor_depth,
            'maxIters': self.max_iters,
            'tolerance': {'n': self.tolerance.numerator, 'd': self.tolerance.denominator},
            'useMonotonicity': self.use_monotonicity,
        }

    def __repr__(self) -> str:
        return (
            f"Config(taylor_depth={self.taylor_depth}, "
            f"max_iters={self.max_iters}, "
            f"tolerance={self.tolerance})"
        )
