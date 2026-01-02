# LeanBound v2 SDK - Domain Types
# Copyright (c) 2024 LeanBound Contributors. All rights reserved.

"""
Domain types for LeanBound v2.

This module provides Interval and Box classes for defining verification domains.
Box uses a dictionary interface with named dimensions.

Example:
    >>> from leanbound_v2.domain import Interval, Box
    >>> i = Interval(0, 1)
    >>> box = Box({'x': (0, 1), 'y': (-1, 1)})
    >>> box.var_order()
    ['x', 'y']
"""

from __future__ import annotations
from dataclasses import dataclass
from fractions import Fraction
from typing import Union, Iterator, Any, TYPE_CHECKING

if TYPE_CHECKING:
    from .expr import Expr

from .exceptions import DomainError


# Type for things that can be converted to Fraction
Numeric = Union[int, float, Fraction]

# Type for kernel interval JSON
KernelInterval = dict[str, dict[str, int]]


# Import from rational module (defined separately to avoid circular imports)
from .rational import to_fraction as _to_fraction


@dataclass(frozen=True)
class Interval:
    """
    A closed interval [lo, hi] with exact rational endpoints.

    Intervals are immutable and can be used as dictionary keys.
    """
    lo: Fraction
    hi: Fraction

    def __init__(self, lo: Numeric, hi: Numeric):
        """
        Create an interval [lo, hi].

        Args:
            lo: Lower bound (converted to Fraction).
            hi: Upper bound (converted to Fraction).

        Raises:
            ValueError: If lo > hi.
        """
        lo_frac = _to_fraction(lo)
        hi_frac = _to_fraction(hi)

        if lo_frac > hi_frac:
            raise ValueError(f"Invalid interval: lo={lo_frac} > hi={hi_frac}")

        # Bypass frozen dataclass __setattr__
        object.__setattr__(self, 'lo', lo_frac)
        object.__setattr__(self, 'hi', hi_frac)

    @classmethod
    def point(cls, x: Numeric) -> Interval:
        """Create a point interval [x, x]."""
        return cls(x, x)

    def width(self) -> Fraction:
        """Width of the interval."""
        return self.hi - self.lo

    def midpoint(self) -> Fraction:
        """Midpoint of the interval."""
        return (self.lo + self.hi) / 2

    def __contains__(self, x: Numeric) -> bool:
        """Check if x is in the interval."""
        x_frac = _to_fraction(x)
        return self.lo <= x_frac <= self.hi

    def to_kernel(self) -> KernelInterval:
        """Convert to kernel JSON format."""
        return {
            'lo': {'n': self.lo.numerator, 'd': self.lo.denominator},
            'hi': {'n': self.hi.numerator, 'd': self.hi.denominator}
        }

    def __repr__(self) -> str:
        lo_str = str(self.lo) if self.lo.denominator != 1 else str(self.lo.numerator)
        hi_str = str(self.hi) if self.hi.denominator != 1 else str(self.hi.numerator)
        return f"Interval[{lo_str}, {hi_str}]"

    def __float__(self) -> float:
        """Return midpoint as float (for convenience)."""
        return float(self.midpoint())


@dataclass
class Box:
    """
    A named multi-dimensional domain (product of intervals).

    Box uses a dictionary interface where keys are variable names
    and values are intervals. The order of keys is preserved and
    determines the De Bruijn index mapping.

    Example:
        >>> box = Box({'x': (0, 1), 'y': (-1, 1)})
        >>> box['x']
        Interval[0, 1]
        >>> box.var_order()
        ['x', 'y']
    """
    _intervals: dict[str, Interval]

    def __init__(self, intervals: dict[str, Union[Interval, tuple[Numeric, Numeric]]]):
        """
        Create a Box from a dictionary.

        Args:
            intervals: Dict mapping variable names to intervals.
                       Values can be Interval objects or (lo, hi) tuples.

        Raises:
            ValueError: If the dict is empty.
        """
        if not intervals:
            raise ValueError("Box cannot be empty")

        self._intervals = {}
        for name, val in intervals.items():
            if isinstance(val, Interval):
                self._intervals[name] = val
            elif isinstance(val, tuple) and len(val) == 2:
                self._intervals[name] = Interval(val[0], val[1])
            else:
                raise TypeError(f"Invalid interval specification for '{name}': {val}")

    def __getitem__(self, name: str) -> Interval:
        """Get interval for a variable."""
        return self._intervals[name]

    def __contains__(self, name: str) -> bool:
        """Check if a variable is defined."""
        return name in self._intervals

    def __len__(self) -> int:
        """Number of dimensions."""
        return len(self._intervals)

    def __iter__(self) -> Iterator[str]:
        """Iterate over variable names."""
        return iter(self._intervals)

    def items(self):
        """Iterate over (name, interval) pairs."""
        return self._intervals.items()

    def var_order(self) -> list[str]:
        """
        Return variable names in order.

        The order matches insertion order (Python 3.7+ dict guarantee)
        and determines the De Bruijn index mapping.
        """
        return list(self._intervals.keys())

    def to_kernel_list(self) -> list[KernelInterval]:
        """Convert to list of kernel intervals in var_order."""
        return [self._intervals[name].to_kernel() for name in self.var_order()]

    def validate_expr(self, expr: 'Expr') -> None:
        """
        Validate that an expression only uses variables defined in this box.

        Args:
            expr: Expression to validate.

        Raises:
            DomainError: If expression uses undefined variables.
        """
        free_vars = expr.free_vars()
        defined_vars = set(self._intervals.keys())

        undefined = free_vars - defined_vars
        if undefined:
            var_list = ', '.join(f"'{v}'" for v in sorted(undefined))
            raise DomainError(f"Variable {var_list} not defined in domain")

    def __repr__(self) -> str:
        parts = [f"'{k}': {v}" for k, v in self._intervals.items()]
        return f"Box({{{', '.join(parts)}}})"


def normalize_domain(
    domain: Union[Interval, Box, tuple[Numeric, Numeric], dict[str, Any]],
    default_var: str = 'x'
) -> Box:
    """
    Normalize various domain specifications to a Box.

    This allows flexible input while ensuring consistent internal representation.

    Args:
        domain: Can be:
            - Box: returned as-is
            - Interval: wrapped in Box with default_var
            - tuple (lo, hi): converted to Interval then Box
            - dict: converted to Box

        default_var: Variable name to use for 1D domains.

    Returns:
        A Box instance.
    """
    if isinstance(domain, Box):
        return domain
    elif isinstance(domain, Interval):
        return Box({default_var: domain})
    elif isinstance(domain, tuple) and len(domain) == 2:
        return Box({default_var: domain})
    elif isinstance(domain, dict):
        return Box(domain)
    else:
        raise TypeError(f"Cannot normalize domain of type {type(domain).__name__}")
