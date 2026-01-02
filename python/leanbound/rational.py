# LeanBound v2 SDK - Rational Number Utilities
# Copyright (c) 2024 LeanBound Contributors. All rights reserved.

"""
Utilities for human-friendly rational number conversion.

This module provides functions to convert floats to fractions in a way
that produces "nice" results for common decimal numbers.

The Problem:
    >>> from fractions import Fraction
    >>> Fraction(0.1)
    Fraction(3602879701896397, 36028797018963968)  # Binary representation!

The Solution:
    >>> from leanbound_v2.rational import to_fraction
    >>> to_fraction(0.1)
    Fraction(1, 10)
"""

from fractions import Fraction
from typing import Union


# Type for things that can be converted to Fraction
Numeric = Union[int, float, Fraction]


def to_fraction(x: Numeric, max_denom: int = 10**12) -> Fraction:
    """
    Convert a numeric value to Fraction with human-friendly results.

    For floats, this function tries to detect "nice" decimal numbers
    (like 0.1, 0.25, 3.14159) and convert them to exact fractions,
    avoiding the binary representation issues of Fraction(float).

    Args:
        x: A number (int, float, or Fraction).
        max_denom: Maximum denominator for fallback limit_denominator.

    Returns:
        A Fraction representing the number.

    Examples:
        >>> to_fraction(0.1)
        Fraction(1, 10)
        >>> to_fraction(0.25)
        Fraction(1, 4)
        >>> to_fraction(3.14159)
        Fraction(314159, 100000)
        >>> to_fraction(Fraction(1, 3))
        Fraction(1, 3)
    """
    if isinstance(x, Fraction):
        return x
    elif isinstance(x, int):
        return Fraction(x)
    else:
        return _float_to_nice_fraction(x, max_denom)


def _float_to_nice_fraction(x: float, max_denom: int = 10**12) -> Fraction:
    """
    Convert a float to a human-friendly Fraction.

    Strategy:
    1. Check if it's an exact integer
    2. Try parsing from string representation (catches 0.1 -> "1/10")
    3. Fall back to limit_denominator
    """
    # Handle special cases
    if x == 0.0:
        return Fraction(0)
    if x == int(x):
        return Fraction(int(x))

    # Try to get a nice fraction from the string representation
    # This works because str(0.1) == "0.1", which is exactly 1/10
    s = str(x)

    # Handle scientific notation (e.g., 1e-10)
    if 'e' in s or 'E' in s:
        # For scientific notation, use limit_denominator
        return Fraction(x).limit_denominator(max_denom)

    # Parse decimal string
    if '.' in s:
        sign = -1 if s.startswith('-') else 1
        s_abs = s.lstrip('-')

        integer_part, decimal_part = s_abs.split('.')
        integer_val = int(integer_part) if integer_part else 0
        decimal_len = len(decimal_part)

        if decimal_len == 0:
            return Fraction(sign * integer_val)

        # Build fraction from decimal: 0.125 -> 125/1000
        decimal_val = int(decimal_part)
        denom = 10 ** decimal_len
        numer = integer_val * denom + decimal_val

        # Reduce the fraction
        result = Fraction(sign * numer, denom)

        # Check if denominator is reasonable
        if result.denominator <= max_denom:
            return result
        else:
            # Fall back to limit_denominator for very long decimals
            return Fraction(x).limit_denominator(max_denom)

    # No decimal point - it's an integer
    return Fraction(int(s))
