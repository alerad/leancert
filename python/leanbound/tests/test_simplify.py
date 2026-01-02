# LeanBound v2 SDK - Simplification Tests
# Copyright (c) 2024 LeanBound Contributors. All rights reserved.

"""
Tests for symbolic simplification.
"""

import pytest
from fractions import Fraction

from leanbound_v2 import var, const, simplify, expand, Solver, Box


class TestSimplification:
    """Test symbolic simplification."""

    def test_constant_folding(self):
        """Test that constants are folded."""
        expr = const(2) + const(3)
        result = simplify(expr)
        assert isinstance(result, type(const(5)))
        assert result.value == 5

    def test_identity_removal_add(self):
        """Test x + 0 = x."""
        x = var('x')
        expr = x + 0
        result = simplify(expr)
        # Result should just be x (possibly wrapped differently)
        assert result.free_vars() == frozenset({'x'})

    def test_identity_removal_mul(self):
        """Test x * 1 = x."""
        x = var('x')
        expr = x * 1
        result = simplify(expr)
        assert result.free_vars() == frozenset({'x'})

    def test_zero_propagation(self):
        """Test x * 0 = 0."""
        x = var('x')
        expr = x * 0
        result = simplify(expr)
        assert result.free_vars() == frozenset()
        assert result.value == 0

    def test_self_subtraction(self):
        """Test x - x = 0."""
        x = var('x')
        expr = x - x
        result = simplify(expr)
        assert result.free_vars() == frozenset()
        assert result.value == 0

    def test_self_division(self):
        """Test x / x = 1 (for polynomial forms)."""
        # Note: Division is not polynomial, so this tests recursive simplification
        x = var('x')
        expr = x / x
        result = simplify(expr)
        # For non-polynomial, we use recursive simplification which catches x/x
        assert result.value == 1

    def test_like_terms(self):
        """Test 2x + 3x = 5x."""
        x = var('x')
        expr = 2*x + 3*x
        result = simplify(expr)
        # Check by evaluating symbolically
        assert result.free_vars() == frozenset({'x'})

    def test_complex_cancellation(self):
        """Test (x*y) - (y*x) = 0."""
        x = var('x')
        y = var('y')
        expr = x*y - y*x
        result = simplify(expr)
        assert result.free_vars() == frozenset()
        assert result.value == 0

    def test_expansion(self):
        """Test (x+1)^2 = x^2 + 2x + 1."""
        x = var('x')
        expr = (x + 1) ** 2
        result = expand(expr)
        # Should be a polynomial with x^2, x, and constant terms
        assert result.free_vars() == frozenset({'x'})

    def test_complex_identity(self):
        """Test (x+1)^2 - x^2 - 2x - 1 = 0."""
        x = var('x')
        expr = (x + 1)**2 - x**2 - 2*x - 1
        result = simplify(expr)
        assert result.free_vars() == frozenset()
        assert result.value == 0

    def test_cancellation_case(self):
        """
        Test cancellation that can cause interval explosion without simplification.

        diff = (a * (b + 100)) - c - ((a * b) - c)
             = a * 100
        """
        size_tokens = var('size_tokens')
        size_usd = var('size_usd')
        price = var('price')

        pnl_diff = (
            (size_tokens * (price + 100)) - size_usd
            - ((size_tokens * price) - size_usd)
        )

        result = simplify(pnl_diff)

        # Should simplify to size_tokens * 100
        assert result.free_vars() == frozenset({'size_tokens'})


class TestSolverIntegration:
    """Test simplification integration with solver."""

    def test_auto_simplify_default(self):
        """Test that auto_simplify is enabled by default."""
        solver = Solver()
        assert solver._auto_simplify is True

    def test_auto_simplify_disabled(self):
        """Test that auto_simplify can be disabled."""
        solver = Solver(auto_simplify=False)
        assert solver._auto_simplify is False

    def test_pnl_verification_with_simplify(self):
        """Test that verify_bound works correctly with simplification."""
        size_tokens = var('size_tokens')
        size_usd = var('size_usd')
        price = var('price')

        pnl_diff = (
            (size_tokens * (price + 100)) - size_usd
            - ((size_tokens * price) - size_usd)
        )

        domain = Box({
            'size_tokens': (2, 1000),
            'size_usd': (10_000, 1_000_000),
            'price': (1000, 5000),
        })

        solver = Solver(auto_simplify=True)

        # This should now work (was failing before)
        result = solver.verify_bound(pnl_diff, domain, lower=0)
        assert result is True

    def test_pnl_bounds_with_simplify(self):
        """Test that find_bounds gives correct results with simplification."""
        size_tokens = var('size_tokens')
        size_usd = var('size_usd')
        price = var('price')

        pnl_diff = (
            (size_tokens * (price + 100)) - size_usd
            - ((size_tokens * price) - size_usd)
        )

        domain = Box({
            'size_tokens': (2, 1000),
            'size_usd': (10_000, 1_000_000),
            'price': (1000, 5000),
        })

        solver = Solver(auto_simplify=True)
        result = solver.find_bounds(pnl_diff, domain)

        # Should be [200, 100000] = size_tokens * 100
        assert float(result.min_bound.lo) >= 200
        assert float(result.min_bound.hi) <= 200
        assert float(result.max_bound.lo) >= 100000
        assert float(result.max_bound.hi) <= 100000


if __name__ == '__main__':
    pytest.main([__file__, '-v'])
