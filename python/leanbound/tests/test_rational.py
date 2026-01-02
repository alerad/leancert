# Tests for rational.py - Human-friendly fraction conversion
# TDD: Write tests first, then implement

import pytest
from fractions import Fraction


class TestToFraction:
    """Tests for to_fraction() - human-friendly conversion."""

    def test_integer_conversion(self):
        from leanbound_v2.rational import to_fraction

        assert to_fraction(0) == Fraction(0)
        assert to_fraction(1) == Fraction(1)
        assert to_fraction(-5) == Fraction(-5)
        assert to_fraction(42) == Fraction(42)

    def test_fraction_passthrough(self):
        from leanbound_v2.rational import to_fraction

        f = Fraction(1, 3)
        assert to_fraction(f) is f  # Should return same object

    def test_float_exact_integer(self):
        from leanbound_v2.rational import to_fraction

        assert to_fraction(0.0) == Fraction(0)
        assert to_fraction(1.0) == Fraction(1)
        assert to_fraction(-5.0) == Fraction(-5)

    def test_simple_decimals(self):
        """The main use case: common decimal numbers."""
        from leanbound_v2.rational import to_fraction

        # These are the problematic cases with Fraction(float)
        assert to_fraction(0.1) == Fraction(1, 10)
        assert to_fraction(0.2) == Fraction(1, 5)  # 1/5 after reduction
        assert to_fraction(0.25) == Fraction(1, 4)
        assert to_fraction(0.5) == Fraction(1, 2)
        assert to_fraction(0.125) == Fraction(1, 8)

    def test_negative_decimals(self):
        from leanbound_v2.rational import to_fraction

        assert to_fraction(-0.1) == Fraction(-1, 10)
        assert to_fraction(-0.5) == Fraction(-1, 2)
        assert to_fraction(-3.14) == Fraction(-314, 100)  # = -157/50 after reduction

    def test_longer_decimals(self):
        from leanbound_v2.rational import to_fraction

        assert to_fraction(3.14159) == Fraction(314159, 100000)
        assert to_fraction(0.001) == Fraction(1, 1000)
        assert to_fraction(0.0001) == Fraction(1, 10000)

    def test_decimals_with_integer_part(self):
        from leanbound_v2.rational import to_fraction

        assert to_fraction(1.5) == Fraction(3, 2)
        assert to_fraction(2.25) == Fraction(9, 4)
        assert to_fraction(10.1) == Fraction(101, 10)

    def test_pi_approximation(self):
        from leanbound_v2.rational import to_fraction

        # Common pi approximations
        assert to_fraction(3.14) == Fraction(314, 100)
        assert to_fraction(3.14159) == Fraction(314159, 100000)
        assert to_fraction(3.141592653) == Fraction(3141592653, 1000000000)

    def test_scientific_notation(self):
        """Scientific notation falls back to limit_denominator."""
        from leanbound_v2.rational import to_fraction

        # These use limit_denominator since str() gives scientific notation
        result = to_fraction(1e-10)
        assert result.denominator <= 10**12
        assert abs(float(result) - 1e-10) < 1e-20

        result = to_fraction(1e10)
        assert result == Fraction(10000000000)


class TestIntervalWithNiceFractions:
    """Test that Interval uses nice fractions for floats."""

    def test_interval_nice_fractions(self):
        from leanbound_v2.domain import Interval

        # This should produce nice fractions, not binary approximations
        i = Interval(0.1, 0.9)
        assert i.lo == Fraction(1, 10)
        assert i.hi == Fraction(9, 10)

    def test_interval_common_bounds(self):
        from leanbound_v2.domain import Interval

        i = Interval(0, 0.5)
        assert i.lo == Fraction(0)
        assert i.hi == Fraction(1, 2)

        i = Interval(-0.25, 0.25)
        assert i.lo == Fraction(-1, 4)
        assert i.hi == Fraction(1, 4)


class TestConstWithNiceFractions:
    """Test that Const uses nice fractions for floats."""

    def test_const_nice_fractions(self):
        from leanbound_v2.expr import const

        c = const(0.1)
        assert c.value == Fraction(1, 10)

        c = const(0.5)
        assert c.value == Fraction(1, 2)

    def test_const_in_expression(self):
        from leanbound_v2.expr import var, const

        x = var('x')
        expr = x + 0.1  # Should produce nice fraction

        # Compile and check the constant
        compiled = expr.compile(['x'])
        # The 0.1 should become 1/10
        e2 = compiled['e2']  # The constant part
        assert e2['kind'] == 'const'
        assert e2['val'] == {'n': 1, 'd': 10}


class TestVerifyBoundWithNiceFractions:
    """Test that verify_bound uses nice fractions."""

    def test_verify_bound_uses_nice_fractions(self):
        """Verify that 0.5 as a bound becomes 1/2."""
        # This is a unit test - doesn't need bridge
        from leanbound_v2.rational import to_fraction

        bound = 0.5
        bound_frac = to_fraction(bound)
        bound_json = {'n': bound_frac.numerator, 'd': bound_frac.denominator}

        assert bound_json == {'n': 1, 'd': 2}

    def test_verify_bound_decimal_precision(self):
        """Verify common decimal bounds are exact."""
        from leanbound_v2.rational import to_fraction

        # These are the values users commonly pass
        test_cases = [
            (0.1, {'n': 1, 'd': 10}),
            (0.01, {'n': 1, 'd': 100}),
            (1.5, {'n': 3, 'd': 2}),
            (-0.5, {'n': -1, 'd': 2}),
        ]

        for val, expected in test_cases:
            frac = to_fraction(val)
            json_val = {'n': frac.numerator, 'd': frac.denominator}
            assert json_val == expected, f"Failed for {val}: got {json_val}"
