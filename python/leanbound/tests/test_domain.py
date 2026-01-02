# Tests for domain.py - Interval and Box
# TDD: Write tests first, then implement

import pytest
from fractions import Fraction


class TestInterval:
    """Tests for Interval creation and behavior."""

    def test_create_from_floats(self):
        from leanbound_v2.domain import Interval
        i = Interval(0.0, 1.0)
        assert float(i.lo) == 0.0
        assert float(i.hi) == 1.0

    def test_create_from_ints(self):
        from leanbound_v2.domain import Interval
        i = Interval(0, 1)
        assert i.lo == Fraction(0)
        assert i.hi == Fraction(1)

    def test_create_from_fractions(self):
        from leanbound_v2.domain import Interval
        i = Interval(Fraction(1, 3), Fraction(2, 3))
        assert i.lo == Fraction(1, 3)
        assert i.hi == Fraction(2, 3)

    def test_invalid_interval_raises(self):
        from leanbound_v2.domain import Interval
        with pytest.raises(ValueError, match="Invalid interval"):
            Interval(1, 0)  # lo > hi

    def test_singleton(self):
        from leanbound_v2.domain import Interval
        i = Interval.point(0.5)
        assert i.lo == i.hi

    def test_width(self):
        from leanbound_v2.domain import Interval
        i = Interval(0, 1)
        assert i.width() == Fraction(1)

    def test_midpoint(self):
        from leanbound_v2.domain import Interval
        i = Interval(0, 1)
        assert i.midpoint() == Fraction(1, 2)

    def test_contains(self):
        from leanbound_v2.domain import Interval
        i = Interval(0, 1)
        assert 0.5 in i
        assert 0 in i
        assert 1 in i
        assert 2 not in i
        assert -1 not in i

    def test_to_kernel(self):
        from leanbound_v2.domain import Interval
        i = Interval(Fraction(1, 2), Fraction(3, 4))
        kernel = i.to_kernel()
        assert kernel == {
            'lo': {'n': 1, 'd': 2},
            'hi': {'n': 3, 'd': 4}
        }

    def test_repr(self):
        from leanbound_v2.domain import Interval
        i = Interval(0, 1)
        assert '[0, 1]' in repr(i)


class TestBox:
    """Tests for Box - named multi-dimensional domain."""

    def test_create_from_dict(self):
        from leanbound_v2.domain import Box
        box = Box({'x': (0, 1), 'y': (-1, 1)})
        assert 'x' in box
        assert 'y' in box
        assert len(box) == 2

    def test_create_from_dict_with_intervals(self):
        from leanbound_v2.domain import Box, Interval
        box = Box({'x': Interval(0, 1), 'y': Interval(-1, 1)})
        assert box['x'] == Interval(0, 1)

    def test_getitem(self):
        from leanbound_v2.domain import Box, Interval
        box = Box({'x': (0, 1)})
        assert box['x'] == Interval(0, 1)

    def test_iter(self):
        from leanbound_v2.domain import Box
        box = Box({'x': (0, 1), 'y': (-1, 1)})
        keys = list(box)
        assert 'x' in keys
        assert 'y' in keys

    def test_var_order(self):
        """Variable order should be deterministic (insertion order in Python 3.7+)."""
        from leanbound_v2.domain import Box
        box = Box({'x': (0, 1), 'y': (-1, 1), 'z': (0, 2)})
        assert box.var_order() == ['x', 'y', 'z']

    def test_to_kernel_list(self):
        """Convert to list of kernel intervals in var_order."""
        from leanbound_v2.domain import Box
        box = Box({'x': (0, 1), 'y': (2, 3)})
        kernel_list = box.to_kernel_list()
        assert len(kernel_list) == 2
        assert kernel_list[0] == {'lo': {'n': 0, 'd': 1}, 'hi': {'n': 1, 'd': 1}}
        assert kernel_list[1] == {'lo': {'n': 2, 'd': 1}, 'hi': {'n': 3, 'd': 1}}

    def test_validate_expr_vars(self):
        """Check that expression uses only variables defined in box."""
        from leanbound_v2.domain import Box
        from leanbound_v2.expr import var

        box = Box({'x': (0, 1), 'y': (-1, 1)})
        x = var('x')
        y = var('y')
        z = var('z')

        # Should pass
        box.validate_expr(x + y)

        # Should fail - z not in box
        from leanbound_v2.exceptions import DomainError
        with pytest.raises(DomainError, match="Variable 'z' not defined"):
            box.validate_expr(x + z)

    def test_1d_box(self):
        """Single dimension box."""
        from leanbound_v2.domain import Box
        box = Box({'x': (0, 1)})
        assert len(box) == 1
        assert box.var_order() == ['x']

    def test_empty_box_raises(self):
        from leanbound_v2.domain import Box
        with pytest.raises(ValueError, match="Box cannot be empty"):
            Box({})


class TestDomainNormalization:
    """Tests for normalizing different domain inputs."""

    def test_normalize_interval_to_box(self):
        from leanbound_v2.domain import normalize_domain, Interval, Box

        # For 1D expressions, an Interval should become a Box with 'x'
        domain = normalize_domain(Interval(0, 1), default_var='x')
        assert isinstance(domain, Box)
        assert domain.var_order() == ['x']

    def test_normalize_tuple_to_interval(self):
        from leanbound_v2.domain import normalize_domain, Box

        # (lo, hi) tuple should become an Interval in a Box
        domain = normalize_domain((0, 1), default_var='x')
        assert isinstance(domain, Box)
        assert domain['x'].lo == 0
        assert domain['x'].hi == 1

    def test_normalize_dict_to_box(self):
        from leanbound_v2.domain import normalize_domain, Box

        domain = normalize_domain({'x': (0, 1), 'y': (-1, 1)})
        assert isinstance(domain, Box)
        assert len(domain) == 2

    def test_normalize_box_passthrough(self):
        from leanbound_v2.domain import normalize_domain, Box

        box = Box({'x': (0, 1)})
        domain = normalize_domain(box)
        assert domain is box
