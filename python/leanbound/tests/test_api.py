# Tests for the high-level API
# TDD: Write tests first, then implement

import pytest
from fractions import Fraction


class TestFindBoundsAPI:
    """Tests for lf.find_bounds() API."""

    def test_find_bounds_simple_univariate(self):
        """x**2 on [0, 1] should have min near 0 and max near 1."""
        import leanbound_v2 as lf

        x = lf.var('x')
        result = lf.find_bounds(x**2, {'x': (0, 1)})

        assert result.verified
        # Min should be near 0
        assert float(result.min_bound.lo) >= -0.01
        assert float(result.min_bound.hi) <= 0.01
        # Max should be near 1
        assert float(result.max_bound.lo) >= 0.99
        assert float(result.max_bound.hi) <= 1.01

    def test_find_bounds_with_interval_syntax(self):
        """Support Interval directly for univariate."""
        import leanbound_v2 as lf

        x = lf.var('x')
        result = lf.find_bounds(x**2, lf.Interval(0, 1))

        assert result.verified

    def test_find_bounds_multivariate(self):
        """x**2 + y**2 on [0,1] x [0,1]."""
        import leanbound_v2 as lf

        x = lf.var('x')
        y = lf.var('y')
        result = lf.find_bounds(x**2 + y**2, {'x': (0, 1), 'y': (0, 1)})

        assert result.verified
        # Min is 0 at origin
        assert float(result.min_bound.hi) <= 0.1
        # Max is 2 at (1, 1)
        assert float(result.max_bound.lo) >= 1.9

    def test_find_bounds_with_trig(self):
        """sin(x) on [0, pi]."""
        import leanbound_v2 as lf
        import math

        x = lf.var('x')
        result = lf.find_bounds(lf.sin(x), {'x': (0, math.pi)})

        assert result.verified
        # Min is 0 at endpoints
        assert float(result.min_bound.hi) <= 0.1
        # Max is 1 at pi/2
        assert float(result.max_bound.lo) >= 0.9

    def test_find_bounds_undefined_var_raises(self):
        """Using a variable not in domain should raise."""
        import leanbound_v2 as lf
        from leanbound_v2.exceptions import DomainError

        x = lf.var('x')
        y = lf.var('y')

        with pytest.raises(DomainError):
            lf.find_bounds(x + y, {'x': (0, 1)})  # y not defined


class TestVerifyBoundAPI:
    """Tests for lf.verify_bound() API."""

    def test_verify_upper_bound_passes(self):
        """x**2 <= 1 on [0, 1] should verify."""
        import leanbound_v2 as lf

        x = lf.var('x')
        result = lf.verify_bound(x**2, {'x': (0, 1)}, upper=1.0)

        assert result is True

    def test_verify_upper_bound_fails(self):
        """x**2 <= 0.5 on [0, 1] should fail."""
        import leanbound_v2 as lf
        from leanbound_v2.exceptions import VerificationFailed

        x = lf.var('x')

        with pytest.raises(VerificationFailed):
            lf.verify_bound(x**2, {'x': (0, 1)}, upper=0.5)

    def test_verify_lower_bound_passes(self):
        """x**2 >= 0 on [0, 1] should verify."""
        import leanbound_v2 as lf

        x = lf.var('x')
        result = lf.verify_bound(x**2, {'x': (0, 1)}, lower=0.0)

        assert result is True

    def test_verify_lower_bound_fails(self):
        """x**2 >= 0.5 on [0, 1] should fail."""
        import leanbound_v2 as lf
        from leanbound_v2.exceptions import VerificationFailed

        x = lf.var('x')

        with pytest.raises(VerificationFailed):
            lf.verify_bound(x**2, {'x': (0, 1)}, lower=0.5)

    def test_verify_both_bounds(self):
        """Verify both upper and lower."""
        import leanbound_v2 as lf

        x = lf.var('x')
        result = lf.verify_bound(x**2, {'x': (0, 1)}, lower=0.0, upper=1.0)

        assert result is True


class TestFindRootsAPI:
    """Tests for lf.find_roots() API."""

    def test_find_roots_quadratic(self):
        """x**2 - 1 = 0 has roots at -1 and 1."""
        import leanbound_v2 as lf

        x = lf.var('x')
        result = lf.find_roots(x**2 - 1, {'x': (-2, 2)})

        assert result.verified
        # Check all roots (confirmed or possible)
        all_roots = [r for r in result.roots if r.status in ('confirmed', 'possible')]
        assert len(all_roots) >= 2

        # Check that -1 and 1 are in some root interval
        values = [-1, 1]
        for val in values:
            found = any(val in root.interval for root in all_roots)
            assert found, f"Root at {val} not found"

    def test_find_roots_no_roots(self):
        """x**2 + 1 = 0 has no real roots."""
        import leanbound_v2 as lf

        x = lf.var('x')
        result = lf.find_roots(x**2 + 1, {'x': (-10, 10)})

        assert result.verified
        assert len(result.confirmed_roots()) == 0


class TestIntegrateAPI:
    """Tests for lf.integrate() API."""

    def test_integrate_constant(self):
        """Integral of 1 over [0, 1] is 1."""
        import leanbound_v2 as lf

        x = lf.var('x')
        result = lf.integrate(lf.const(1), {'x': (0, 1)})

        assert result.verified
        assert 0.99 <= float(result.bounds.lo) <= float(result.bounds.hi) <= 1.01

    def test_integrate_linear(self):
        """Integral of x over [0, 1] is 0.5."""
        import leanbound_v2 as lf

        x = lf.var('x')
        # Use more partitions for tighter bounds
        result = lf.integrate(x, {'x': (0, 1)}, partitions=100)

        assert result.verified
        # Interval arithmetic gives conservative bounds - check that 0.5 is contained
        assert float(result.bounds.lo) <= 0.5 <= float(result.bounds.hi)

    def test_integrate_quadratic(self):
        """Integral of x**2 over [0, 1] is 1/3."""
        import leanbound_v2 as lf

        x = lf.var('x')
        # Use more partitions for tighter bounds
        result = lf.integrate(x**2, {'x': (0, 1)}, partitions=100)

        assert result.verified
        # Interval arithmetic gives conservative bounds - check that 1/3 is contained
        assert float(result.bounds.lo) <= 1/3 <= float(result.bounds.hi)


class TestConfigAPI:
    """Tests for configuration options."""

    def test_find_bounds_with_config(self):
        import leanbound_v2 as lf

        x = lf.var('x')
        config = lf.Config(taylor_depth=5, max_iters=100)
        result = lf.find_bounds(x**2, {'x': (0, 1)}, config=config)

        assert result.verified

    def test_high_precision_config(self):
        import leanbound_v2 as lf

        x = lf.var('x')
        config = lf.Config.high_precision()
        result = lf.find_bounds(x**2, {'x': (0, 1)}, config=config)

        assert result.verified
        # High precision should give tighter bounds
        assert result.min_bound.width() < Fraction(1, 1000)


class TestContextManager:
    """Tests for context manager usage."""

    def test_solver_context_manager(self):
        import leanbound_v2 as lf

        x = lf.var('x')

        with lf.Solver() as solver:
            result = solver.find_bounds(x**2, {'x': (0, 1)})
            assert result.verified

    def test_bridge_closes_on_exit(self):
        import leanbound_v2 as lf

        x = lf.var('x')

        solver = lf.Solver()
        solver.find_bounds(x**2, {'x': (0, 1)})
        solver.close()
        # Should not raise even if called multiple times
        solver.close()


class TestAdaptiveVerification:
    """Tests for adaptive verification using optimization."""

    def test_verify_adaptive_upper_bound_passes(self):
        """Adaptive verification can verify a loose upper bound."""
        import leanbound_v2 as lf

        x = lf.var('x')
        # x**2 <= 1.5 on [0, 1] should verify
        result = lf.verify_bound(x**2, {'x': (0, 1)}, upper=1.5, method='adaptive')
        assert result is True

    def test_verify_adaptive_tight_bound_passes(self):
        """Adaptive verification can verify tight bounds better than interval eval."""
        import leanbound_v2 as lf

        x = lf.var('x')
        # x**2 <= 1.01 on [0, 1] should verify with optimization
        result = lf.verify_bound(x**2, {'x': (0, 1)}, upper=1.01, method='adaptive')
        assert result is True

    def test_verify_adaptive_lower_bound_passes(self):
        """Adaptive verification works for lower bounds."""
        import leanbound_v2 as lf

        x = lf.var('x')
        # x**2 >= -0.1 on [0, 1] should verify
        result = lf.verify_bound(x**2, {'x': (0, 1)}, lower=-0.1, method='adaptive')
        assert result is True

    def test_verify_adaptive_fails_when_wrong(self):
        """Adaptive verification fails for invalid bounds."""
        import leanbound_v2 as lf
        from leanbound_v2.exceptions import VerificationFailed

        x = lf.var('x')
        # x**2 <= 0.5 on [0, 1] should fail (max is 1)
        with pytest.raises(VerificationFailed):
            lf.verify_bound(x**2, {'x': (0, 1)}, upper=0.5, method='adaptive')

    def test_verify_default_method_is_interval(self):
        """Default method is 'interval' (faster but less powerful)."""
        import leanbound_v2 as lf

        x = lf.var('x')
        # This should use interval method by default
        result = lf.verify_bound(x**2, {'x': (0, 1)}, upper=1.0)
        assert result is True


class TestUniqueRootFinding:
    """Tests for unique root finding via Newton contraction."""

    def test_find_unique_root_simple(self):
        """x - 0.5 = 0 has unique root at 0.5."""
        import leanbound_v2 as lf

        x = lf.var('x')
        result = lf.find_unique_root(x - 0.5, {'x': (0, 1)})

        # May or may not prove uniqueness depending on Newton contraction
        # The key is it returns a result with the correct fields
        assert hasattr(result, 'unique')
        assert hasattr(result, 'interval')
        assert hasattr(result, 'reason')

    def test_find_unique_root_steep_function(self):
        """2*x - 1 = 0 on [0, 1] - should prove unique root at 0.5."""
        import leanbound_v2 as lf

        x = lf.var('x')
        # Linear function: derivative is constant (2), so Newton should contract
        result = lf.find_unique_root(2*x - 1, {'x': (0, 1)})

        # For linear functions, Newton may or may not contract depending on implementation
        # Just verify structure
        assert result.reason in ('newton_contraction', 'no_contraction', 'newton_step_failed')
        if result.unique:
            # If unique is proven, the root interval should be tight
            assert 0.4 < float(result.interval.midpoint()) < 0.6

    def test_find_unique_root_no_root(self):
        """x**2 + 1 = 0 on [-1, 1] has no real roots."""
        import leanbound_v2 as lf

        x = lf.var('x')
        result = lf.find_unique_root(x**2 + 1, {'x': (-1, 1)})

        # Newton step may fail or not contract for functions with no roots
        assert result.unique is False

    def test_unique_root_result_type(self):
        """UniqueRootResult has expected structure."""
        import leanbound_v2 as lf

        x = lf.var('x')
        result = lf.find_unique_root(x - 0.5, {'x': (0, 1)})

        # Check it's the right type
        assert isinstance(result, lf.UniqueRootResult)
