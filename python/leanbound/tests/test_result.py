# Tests for result.py - Results and Certificates
# TDD: Write tests first, then implement

import pytest
import json
import tempfile
from pathlib import Path
from fractions import Fraction


class TestBoundsResult:
    """Tests for BoundsResult."""

    def test_create_bounds_result(self):
        from leanbound_v2.result import BoundsResult
        from leanbound_v2.domain import Interval

        result = BoundsResult(
            min_bound=Interval(-0.25, -0.24),
            max_bound=Interval(0.99, 1.01),
            verified=True
        )
        assert result.verified
        assert result.min_bound.lo == Fraction(-0.25).limit_denominator(1000000)

    def test_bounds_result_repr(self):
        from leanbound_v2.result import BoundsResult
        from leanbound_v2.domain import Interval

        result = BoundsResult(
            min_bound=Interval(0, 1),
            max_bound=Interval(2, 3),
            verified=True
        )
        s = repr(result)
        assert 'BoundsResult' in s
        assert 'verified=True' in s


class TestRootsResult:
    """Tests for RootsResult."""

    def test_create_roots_result(self):
        from leanbound_v2.result import RootsResult, RootInterval
        from leanbound_v2.domain import Interval

        result = RootsResult(
            roots=[
                RootInterval(Interval(-1.1, -0.9), status='confirmed'),
                RootInterval(Interval(0.9, 1.1), status='confirmed'),
            ],
            iterations=50,
            verified=True
        )
        assert len(result.roots) == 2
        assert result.confirmed_roots() == result.roots

    def test_roots_filtering(self):
        from leanbound_v2.result import RootsResult, RootInterval
        from leanbound_v2.domain import Interval

        result = RootsResult(
            roots=[
                RootInterval(Interval(-1, 0), status='confirmed'),
                RootInterval(Interval(0, 1), status='possible'),
                RootInterval(Interval(1, 2), status='no_root'),
            ],
            iterations=50,
            verified=True
        )
        assert len(result.confirmed_roots()) == 1
        assert len(result.possible_roots()) == 1


class TestCertificate:
    """Tests for Certificate export and persistence."""

    def test_certificate_to_dict(self):
        from leanbound_v2.result import Certificate

        cert = Certificate(
            operation='find_bounds',
            expr_json={'kind': 'var', 'idx': 0},
            domain_json=[{'lo': {'n': 0, 'd': 1}, 'hi': {'n': 1, 'd': 1}}],
            result_json={'min': {'n': 0, 'd': 1}, 'max': {'n': 1, 'd': 1}},
            verified=True,
            lean_version='4.24.0',
            leanbound_version='0.2.0'
        )
        d = cert.to_dict()
        assert d['operation'] == 'find_bounds'
        assert d['verified'] is True
        assert 'lean_version' in d

    def test_certificate_save_json(self):
        from leanbound_v2.result import Certificate

        cert = Certificate(
            operation='find_bounds',
            expr_json={'kind': 'var', 'idx': 0},
            domain_json=[{'lo': {'n': 0, 'd': 1}, 'hi': {'n': 1, 'd': 1}}],
            result_json={'min': {'n': 0, 'd': 1}, 'max': {'n': 1, 'd': 1}},
            verified=True,
            lean_version='4.24.0',
            leanbound_version='0.2.0'
        )

        with tempfile.NamedTemporaryFile(suffix='.json', delete=False) as f:
            path = f.name

        try:
            cert.save(path)
            with open(path) as f:
                loaded = json.load(f)
            assert loaded['operation'] == 'find_bounds'
            assert loaded['verified'] is True
        finally:
            Path(path).unlink(missing_ok=True)

    def test_certificate_load_json(self):
        from leanbound_v2.result import Certificate

        data = {
            'operation': 'find_bounds',
            'expr': {'kind': 'var', 'idx': 0},
            'domain': [{'lo': {'n': 0, 'd': 1}, 'hi': {'n': 1, 'd': 1}}],
            'result': {'min': {'n': 0, 'd': 1}, 'max': {'n': 1, 'd': 1}},
            'verified': True,
            'lean_version': '4.24.0',
            'leanbound_version': '0.2.0'
        }

        with tempfile.NamedTemporaryFile(suffix='.json', delete=False, mode='w') as f:
            json.dump(data, f)
            path = f.name

        try:
            cert = Certificate.load(path)
            assert cert.operation == 'find_bounds'
            assert cert.verified is True
        finally:
            Path(path).unlink(missing_ok=True)

    def test_certificate_hash(self):
        from leanbound_v2.result import Certificate

        cert = Certificate(
            operation='find_bounds',
            expr_json={'kind': 'var', 'idx': 0},
            domain_json=[{'lo': {'n': 0, 'd': 1}, 'hi': {'n': 1, 'd': 1}}],
            result_json={'min': {'n': 0, 'd': 1}, 'max': {'n': 1, 'd': 1}},
            verified=True,
            lean_version='4.24.0',
            leanbound_version='0.2.0'
        )
        h = cert.hash()
        assert len(h) == 64  # SHA256 hex string
        assert all(c in '0123456789abcdef' for c in h)


class TestIntegralResult:
    """Tests for IntegralResult."""

    def test_create_integral_result(self):
        from leanbound_v2.result import IntegralResult
        from leanbound_v2.domain import Interval

        result = IntegralResult(
            bounds=Interval(Fraction(1, 3), Fraction(1, 2)),
            verified=True
        )
        assert result.verified
        assert result.bounds.lo == Fraction(1, 3)

    def test_integral_width(self):
        from leanbound_v2.result import IntegralResult
        from leanbound_v2.domain import Interval

        result = IntegralResult(
            bounds=Interval(0, 1),
            verified=True
        )
        assert result.error_bound() == 1


class TestCertificateToLeanTactic:
    """Tests for Certificate.to_lean_tactic() - Lean code generation."""

    def test_to_lean_tactic_find_bounds(self):
        """Test Lean code generation for find_bounds operation."""
        from leanbound_v2.result import Certificate

        cert = Certificate(
            operation='find_bounds',
            expr_json={'kind': 'pow', 'base': {'kind': 'var', 'idx': 0}, 'exp': 2},
            domain_json=[{'lo': {'n': 0, 'd': 1}, 'hi': {'n': 1, 'd': 1}}],
            result_json={
                'min': {'lo': {'n': 0, 'd': 1}, 'hi': {'n': 1, 'd': 100}},
                'max': {'lo': {'n': 99, 'd': 100}, 'hi': {'n': 1, 'd': 1}}
            },
            verified=True,
            lean_version='4.24.0',
            leanbound_version='0.2.0',
            metadata={'taylor_depth': 10}
        )

        lean_code = cert.to_lean_tactic()

        # Check structure
        assert '-- Certificate hash:' in lean_code
        assert '-- Generated from: find_bounds' in lean_code
        assert 'theorem bounds_check' in lean_code
        assert 'interval_bound' in lean_code

    def test_to_lean_tactic_expr_conversion(self):
        """Test expression-to-Lean conversion."""
        from leanbound_v2.result import Certificate

        cert = Certificate(
            operation='find_bounds',
            expr_json={
                'kind': 'add',
                'e1': {'kind': 'sin', 'e': {'kind': 'var', 'idx': 0}},
                'e2': {'kind': 'const', 'val': {'n': 1, 'd': 2}}
            },
            domain_json=[{'lo': {'n': 0, 'd': 1}, 'hi': {'n': 314159, 'd': 100000}}],
            result_json={
                'min': {'lo': {'n': 0, 'd': 1}, 'hi': {'n': 1, 'd': 10}},
                'max': {'lo': {'n': 14, 'd': 10}, 'hi': {'n': 15, 'd': 10}}
            },
            verified=True,
            lean_version='4.24.0',
            leanbound_version='0.2.0'
        )

        lean_code = cert.to_lean_tactic()

        # Should include sin and const conversion
        assert 'Real.sin' in lean_code
        assert '(1/2)' in lean_code

    def test_to_lean_tactic_multivariate_domain(self):
        """Test Lean code generation for multivariate domains."""
        from leanbound_v2.result import Certificate

        cert = Certificate(
            operation='find_bounds',
            expr_json={'kind': 'add',
                      'e1': {'kind': 'var', 'idx': 0},
                      'e2': {'kind': 'var', 'idx': 1}},
            domain_json=[
                {'lo': {'n': 0, 'd': 1}, 'hi': {'n': 1, 'd': 1}},
                {'lo': {'n': 0, 'd': 1}, 'hi': {'n': 2, 'd': 1}}
            ],
            result_json={
                'min': {'lo': {'n': 0, 'd': 1}, 'hi': {'n': 0, 'd': 1}},
                'max': {'lo': {'n': 3, 'd': 1}, 'hi': {'n': 3, 'd': 1}}
            },
            verified=True,
            lean_version='4.24.0',
            leanbound_version='0.2.0'
        )

        lean_code = cert.to_lean_tactic()

        # Should show multivariate domain format
        assert 'x0' in lean_code
        assert 'x1' in lean_code

    def test_to_lean_tactic_verify_bound(self):
        """Test Lean code generation for verify_bound operation."""
        from leanbound_v2.result import Certificate

        cert = Certificate(
            operation='verify_bound',
            expr_json={'kind': 'pow', 'base': {'kind': 'var', 'idx': 0}, 'exp': 2},
            domain_json=[{'lo': {'n': 0, 'd': 1}, 'hi': {'n': 1, 'd': 1}}],
            result_json={'bound_type': 'upper', 'bound_value': 1.5},
            verified=True,
            lean_version='4.24.0',
            leanbound_version='0.2.0',
            metadata={'taylor_depth': 10}
        )

        lean_code = cert.to_lean_tactic()

        assert '-- Generated from: verify_bound' in lean_code
        assert 'upper_bound_check' in lean_code or 'bound_check' in lean_code
        assert 'interval_bound' in lean_code

    def test_to_lean_tactic_find_roots(self):
        """Test Lean code generation for find_roots operation."""
        from leanbound_v2.result import Certificate

        cert = Certificate(
            operation='find_roots',
            expr_json={'kind': 'add',
                      'e1': {'kind': 'pow', 'base': {'kind': 'var', 'idx': 0}, 'exp': 2},
                      'e2': {'kind': 'neg', 'e': {'kind': 'const', 'val': {'n': 1, 'd': 1}}}},
            domain_json=[{'lo': {'n': -2, 'd': 1}, 'hi': {'n': 2, 'd': 1}}],
            result_json={
                'roots': [
                    {'lo': {'n': -11, 'd': 10}, 'hi': {'n': -9, 'd': 10}, 'status': 'hasRoot'},
                    {'lo': {'n': 9, 'd': 10}, 'hi': {'n': 11, 'd': 10}, 'status': 'hasRoot'}
                ]
            },
            verified=True,
            lean_version='4.24.0',
            leanbound_version='0.2.0'
        )

        lean_code = cert.to_lean_tactic()

        assert '-- Generated from: find_roots' in lean_code
        assert 'Root' in lean_code
        assert 'IVT' in lean_code  # Intermediate Value Theorem mentioned

    def test_to_lean_tactic_integrate(self):
        """Test Lean code generation for integrate operation."""
        from leanbound_v2.result import Certificate

        cert = Certificate(
            operation='integrate',
            expr_json={'kind': 'pow', 'base': {'kind': 'var', 'idx': 0}, 'exp': 2},
            domain_json=[{'lo': {'n': 0, 'd': 1}, 'hi': {'n': 1, 'd': 1}}],
            result_json={'lo': {'n': 32, 'd': 100}, 'hi': {'n': 34, 'd': 100}},
            verified=True,
            lean_version='4.24.0',
            leanbound_version='0.2.0',
            metadata={'taylor_depth': 10}
        )

        lean_code = cert.to_lean_tactic()

        assert '-- Generated from: integrate' in lean_code
        assert 'Integral' in lean_code or 'integral' in lean_code

    def test_to_lean_tactic_unknown_operation(self):
        """Test Lean code generation for unknown operations."""
        from leanbound_v2.result import Certificate

        cert = Certificate(
            operation='unknown_op',
            expr_json={'kind': 'var', 'idx': 0},
            domain_json=[{'lo': {'n': 0, 'd': 1}, 'hi': {'n': 1, 'd': 1}}],
            result_json={'some': 'data'},
            verified=True,
            lean_version='4.24.0',
            leanbound_version='0.2.0'
        )

        lean_code = cert.to_lean_tactic()

        assert '-- Unknown operation: unknown_op' in lean_code
        assert '-- Raw result:' in lean_code

    def test_expr_to_lean_all_kinds(self):
        """Test _expr_to_lean handles all expression kinds."""
        from leanbound_v2.result import Certificate

        # Create certificate to access _expr_to_lean
        cert = Certificate(
            operation='test',
            expr_json={},
            domain_json=[],
            result_json={},
            verified=True,
            lean_version='4.24.0',
            leanbound_version='0.2.0'
        )

        # Test various expression kinds
        assert cert._expr_to_lean({'kind': 'const', 'val': {'n': 3, 'd': 1}}) == '3'
        assert cert._expr_to_lean({'kind': 'const', 'val': {'n': 1, 'd': 2}}) == '(1/2)'
        assert cert._expr_to_lean({'kind': 'var', 'idx': 0}) == 'x'
        assert cert._expr_to_lean({'kind': 'var', 'idx': 1}) == 'x1'

        # Binary ops
        assert '+ 1' in cert._expr_to_lean({'kind': 'add', 'e1': {'kind': 'var', 'idx': 0}, 'e2': {'kind': 'const', 'val': {'n': 1, 'd': 1}}})
        assert '* 2' in cert._expr_to_lean({'kind': 'mul', 'e1': {'kind': 'var', 'idx': 0}, 'e2': {'kind': 'const', 'val': {'n': 2, 'd': 1}}})
        assert '/ 3' in cert._expr_to_lean({'kind': 'div', 'e1': {'kind': 'var', 'idx': 0}, 'e2': {'kind': 'const', 'val': {'n': 3, 'd': 1}}})

        # Unary ops
        assert cert._expr_to_lean({'kind': 'neg', 'e': {'kind': 'var', 'idx': 0}}) == '(-x)'
        assert cert._expr_to_lean({'kind': 'pow', 'base': {'kind': 'var', 'idx': 0}, 'exp': 3}) == '(x^3)'

        # Functions
        assert cert._expr_to_lean({'kind': 'sin', 'e': {'kind': 'var', 'idx': 0}}) == 'Real.sin x'
        assert cert._expr_to_lean({'kind': 'cos', 'e': {'kind': 'var', 'idx': 0}}) == 'Real.cos x'
        assert cert._expr_to_lean({'kind': 'exp', 'e': {'kind': 'var', 'idx': 0}}) == 'Real.exp x'
        assert cert._expr_to_lean({'kind': 'log', 'e': {'kind': 'var', 'idx': 0}}) == 'Real.log x'
        assert cert._expr_to_lean({'kind': 'sqrt', 'e': {'kind': 'var', 'idx': 0}}) == 'Real.sqrt x'
        assert cert._expr_to_lean({'kind': 'tan', 'e': {'kind': 'var', 'idx': 0}}) == 'Real.tan x'
        assert cert._expr_to_lean({'kind': 'atan', 'e': {'kind': 'var', 'idx': 0}}) == 'Real.atan x'
        assert cert._expr_to_lean({'kind': 'inv', 'e': {'kind': 'var', 'idx': 0}}) == 'Real.inv x'
        assert cert._expr_to_lean({'kind': 'arsinh', 'e': {'kind': 'var', 'idx': 0}}) == 'Real.arsinh x'
        assert cert._expr_to_lean({'kind': 'atanh', 'e': {'kind': 'var', 'idx': 0}}) == 'Real.atanh x'
        assert cert._expr_to_lean({'kind': 'sinc', 'e': {'kind': 'var', 'idx': 0}}) == 'Real.sinc x'
        assert cert._expr_to_lean({'kind': 'erf', 'e': {'kind': 'var', 'idx': 0}}) == 'Real.erf x'

        # Unknown
        assert '<unknown?>' in cert._expr_to_lean({'kind': 'unknown'})


class TestUniqueRootResult:
    """Tests for UniqueRootResult."""

    def test_create_unique_root_result(self):
        from leanbound_v2.result import UniqueRootResult
        from leanbound_v2.domain import Interval

        result = UniqueRootResult(
            unique=True,
            interval=Interval(Fraction(49, 100), Fraction(51, 100)),
            reason='newton_contraction'
        )
        assert result.unique is True
        assert result.reason == 'newton_contraction'
        assert 0.49 <= result.root_value <= 0.51

    def test_unique_root_result_repr_unique(self):
        from leanbound_v2.result import UniqueRootResult
        from leanbound_v2.domain import Interval

        result = UniqueRootResult(
            unique=True,
            interval=Interval(0.5, 0.5),
            reason='newton_contraction'
        )
        s = repr(result)
        assert 'UNIQUE' in s

    def test_unique_root_result_repr_not_unique(self):
        from leanbound_v2.result import UniqueRootResult
        from leanbound_v2.domain import Interval

        result = UniqueRootResult(
            unique=False,
            interval=Interval(0, 1),
            reason='no_contraction'
        )
        s = repr(result)
        assert 'not proven unique' in s
        assert 'no_contraction' in s
