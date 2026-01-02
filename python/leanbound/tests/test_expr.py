# Tests for expr.py - Symbolic expressions
# TDD: Write tests first, then implement

import pytest
from fractions import Fraction


class TestVariable:
    """Tests for Variable creation and behavior."""

    def test_create_variable(self):
        from leanbound_v2.expr import var
        x = var('x')
        assert x.name == 'x'

    def test_variable_equality(self):
        from leanbound_v2.expr import var
        x1 = var('x')
        x2 = var('x')
        y = var('y')
        assert x1 == x2
        assert x1 != y

    def test_variable_hashable(self):
        from leanbound_v2.expr import var
        x = var('x')
        y = var('y')
        s = {x, y, var('x')}
        assert len(s) == 2

    def test_variable_free_vars(self):
        from leanbound_v2.expr import var
        x = var('x')
        assert x.free_vars() == frozenset({'x'})


class TestConstant:
    """Tests for Constant expressions."""

    def test_const_from_int(self):
        from leanbound_v2.expr import const
        c = const(42)
        assert c.value == Fraction(42)

    def test_const_from_float(self):
        from leanbound_v2.expr import const
        c = const(0.5)
        assert c.value == Fraction(1, 2)

    def test_const_from_fraction(self):
        from leanbound_v2.expr import const
        c = const(Fraction(1, 3))
        assert c.value == Fraction(1, 3)

    def test_const_free_vars_empty(self):
        from leanbound_v2.expr import const
        c = const(5)
        assert c.free_vars() == frozenset()


class TestOperatorOverloading:
    """Tests for natural math syntax."""

    def test_add_exprs(self):
        from leanbound_v2.expr import var
        x = var('x')
        y = var('y')
        expr = x + y
        assert expr.free_vars() == frozenset({'x', 'y'})

    def test_add_expr_and_int(self):
        from leanbound_v2.expr import var
        x = var('x')
        expr = x + 1
        assert expr.free_vars() == frozenset({'x'})

    def test_radd_int_and_expr(self):
        from leanbound_v2.expr import var
        x = var('x')
        expr = 1 + x
        assert expr.free_vars() == frozenset({'x'})

    def test_sub(self):
        from leanbound_v2.expr import var
        x = var('x')
        y = var('y')
        expr = x - y
        assert expr.free_vars() == frozenset({'x', 'y'})

    def test_mul(self):
        from leanbound_v2.expr import var
        x = var('x')
        expr = x * 2
        assert expr.free_vars() == frozenset({'x'})

    def test_div(self):
        from leanbound_v2.expr import var
        x = var('x')
        expr = x / 2
        assert expr.free_vars() == frozenset({'x'})

    def test_neg(self):
        from leanbound_v2.expr import var
        x = var('x')
        expr = -x
        assert expr.free_vars() == frozenset({'x'})

    def test_pow(self):
        from leanbound_v2.expr import var
        x = var('x')
        expr = x ** 2
        assert expr.free_vars() == frozenset({'x'})

    def test_complex_expression(self):
        from leanbound_v2.expr import var, sin, cos
        x = var('x')
        y = var('y')
        expr = x**2 + sin(y) * 2 - cos(x + y)
        assert expr.free_vars() == frozenset({'x', 'y'})


class TestUnaryFunctions:
    """Tests for sin, cos, exp, log, etc."""

    def test_sin(self):
        from leanbound_v2.expr import var, sin
        x = var('x')
        expr = sin(x)
        assert expr.free_vars() == frozenset({'x'})

    def test_cos(self):
        from leanbound_v2.expr import var, cos
        x = var('x')
        expr = cos(x)
        assert expr.free_vars() == frozenset({'x'})

    def test_exp(self):
        from leanbound_v2.expr import var, exp
        x = var('x')
        expr = exp(x)
        assert expr.free_vars() == frozenset({'x'})

    def test_log(self):
        from leanbound_v2.expr import var, log
        x = var('x')
        expr = log(x)
        assert expr.free_vars() == frozenset({'x'})

    def test_sqrt(self):
        from leanbound_v2.expr import var, sqrt
        x = var('x')
        expr = sqrt(x)
        assert expr.free_vars() == frozenset({'x'})

    def test_nested_functions(self):
        from leanbound_v2.expr import var, sin, exp
        x = var('x')
        expr = sin(exp(x))
        assert expr.free_vars() == frozenset({'x'})


class TestCompilation:
    """Tests for compiling symbolic expressions to De Bruijn indices."""

    def test_compile_variable(self):
        from leanbound_v2.expr import var
        x = var('x')
        kernel_expr = x.compile(['x'])
        assert kernel_expr == {'kind': 'var', 'idx': 0}

    def test_compile_variable_second_position(self):
        from leanbound_v2.expr import var
        y = var('y')
        kernel_expr = y.compile(['x', 'y'])
        assert kernel_expr == {'kind': 'var', 'idx': 1}

    def test_compile_constant(self):
        from leanbound_v2.expr import const
        c = const(Fraction(3, 4))
        kernel_expr = c.compile([])
        assert kernel_expr == {'kind': 'const', 'val': {'n': 3, 'd': 4}}

    def test_compile_add(self):
        from leanbound_v2.expr import var
        x = var('x')
        y = var('y')
        expr = x + y
        kernel_expr = expr.compile(['x', 'y'])
        assert kernel_expr == {
            'kind': 'add',
            'e1': {'kind': 'var', 'idx': 0},
            'e2': {'kind': 'var', 'idx': 1}
        }

    def test_compile_sin(self):
        from leanbound_v2.expr import var, sin
        x = var('x')
        expr = sin(x)
        kernel_expr = expr.compile(['x'])
        assert kernel_expr == {
            'kind': 'sin',
            'e': {'kind': 'var', 'idx': 0}
        }

    def test_compile_complex(self):
        from leanbound_v2.expr import var, sin
        x = var('x')
        expr = x**2 + sin(x)
        kernel_expr = expr.compile(['x'])
        # x**2 + sin(x) should compile to add(pow(var(0), 2), sin(var(0)))
        assert kernel_expr['kind'] == 'add'
        assert kernel_expr['e1']['kind'] == 'pow'
        assert kernel_expr['e2']['kind'] == 'sin'

    def test_compile_missing_variable_raises(self):
        from leanbound_v2.expr import var
        from leanbound_v2.exceptions import CompilationError
        x = var('x')
        with pytest.raises(CompilationError, match="Variable 'x' not in domain"):
            x.compile(['y', 'z'])

    def test_compile_sub_desugars(self):
        """Subtraction should desugar to add + neg."""
        from leanbound_v2.expr import var
        x = var('x')
        y = var('y')
        expr = x - y
        kernel_expr = expr.compile(['x', 'y'])
        # x - y becomes add(x, neg(y))
        assert kernel_expr['kind'] == 'add'
        assert kernel_expr['e2']['kind'] == 'neg'


class TestExprRepr:
    """Tests for string representation."""

    def test_variable_repr(self):
        from leanbound_v2.expr import var
        x = var('x')
        assert repr(x) == "var('x')"

    def test_const_repr(self):
        from leanbound_v2.expr import const
        c = const(5)
        assert repr(c) == "const(5)"

    def test_add_repr(self):
        from leanbound_v2.expr import var
        x = var('x')
        y = var('y')
        expr = x + y
        assert 'x' in repr(expr) and 'y' in repr(expr)


class TestHyperbolicFunctions:
    """Tests for hyperbolic functions: sinh, cosh, tanh, arsinh, atanh."""

    def test_sinh(self):
        from leanbound_v2.expr import var, sinh
        x = var('x')
        expr = sinh(x)
        assert expr.free_vars() == frozenset({'x'})

    def test_cosh(self):
        from leanbound_v2.expr import var, cosh
        x = var('x')
        expr = cosh(x)
        assert expr.free_vars() == frozenset({'x'})

    def test_tanh(self):
        from leanbound_v2.expr import var, tanh
        x = var('x')
        expr = tanh(x)
        assert expr.free_vars() == frozenset({'x'})

    def test_arsinh(self):
        from leanbound_v2.expr import var, arsinh
        x = var('x')
        expr = arsinh(x)
        assert expr.free_vars() == frozenset({'x'})

    def test_atanh(self):
        from leanbound_v2.expr import var, atanh
        x = var('x')
        expr = atanh(x)
        assert expr.free_vars() == frozenset({'x'})

    def test_sinh_compile(self):
        """sinh compiles to (exp(x) - exp(-x)) / 2."""
        from leanbound_v2.expr import var, sinh
        x = var('x')
        expr = sinh(x)
        kernel_expr = expr.compile(['x'])
        # Should be a derived expression, check it's valid JSON
        assert kernel_expr['kind'] == 'div' or kernel_expr['kind'] == 'mul'

    def test_cosh_compile(self):
        """cosh compiles to (exp(x) + exp(-x)) / 2."""
        from leanbound_v2.expr import var, cosh
        x = var('x')
        expr = cosh(x)
        kernel_expr = expr.compile(['x'])
        assert kernel_expr['kind'] == 'div' or kernel_expr['kind'] == 'mul'

    def test_tanh_compile(self):
        """tanh compiles to sinh(x) / cosh(x)."""
        from leanbound_v2.expr import var, tanh
        x = var('x')
        expr = tanh(x)
        kernel_expr = expr.compile(['x'])
        assert kernel_expr['kind'] == 'div'

    def test_arsinh_compile(self):
        """arsinh is a primitive in the kernel."""
        from leanbound_v2.expr import var, arsinh
        x = var('x')
        expr = arsinh(x)
        kernel_expr = expr.compile(['x'])
        assert kernel_expr['kind'] == 'arsinh'

    def test_atanh_compile(self):
        """atanh is a primitive in the kernel."""
        from leanbound_v2.expr import var, atanh
        x = var('x')
        expr = atanh(x)
        kernel_expr = expr.compile(['x'])
        assert kernel_expr['kind'] == 'atanh'


class TestInvFunction:
    """Tests for the explicit inverse (reciprocal) function."""

    def test_inv(self):
        from leanbound_v2.expr import var, inv
        x = var('x')
        expr = inv(x)
        assert expr.free_vars() == frozenset({'x'})

    def test_inv_compile(self):
        """inv is a primitive in the kernel."""
        from leanbound_v2.expr import var, inv
        x = var('x')
        expr = inv(x)
        kernel_expr = expr.compile(['x'])
        assert kernel_expr['kind'] == 'inv'

    def test_div_compiles_to_mul_inv(self):
        """Division x/y compiles to mul(x, inv(y)) for kernel."""
        from leanbound_v2.expr import var
        x = var('x')
        y = var('y')
        expr = x / y
        kernel_expr = expr.compile(['x', 'y'])
        # The kernel expects div, but could also be mul + inv
        assert kernel_expr['kind'] in ('div', 'mul')


class TestSpecialFunctions:
    """Tests for special mathematical functions: sinc, erf."""

    def test_sinc(self):
        """sinc function basic creation and free vars."""
        from leanbound_v2.expr import var, sinc
        x = var('x')
        expr = sinc(x)
        assert expr.free_vars() == frozenset({'x'})

    def test_sinc_compile(self):
        """sinc is a primitive in the kernel."""
        from leanbound_v2.expr import var, sinc
        x = var('x')
        expr = sinc(x)
        kernel_expr = expr.compile(['x'])
        assert kernel_expr['kind'] == 'sinc'
        assert kernel_expr['e']['kind'] == 'var'
        assert kernel_expr['e']['idx'] == 0

    def test_sinc_repr(self):
        from leanbound_v2.expr import var, sinc
        x = var('x')
        expr = sinc(x)
        assert repr(expr) == "sinc(var('x'))"

    def test_sinc_nested(self):
        """sinc of a complex expression."""
        from leanbound_v2.expr import var, sinc, sin
        x = var('x')
        expr = sinc(sin(x))
        assert expr.free_vars() == frozenset({'x'})
        kernel_expr = expr.compile(['x'])
        assert kernel_expr['kind'] == 'sinc'
        assert kernel_expr['e']['kind'] == 'sin'

    def test_erf(self):
        """erf function basic creation and free vars."""
        from leanbound_v2.expr import var, erf
        x = var('x')
        expr = erf(x)
        assert expr.free_vars() == frozenset({'x'})

    def test_erf_compile(self):
        """erf is a primitive in the kernel."""
        from leanbound_v2.expr import var, erf
        x = var('x')
        expr = erf(x)
        kernel_expr = expr.compile(['x'])
        assert kernel_expr['kind'] == 'erf'
        assert kernel_expr['e']['kind'] == 'var'
        assert kernel_expr['e']['idx'] == 0

    def test_erf_repr(self):
        from leanbound_v2.expr import var, erf
        x = var('x')
        expr = erf(x)
        assert repr(expr) == "erf(var('x'))"

    def test_erf_in_expression(self):
        """erf used in a larger expression (like Black-Scholes)."""
        from leanbound_v2.expr import var, erf, exp, sqrt, const
        x = var('x')
        # A simplified part of Black-Scholes CDF: (1 + erf(x/sqrt(2)))/2
        expr = (const(1) + erf(x / sqrt(const(2)))) / const(2)
        assert 'x' in expr.free_vars()

    def test_sinc_vs_sin_over_x(self):
        """sinc(x) is NOT the same as sin(x)/x in terms of AST."""
        from leanbound_v2.expr import var, sinc, sin
        x = var('x')
        sinc_expr = sinc(x)
        sin_over_x = sin(x) / x

        # They compile to different kernel representations
        sinc_kernel = sinc_expr.compile(['x'])
        sin_over_x_kernel = sin_over_x.compile(['x'])

        # sinc is a primitive, sin/x is a division
        assert sinc_kernel['kind'] == 'sinc'
        assert sin_over_x_kernel['kind'] == 'div'
