# LeanBound v2 SDK - Symbolic Simplification
# Copyright (c) 2024 LeanBound Contributors. All rights reserved.

"""
Symbolic simplification for LeanBound expressions.

This module provides algebraic simplification to reduce the dependency problem
in interval arithmetic. When the same subexpression appears multiple times
(e.g., in A - A), naive interval arithmetic treats each occurrence independently,
causing over-approximation.

By simplifying expressions before evaluation, we can:
1. Cancel identical subexpressions (x - x = 0)
2. Combine like terms (2*x + 3*x = 5*x)
3. Expand and collect to expose cancellations

Example:
    >>> x = var('x')
    >>> expr = (x * 100 + 5) - (x * 100)  # Should be 5
    >>> simplified = simplify(expr)
    >>> # simplified is now const(5)
"""

from __future__ import annotations
from fractions import Fraction
from typing import Dict, Tuple, FrozenSet
from dataclasses import dataclass

from .expr import (
    Expr, Variable, Const, Add, Sub, Mul, Div, Pow, Neg,
    Sin, Cos, Exp, Log, Sqrt, Tan, Atan, Inv, Sinh, Cosh, Tanh,
    Arsinh, Atanh, Sinc, Erf,
    var, const,
)


def simplify(expr: Expr) -> Expr:
    """
    Simplify an expression algebraically.

    This applies multiple simplification strategies:
    1. Constant folding (2 + 3 -> 5)
    2. Identity removal (x + 0 -> x, x * 1 -> x)
    3. Zero propagation (x * 0 -> 0)
    4. Negation simplification (--x -> x)
    5. Like term collection in polynomial form
    6. Subexpression cancellation

    Args:
        expr: Expression to simplify

    Returns:
        Simplified expression (mathematically equivalent)
    """
    # Convert to polynomial form, simplify, convert back
    poly = to_polynomial(expr)
    if poly is not None:
        return from_polynomial(poly)

    # Fall back to recursive simplification for non-polynomial expressions
    return _simplify_recursive(expr)


def _simplify_recursive(expr: Expr) -> Expr:
    """Recursively simplify an expression."""
    if isinstance(expr, (Variable, Const)):
        return expr

    if isinstance(expr, Neg):
        inner = _simplify_recursive(expr.e)
        # --x -> x
        if isinstance(inner, Neg):
            return inner.e
        # -const -> const
        if isinstance(inner, Const):
            return const(-inner.value)
        return Neg(inner)

    if isinstance(expr, Add):
        e1 = _simplify_recursive(expr.e1)
        e2 = _simplify_recursive(expr.e2)
        # const + const
        if isinstance(e1, Const) and isinstance(e2, Const):
            return const(e1.value + e2.value)
        # x + 0 -> x
        if isinstance(e2, Const) and e2.value == 0:
            return e1
        # 0 + x -> x
        if isinstance(e1, Const) and e1.value == 0:
            return e2
        # x + (-y) -> x - y (for cleaner output)
        if isinstance(e2, Neg):
            return Sub(e1, e2.e)
        return Add(e1, e2)

    if isinstance(expr, Sub):
        e1 = _simplify_recursive(expr.e1)
        e2 = _simplify_recursive(expr.e2)
        # const - const
        if isinstance(e1, Const) and isinstance(e2, Const):
            return const(e1.value - e2.value)
        # x - 0 -> x
        if isinstance(e2, Const) and e2.value == 0:
            return e1
        # 0 - x -> -x
        if isinstance(e1, Const) and e1.value == 0:
            return Neg(e2)
        # x - x -> 0 (KEY: This catches the dependency problem!)
        if _expr_equal(e1, e2):
            return const(0)
        return Sub(e1, e2)

    if isinstance(expr, Mul):
        e1 = _simplify_recursive(expr.e1)
        e2 = _simplify_recursive(expr.e2)
        # const * const
        if isinstance(e1, Const) and isinstance(e2, Const):
            return const(e1.value * e2.value)
        # x * 0 -> 0
        if isinstance(e2, Const) and e2.value == 0:
            return const(0)
        if isinstance(e1, Const) and e1.value == 0:
            return const(0)
        # x * 1 -> x
        if isinstance(e2, Const) and e2.value == 1:
            return e1
        if isinstance(e1, Const) and e1.value == 1:
            return e2
        # (-x) * (-y) -> x * y
        if isinstance(e1, Neg) and isinstance(e2, Neg):
            return Mul(e1.e, e2.e)
        return Mul(e1, e2)

    if isinstance(expr, Div):
        e1 = _simplify_recursive(expr.e1)
        e2 = _simplify_recursive(expr.e2)
        # const / const
        if isinstance(e1, Const) and isinstance(e2, Const) and e2.value != 0:
            return const(e1.value / e2.value)
        # 0 / x -> 0
        if isinstance(e1, Const) and e1.value == 0:
            return const(0)
        # x / 1 -> x
        if isinstance(e2, Const) and e2.value == 1:
            return e1
        # x / x -> 1 (when x != 0, which we assume)
        if _expr_equal(e1, e2):
            return const(1)
        return Div(e1, e2)

    if isinstance(expr, Pow):
        base = _simplify_recursive(expr.base)
        n = expr.n
        # x^0 -> 1
        if n == 0:
            return const(1)
        # x^1 -> x
        if n == 1:
            return base
        # const^n -> const
        if isinstance(base, Const):
            return const(base.value ** n)
        return Pow(base, n)

    # Transcendental functions - just simplify the argument
    if isinstance(expr, (Sin, Cos, Exp, Log, Sqrt, Tan, Atan, Inv,
                         Sinh, Cosh, Tanh, Arsinh, Atanh, Sinc, Erf)):
        inner = _simplify_recursive(expr.e)
        return type(expr)(inner)

    return expr


def _expr_equal(e1: Expr, e2: Expr) -> bool:
    """Check if two expressions are structurally identical."""
    if type(e1) != type(e2):
        return False

    if isinstance(e1, Variable):
        return e1.name == e2.name

    if isinstance(e1, Const):
        return e1.value == e2.value

    if isinstance(e1, (Neg, Sin, Cos, Exp, Log, Sqrt, Tan, Atan, Inv,
                       Sinh, Cosh, Tanh, Arsinh, Atanh, Sinc, Erf)):
        return _expr_equal(e1.e, e2.e)

    if isinstance(e1, (Add, Sub, Mul, Div)):
        return _expr_equal(e1.e1, e2.e1) and _expr_equal(e1.e2, e2.e2)

    if isinstance(e1, Pow):
        return _expr_equal(e1.base, e2.base) and e1.n == e2.n

    return False


# Polynomial representation for better simplification
# A polynomial is represented as a dict mapping monomials to coefficients
# A monomial is a frozenset of (var_name, power) tuples

Monomial = FrozenSet[Tuple[str, int]]
Polynomial = Dict[Monomial, Fraction]


def to_polynomial(expr: Expr) -> Polynomial | None:
    """
    Convert expression to polynomial form if possible.

    Returns None for non-polynomial expressions (those with transcendentals).
    """
    if isinstance(expr, Const):
        # Constant: empty monomial with coefficient
        return {frozenset(): expr.value}

    if isinstance(expr, Variable):
        # Variable: monomial x^1 with coefficient 1
        return {frozenset({(expr.name, 1)}): Fraction(1)}

    if isinstance(expr, Neg):
        inner = to_polynomial(expr.e)
        if inner is None:
            return None
        return {m: -c for m, c in inner.items()}

    if isinstance(expr, Add):
        p1 = to_polynomial(expr.e1)
        p2 = to_polynomial(expr.e2)
        if p1 is None or p2 is None:
            return None
        return _add_poly(p1, p2)

    if isinstance(expr, Sub):
        p1 = to_polynomial(expr.e1)
        p2 = to_polynomial(expr.e2)
        if p1 is None or p2 is None:
            return None
        return _add_poly(p1, {m: -c for m, c in p2.items()})

    if isinstance(expr, Mul):
        p1 = to_polynomial(expr.e1)
        p2 = to_polynomial(expr.e2)
        if p1 is None or p2 is None:
            return None
        return _mul_poly(p1, p2)

    if isinstance(expr, Pow):
        base = to_polynomial(expr.base)
        if base is None:
            return None
        result = {frozenset(): Fraction(1)}  # Start with 1
        for _ in range(expr.n):
            result = _mul_poly(result, base)
        return result

    # Div and transcendentals are not polynomial
    return None


def _add_poly(p1: Polynomial, p2: Polynomial) -> Polynomial:
    """Add two polynomials."""
    result = dict(p1)
    for m, c in p2.items():
        result[m] = result.get(m, Fraction(0)) + c
    # Remove zero coefficients
    return {m: c for m, c in result.items() if c != 0}


def _mul_poly(p1: Polynomial, p2: Polynomial) -> Polynomial:
    """Multiply two polynomials."""
    result: Polynomial = {}
    for m1, c1 in p1.items():
        for m2, c2 in p2.items():
            # Multiply monomials by adding exponents
            new_mono = _mul_monomial(m1, m2)
            new_coef = c1 * c2
            result[new_mono] = result.get(new_mono, Fraction(0)) + new_coef
    # Remove zero coefficients
    return {m: c for m, c in result.items() if c != 0}


def _mul_monomial(m1: Monomial, m2: Monomial) -> Monomial:
    """Multiply two monomials by adding exponents."""
    powers: Dict[str, int] = {}
    for var, exp in m1:
        powers[var] = powers.get(var, 0) + exp
    for var, exp in m2:
        powers[var] = powers.get(var, 0) + exp
    # Remove zero exponents
    return frozenset((v, e) for v, e in powers.items() if e != 0)


def from_polynomial(poly: Polynomial) -> Expr:
    """Convert polynomial back to expression."""
    if not poly:
        return const(0)

    terms = []
    for mono, coef in sorted(poly.items(), key=lambda x: (-len(x[0]), sorted(x[0]))):
        if coef == 0:
            continue

        # Handle pure constant (empty monomial)
        if not mono:
            terms.append(const(coef))
            continue

        term = _mono_to_expr(mono)

        if coef == 1:
            terms.append(term)
        elif coef == -1:
            terms.append(Neg(term))
        else:
            terms.append(Mul(const(coef), term))

    if not terms:
        return const(0)

    result = terms[0]
    for t in terms[1:]:
        if isinstance(t, Neg):
            result = Sub(result, t.e)
        else:
            result = Add(result, t)

    return result


def _mono_to_expr(mono: Monomial) -> Expr:
    """Convert a monomial to an expression."""
    if not mono:
        return const(1)

    factors = []
    for var_name, exp in sorted(mono):
        v = Variable(var_name)
        if exp == 1:
            factors.append(v)
        else:
            factors.append(Pow(v, exp))

    result = factors[0]
    for f in factors[1:]:
        result = Mul(result, f)

    return result


def expand(expr: Expr) -> Expr:
    """
    Fully expand an expression (distribute multiplication over addition).

    This is useful when you want to expose all terms for cancellation.
    """
    poly = to_polynomial(expr)
    if poly is not None:
        return from_polynomial(poly)
    return _simplify_recursive(expr)


def collect(expr: Expr, var_name: str) -> Expr:
    """
    Collect terms with respect to a variable.

    E.g., x*a + x*b + c becomes x*(a+b) + c
    """
    # For now, just use polynomial simplification
    return simplify(expr)
