# LeanBound v2 SDK - Symbolic Expressions
# Copyright (c) 2024 LeanBound Contributors. All rights reserved.

"""
Symbolic expression AST for LeanBound v2.

This module provides a user-friendly symbolic expression system with named variables.
Expressions are immutable and support natural Python math syntax.

Example:
    >>> x = var('x')
    >>> y = var('y')
    >>> expr = x**2 + sin(y)
    >>> expr.free_vars()
    frozenset({'x', 'y'})
"""

from __future__ import annotations
from abc import ABC, abstractmethod
import builtins
from dataclasses import dataclass
from fractions import Fraction
from typing import Union, Any, FrozenSet
import math

# Store reference to builtin abs before we shadow it
builtins_abs = builtins.abs

from .exceptions import CompilationError
from .rational import to_fraction as _to_nice_fraction


# Type for evaluation environment
EvalEnv = dict[str, Union[float, Fraction]]
EvalResult = Union[float, Fraction]


# Type alias for kernel expressions (De Bruijn indexed JSON)
KernelExpr = dict[str, Any]

# Type alias for things that can be converted to expressions
ExprLike = Union['Expr', int, float, Fraction]


class Expr(ABC):
    """
    Base class for symbolic expressions.

    Expressions are immutable and can be composed using Python operators.
    They track their free variables and can be compiled to kernel representation.
    """

    @abstractmethod
    def free_vars(self) -> FrozenSet[str]:
        """Return all variable names used in this expression."""
        ...

    @abstractmethod
    def compile(self, var_order: list[str]) -> KernelExpr:
        """
        Compile to De Bruijn representation given variable ordering.

        Args:
            var_order: List of variable names. Index in list = De Bruijn index.

        Returns:
            JSON-serializable dict for the Lean kernel.

        Raises:
            CompilationError: If a variable is not in var_order.
        """
        ...

    @abstractmethod
    def evaluate(self, env: EvalEnv) -> EvalResult:
        """
        Evaluate the expression concretely using Python math.

        Used for counterexample verification to filter false positives.
        When the solver reports a potential bug, we evaluate the expression
        at the reported point using standard Python arithmetic. If the
        concrete value doesn't violate the bound, it's a false positive
        caused by interval over-approximation.

        Args:
            env: Dictionary mapping variable names to concrete values.

        Returns:
            The concrete value (float for transcendentals, Fraction for polynomials).

        Raises:
            ValueError: If a required variable is not in env.
        """
        ...

    # Operator overloading for natural math syntax
    def __neg__(self) -> Expr:
        return Neg(self)

    def __add__(self, other: ExprLike) -> Expr:
        return Add(self, _to_expr(other))

    def __radd__(self, other: ExprLike) -> Expr:
        return Add(_to_expr(other), self)

    def __sub__(self, other: ExprLike) -> Expr:
        return Sub(self, _to_expr(other))

    def __rsub__(self, other: ExprLike) -> Expr:
        return Sub(_to_expr(other), self)

    def __mul__(self, other: ExprLike) -> Expr:
        return Mul(self, _to_expr(other))

    def __rmul__(self, other: ExprLike) -> Expr:
        return Mul(_to_expr(other), self)

    def __truediv__(self, other: ExprLike) -> Expr:
        return Div(self, _to_expr(other))

    def __rtruediv__(self, other: ExprLike) -> Expr:
        return Div(_to_expr(other), self)

    def __pow__(self, n: int) -> Expr:
        if not isinstance(n, int) or n < 0:
            raise ValueError("Only non-negative integer powers are supported")
        return Pow(self, n)


def _to_expr(x: ExprLike) -> Expr:
    """Convert a value to an Expr."""
    if isinstance(x, Expr):
        return x
    elif isinstance(x, (int, float, Fraction)):
        return Const(x)
    else:
        raise TypeError(f"Cannot convert {type(x).__name__} to Expr")


@dataclass(frozen=True)
class Variable(Expr):
    """A symbolic variable with a name."""
    name: str

    def free_vars(self) -> FrozenSet[str]:
        return frozenset({self.name})

    def compile(self, var_order: list[str]) -> KernelExpr:
        if self.name not in var_order:
            raise CompilationError(f"Variable '{self.name}' not in domain")
        idx = var_order.index(self.name)
        return {'kind': 'var', 'idx': idx}

    def evaluate(self, env: EvalEnv) -> EvalResult:
        if self.name not in env:
            raise ValueError(f"Variable '{self.name}' not in environment")
        return env[self.name]

    def __repr__(self) -> str:
        return f"var('{self.name}')"


@dataclass(frozen=True)
class Const(Expr):
    """A constant value (rational number)."""
    _value: Union[int, float, Fraction]

    @property
    def value(self) -> Fraction:
        """Get the value as an exact Fraction."""
        return _to_nice_fraction(self._value)

    def free_vars(self) -> FrozenSet[str]:
        return frozenset()

    def compile(self, var_order: list[str]) -> KernelExpr:
        v = self.value
        return {'kind': 'const', 'val': {'n': v.numerator, 'd': v.denominator}}

    def evaluate(self, env: EvalEnv) -> Fraction:
        return self.value

    def __repr__(self) -> str:
        v = self.value
        if v.denominator == 1:
            return f"const({v.numerator})"
        return f"const({v})"


# Binary operations

@dataclass(frozen=True)
class Add(Expr):
    """Addition: e1 + e2."""
    e1: Expr
    e2: Expr

    def free_vars(self) -> FrozenSet[str]:
        return self.e1.free_vars() | self.e2.free_vars()

    def compile(self, var_order: list[str]) -> KernelExpr:
        return {
            'kind': 'add',
            'e1': self.e1.compile(var_order),
            'e2': self.e2.compile(var_order)
        }

    def evaluate(self, env: EvalEnv) -> EvalResult:
        return self.e1.evaluate(env) + self.e2.evaluate(env)

    def __repr__(self) -> str:
        return f"({self.e1} + {self.e2})"


@dataclass(frozen=True)
class Sub(Expr):
    """Subtraction: e1 - e2. Desugars to e1 + neg(e2) on compilation."""
    e1: Expr
    e2: Expr

    def free_vars(self) -> FrozenSet[str]:
        return self.e1.free_vars() | self.e2.free_vars()

    def compile(self, var_order: list[str]) -> KernelExpr:
        # Desugar: e1 - e2 = e1 + neg(e2)
        return {
            'kind': 'add',
            'e1': self.e1.compile(var_order),
            'e2': {'kind': 'neg', 'e': self.e2.compile(var_order)}
        }

    def evaluate(self, env: EvalEnv) -> EvalResult:
        return self.e1.evaluate(env) - self.e2.evaluate(env)

    def __repr__(self) -> str:
        return f"({self.e1} - {self.e2})"


@dataclass(frozen=True)
class Mul(Expr):
    """Multiplication: e1 * e2."""
    e1: Expr
    e2: Expr

    def free_vars(self) -> FrozenSet[str]:
        return self.e1.free_vars() | self.e2.free_vars()

    def compile(self, var_order: list[str]) -> KernelExpr:
        return {
            'kind': 'mul',
            'e1': self.e1.compile(var_order),
            'e2': self.e2.compile(var_order)
        }

    def evaluate(self, env: EvalEnv) -> EvalResult:
        return self.e1.evaluate(env) * self.e2.evaluate(env)

    def __repr__(self) -> str:
        return f"({self.e1} * {self.e2})"


@dataclass(frozen=True)
class Div(Expr):
    """Division: e1 / e2."""
    e1: Expr
    e2: Expr

    def free_vars(self) -> FrozenSet[str]:
        return self.e1.free_vars() | self.e2.free_vars()

    def compile(self, var_order: list[str]) -> KernelExpr:
        return {
            'kind': 'div',
            'e1': self.e1.compile(var_order),
            'e2': self.e2.compile(var_order)
        }

    def evaluate(self, env: EvalEnv) -> EvalResult:
        v1 = self.e1.evaluate(env)
        v2 = self.e2.evaluate(env)
        # Use float division for consistency with transcendentals
        return float(v1) / float(v2)

    def __repr__(self) -> str:
        return f"({self.e1} / {self.e2})"


@dataclass(frozen=True)
class Pow(Expr):
    """Integer power: base ** n."""
    base: Expr
    n: int

    def free_vars(self) -> FrozenSet[str]:
        return self.base.free_vars()

    def compile(self, var_order: list[str]) -> KernelExpr:
        return {
            'kind': 'pow',
            'base': self.base.compile(var_order),
            'exp': self.n
        }

    def evaluate(self, env: EvalEnv) -> EvalResult:
        return self.base.evaluate(env) ** self.n

    def __repr__(self) -> str:
        return f"({self.base} ** {self.n})"


# Unary operations

@dataclass(frozen=True)
class Neg(Expr):
    """Negation: -e."""
    e: Expr

    def free_vars(self) -> FrozenSet[str]:
        return self.e.free_vars()

    def compile(self, var_order: list[str]) -> KernelExpr:
        return {'kind': 'neg', 'e': self.e.compile(var_order)}

    def evaluate(self, env: EvalEnv) -> EvalResult:
        return -self.e.evaluate(env)

    def __repr__(self) -> str:
        return f"(-{self.e})"


@dataclass(frozen=True)
class Sin(Expr):
    """Sine function."""
    e: Expr

    def free_vars(self) -> FrozenSet[str]:
        return self.e.free_vars()

    def compile(self, var_order: list[str]) -> KernelExpr:
        return {'kind': 'sin', 'e': self.e.compile(var_order)}

    def evaluate(self, env: EvalEnv) -> float:
        return math.sin(float(self.e.evaluate(env)))

    def __repr__(self) -> str:
        return f"sin({self.e})"


@dataclass(frozen=True)
class Cos(Expr):
    """Cosine function."""
    e: Expr

    def free_vars(self) -> FrozenSet[str]:
        return self.e.free_vars()

    def compile(self, var_order: list[str]) -> KernelExpr:
        return {'kind': 'cos', 'e': self.e.compile(var_order)}

    def evaluate(self, env: EvalEnv) -> float:
        return math.cos(float(self.e.evaluate(env)))

    def __repr__(self) -> str:
        return f"cos({self.e})"


@dataclass(frozen=True)
class Exp(Expr):
    """Exponential function."""
    e: Expr

    def free_vars(self) -> FrozenSet[str]:
        return self.e.free_vars()

    def compile(self, var_order: list[str]) -> KernelExpr:
        return {'kind': 'exp', 'e': self.e.compile(var_order)}

    def evaluate(self, env: EvalEnv) -> float:
        return math.exp(float(self.e.evaluate(env)))

    def __repr__(self) -> str:
        return f"exp({self.e})"


@dataclass(frozen=True)
class Log(Expr):
    """Natural logarithm."""
    e: Expr

    def free_vars(self) -> FrozenSet[str]:
        return self.e.free_vars()

    def compile(self, var_order: list[str]) -> KernelExpr:
        return {'kind': 'log', 'e': self.e.compile(var_order)}

    def evaluate(self, env: EvalEnv) -> float:
        return math.log(float(self.e.evaluate(env)))

    def __repr__(self) -> str:
        return f"log({self.e})"


@dataclass(frozen=True)
class Sqrt(Expr):
    """Square root."""
    e: Expr

    def free_vars(self) -> FrozenSet[str]:
        return self.e.free_vars()

    def compile(self, var_order: list[str]) -> KernelExpr:
        return {'kind': 'sqrt', 'e': self.e.compile(var_order)}

    def evaluate(self, env: EvalEnv) -> float:
        return math.sqrt(float(self.e.evaluate(env)))

    def __repr__(self) -> str:
        return f"sqrt({self.e})"


@dataclass(frozen=True)
class Tan(Expr):
    """Tangent function."""
    e: Expr

    def free_vars(self) -> FrozenSet[str]:
        return self.e.free_vars()

    def compile(self, var_order: list[str]) -> KernelExpr:
        return {'kind': 'tan', 'e': self.e.compile(var_order)}

    def evaluate(self, env: EvalEnv) -> float:
        return math.tan(float(self.e.evaluate(env)))

    def __repr__(self) -> str:
        return f"tan({self.e})"


@dataclass(frozen=True)
class Atan(Expr):
    """Arc tangent function."""
    e: Expr

    def free_vars(self) -> FrozenSet[str]:
        return self.e.free_vars()

    def compile(self, var_order: list[str]) -> KernelExpr:
        return {'kind': 'atan', 'e': self.e.compile(var_order)}

    def evaluate(self, env: EvalEnv) -> float:
        return math.atan(float(self.e.evaluate(env)))

    def __repr__(self) -> str:
        return f"atan({self.e})"


@dataclass(frozen=True)
class Inv(Expr):
    """Multiplicative inverse (1/x)."""
    e: Expr

    def free_vars(self) -> FrozenSet[str]:
        return self.e.free_vars()

    def compile(self, var_order: list[str]) -> KernelExpr:
        return {'kind': 'inv', 'e': self.e.compile(var_order)}

    def evaluate(self, env: EvalEnv) -> float:
        return 1.0 / float(self.e.evaluate(env))

    def __repr__(self) -> str:
        return f"inv({self.e})"


@dataclass(frozen=True)
class Arsinh(Expr):
    """Inverse hyperbolic sine (arsinh)."""
    e: Expr

    def free_vars(self) -> FrozenSet[str]:
        return self.e.free_vars()

    def compile(self, var_order: list[str]) -> KernelExpr:
        return {'kind': 'arsinh', 'e': self.e.compile(var_order)}

    def evaluate(self, env: EvalEnv) -> float:
        return math.asinh(float(self.e.evaluate(env)))

    def __repr__(self) -> str:
        return f"arsinh({self.e})"


@dataclass(frozen=True)
class Atanh(Expr):
    """Inverse hyperbolic tangent (atanh)."""
    e: Expr

    def free_vars(self) -> FrozenSet[str]:
        return self.e.free_vars()

    def compile(self, var_order: list[str]) -> KernelExpr:
        return {'kind': 'atanh', 'e': self.e.compile(var_order)}

    def evaluate(self, env: EvalEnv) -> float:
        return math.atanh(float(self.e.evaluate(env)))

    def __repr__(self) -> str:
        return f"atanh({self.e})"


@dataclass(frozen=True)
class Sinc(Expr):
    """
    Sinc function: sinc(x) = sin(x)/x, with sinc(0) = 1.

    This is a kernel primitive because its Taylor series is well-behaved
    and used directly in the Lean kernel for robust evaluation near x=0.
    Using sin(x)/x directly would fail at x=0, but the kernel handles
    sinc properly using its Taylor expansion.
    """
    e: Expr

    def free_vars(self) -> FrozenSet[str]:
        return self.e.free_vars()

    def compile(self, var_order: list[str]) -> KernelExpr:
        return {'kind': 'sinc', 'e': self.e.compile(var_order)}

    def evaluate(self, env: EvalEnv) -> float:
        x = float(self.e.evaluate(env))
        if abs(x) < 1e-10:
            return 1.0  # sinc(0) = 1
        return math.sin(x) / x

    def __repr__(self) -> str:
        return f"sinc({self.e})"


@dataclass(frozen=True)
class Erf(Expr):
    """
    Error function: erf(x) = (2/√π) ∫₀ˣ exp(-t²) dt.

    This is a kernel primitive implemented via Taylor model approximation.
    Essential for statistical and financial modeling (e.g., Black-Scholes,
    normal distribution CDF).
    """
    e: Expr

    def free_vars(self) -> FrozenSet[str]:
        return self.e.free_vars()

    def compile(self, var_order: list[str]) -> KernelExpr:
        return {'kind': 'erf', 'e': self.e.compile(var_order)}

    def evaluate(self, env: EvalEnv) -> float:
        return math.erf(float(self.e.evaluate(env)))

    def __repr__(self) -> str:
        return f"erf({self.e})"


# Derived hyperbolic functions (compiled to primitives)

@dataclass(frozen=True)
class Sinh(Expr):
    """Hyperbolic sine."""
    e: Expr

    def free_vars(self) -> FrozenSet[str]:
        return self.e.free_vars()

    def compile(self, var_order: list[str]) -> KernelExpr:
        # Use native sinh expression to avoid interval explosion from exp desugaring
        return {'kind': 'sinh', 'e': self.e.compile(var_order)}

    def evaluate(self, env: EvalEnv) -> float:
        return math.sinh(float(self.e.evaluate(env)))

    def __repr__(self) -> str:
        return f"sinh({self.e})"


@dataclass(frozen=True)
class Cosh(Expr):
    """Hyperbolic cosine."""
    e: Expr

    def free_vars(self) -> FrozenSet[str]:
        return self.e.free_vars()

    def compile(self, var_order: list[str]) -> KernelExpr:
        # Use native cosh expression to avoid interval explosion from exp desugaring
        return {'kind': 'cosh', 'e': self.e.compile(var_order)}

    def evaluate(self, env: EvalEnv) -> float:
        return math.cosh(float(self.e.evaluate(env)))

    def __repr__(self) -> str:
        return f"cosh({self.e})"


@dataclass(frozen=True)
class Tanh(Expr):
    """Hyperbolic tangent."""
    e: Expr

    def free_vars(self) -> FrozenSet[str]:
        return self.e.free_vars()

    def compile(self, var_order: list[str]) -> KernelExpr:
        # Use native tanh expression to avoid interval explosion from exp desugaring
        return {'kind': 'tanh', 'e': self.e.compile(var_order)}

    def evaluate(self, env: EvalEnv) -> float:
        return math.tanh(float(self.e.evaluate(env)))

    def __repr__(self) -> str:
        return f"tanh({self.e})"


# Public constructors

def var(name: str) -> Variable:
    """Create a symbolic variable with the given name."""
    if not isinstance(name, str):
        raise TypeError(f"Variable name must be a string, got {type(name).__name__}")
    if not name:
        raise ValueError("Variable name cannot be empty")
    return Variable(name)


def const(value: Union[int, float, Fraction]) -> Const:
    """Create a constant expression."""
    return Const(value)


# Function constructors

def sin(e: ExprLike) -> Sin:
    """Sine function."""
    return Sin(_to_expr(e))


def cos(e: ExprLike) -> Cos:
    """Cosine function."""
    return Cos(_to_expr(e))


def exp(e: ExprLike) -> Exp:
    """Exponential function."""
    return Exp(_to_expr(e))


def log(e: ExprLike) -> Log:
    """Natural logarithm."""
    return Log(_to_expr(e))


def sqrt(e: ExprLike) -> Sqrt:
    """Square root."""
    return Sqrt(_to_expr(e))


def tan(e: ExprLike) -> Tan:
    """Tangent function."""
    return Tan(_to_expr(e))


def atan(e: ExprLike) -> Atan:
    """Arc tangent function."""
    return Atan(_to_expr(e))


def inv(e: ExprLike) -> Inv:
    """Multiplicative inverse (1/x)."""
    return Inv(_to_expr(e))


def sinh(e: ExprLike) -> Sinh:
    """Hyperbolic sine."""
    return Sinh(_to_expr(e))


def cosh(e: ExprLike) -> Cosh:
    """Hyperbolic cosine."""
    return Cosh(_to_expr(e))


def tanh(e: ExprLike) -> Tanh:
    """Hyperbolic tangent."""
    return Tanh(_to_expr(e))


def arsinh(e: ExprLike) -> Arsinh:
    """Inverse hyperbolic sine."""
    return Arsinh(_to_expr(e))


def atanh(e: ExprLike) -> Atanh:
    """Inverse hyperbolic tangent."""
    return Atanh(_to_expr(e))


def sinc(e: ExprLike) -> Sinc:
    """
    Sinc function: sinc(x) = sin(x)/x, with sinc(0) = 1.

    Use this instead of sin(x)/x for robust evaluation near x=0.
    """
    return Sinc(_to_expr(e))


def erf(e: ExprLike) -> Erf:
    """
    Error function: erf(x) = (2/√π) ∫₀ˣ exp(-t²) dt.

    Used in statistical and financial modeling (normal distribution CDF,
    Black-Scholes formula, etc.).
    """
    return Erf(_to_expr(e))


@dataclass(frozen=True)
class Abs(Expr):
    """
    Absolute value: |e|

    Compiles to native 'abs' kind in the bridge, which uses
    the Lean definition |x| = sqrt(x²).
    """
    e: Expr

    def free_vars(self) -> FrozenSet[str]:
        return self.e.free_vars()

    def compile(self, var_order: list[str]) -> KernelExpr:
        return {'kind': 'abs', 'e': self.e.compile(var_order)}

    def evaluate(self, env: EvalEnv) -> float:
        return builtins_abs(float(self.e.evaluate(env)))

    def __repr__(self) -> str:
        return f"abs({self.e})"


@dataclass(frozen=True)
class MinExpr(Expr):
    """
    Minimum of two expressions.

    Compiles to native 'min' kind in the bridge, which uses
    min(a, b) = (a + b - |a - b|) / 2
    """
    e1: Expr
    e2: Expr

    def free_vars(self) -> FrozenSet[str]:
        return self.e1.free_vars() | self.e2.free_vars()

    def compile(self, var_order: list[str]) -> KernelExpr:
        return {
            'kind': 'min',
            'e1': self.e1.compile(var_order),
            'e2': self.e2.compile(var_order)
        }

    def evaluate(self, env: EvalEnv) -> EvalResult:
        return min(self.e1.evaluate(env), self.e2.evaluate(env))

    def __repr__(self) -> str:
        return f"Min({self.e1}, {self.e2})"


@dataclass(frozen=True)
class MaxExpr(Expr):
    """
    Maximum of two expressions.

    Compiles to native 'max' kind in the bridge, which uses
    max(a, b) = (a + b + |a - b|) / 2
    """
    e1: Expr
    e2: Expr

    def free_vars(self) -> FrozenSet[str]:
        return self.e1.free_vars() | self.e2.free_vars()

    def compile(self, var_order: list[str]) -> KernelExpr:
        return {
            'kind': 'max',
            'e1': self.e1.compile(var_order),
            'e2': self.e2.compile(var_order)
        }

    def evaluate(self, env: EvalEnv) -> EvalResult:
        return max(self.e1.evaluate(env), self.e2.evaluate(env))

    def __repr__(self) -> str:
        return f"Max({self.e1}, {self.e2})"


def abs_(e: ExprLike) -> Abs:
    """Absolute value."""
    return Abs(_to_expr(e))


# Alias for abs to avoid shadowing builtin
abs = abs_


def Min(a: ExprLike, b: ExprLike) -> MinExpr:
    """
    Minimum of two expressions.

    Compiles to native 'min' kind in the bridge, which uses
    min(a, b) = (a + b - |a - b|) / 2

    This identity allows interval arithmetic to work correctly without branching.
    """
    return MinExpr(_to_expr(a), _to_expr(b))


def Max(a: ExprLike, b: ExprLike) -> MaxExpr:
    """
    Maximum of two expressions.

    Compiles to native 'max' kind in the bridge, which uses
    max(a, b) = (a + b + |a - b|) / 2

    This identity allows interval arithmetic to work correctly without branching.
    """
    return MaxExpr(_to_expr(a), _to_expr(b))


def clamp(x: ExprLike, lo: ExprLike, hi: ExprLike) -> Expr:
    """
    Clamp x to the range [lo, hi]: clamp(x, lo, hi) = min(max(x, lo), hi)

    Returns lo if x < lo, hi if x > hi, otherwise x.

    WARNING: Uses Min/Max which involve sqrt/log. For better performance,
    consider restricting the domain of x to [lo, hi] directly.
    """
    return Min(Max(x, lo), hi)
