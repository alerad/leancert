# LeanBound v2 SDK - Exceptions
# Copyright (c) 2024 LeanBound Contributors. All rights reserved.

"""Exception hierarchy for LeanBound v2."""

from __future__ import annotations
from typing import TYPE_CHECKING, Optional, Any, List

if TYPE_CHECKING:
    from .domain import Interval, Box


# Supported expression kinds for reference in error messages
SUPPORTED_KINDS = [
    'const', 'var', 'add', 'sub', 'mul', 'div', 'neg', 'inv',
    'sin', 'cos', 'tan', 'exp', 'log', 'sqrt', 'pow', 'abs',
    'sinh', 'cosh', 'tanh', 'atan', 'arsinh', 'atanh',
    'sinc', 'erf', 'min', 'max',
]

# Partial functions that require domain constraints
PARTIAL_FUNCTIONS = {
    'log': 'log(x) requires x > 0',
    'sqrt': 'sqrt(x) requires x >= 0',
    'inv': '1/x requires x != 0',
    'div': 'a/b requires b != 0',
    'atanh': 'atanh(x) requires -1 < x < 1',
}


class LeanBoundError(Exception):
    """Base class for all LeanBound exceptions."""
    pass


class CompilationError(LeanBoundError):
    """Raised when expression compilation fails."""
    pass


class DomainError(LeanBoundError):
    """Raised when domain is invalid or incompatible with expression."""
    pass


class VerificationFailed(LeanBoundError):
    """Raised when a bound verification fails."""

    def __init__(
        self,
        message: str,
        computed_bound: Optional[Any] = None,
        counterexample_box: Optional['Box'] = None
    ):
        super().__init__(message)
        self.computed_bound = computed_bound
        self.counterexample_box = counterexample_box


class VerificationTimeout(LeanBoundError):
    """Raised when verification times out."""

    def __init__(self, message: str, elapsed_seconds: float, partial_result: Optional[Any] = None):
        super().__init__(message)
        self.elapsed_seconds = elapsed_seconds
        self.partial_result = partial_result


class BridgeError(LeanBoundError):
    """Raised when communication with Lean kernel fails."""

    def __init__(self, message: str):
        # Parse and enhance error messages from the bridge
        enhanced_message = _enhance_bridge_error(message)
        super().__init__(enhanced_message)
        self.raw_message = message


class ExpressionError(LeanBoundError):
    """Raised when an unsupported expression is used."""

    def __init__(
        self,
        message: str,
        expression_kind: Optional[str] = None,
        suggestion: Optional[str] = None,
    ):
        full_message = message
        if suggestion:
            full_message += f"\n  Suggestion: {suggestion}"
        super().__init__(full_message)
        self.expression_kind = expression_kind
        self.suggestion = suggestion


class UnsupportedExpressionError(ExpressionError):
    """Raised when an expression kind is not supported by LeanBound."""

    def __init__(self, kind: str, context: Optional[str] = None):
        suggestion = _get_suggestion_for_kind(kind)
        message = f"Unsupported expression kind: '{kind}'"
        if context:
            message += f" in {context}"
        super().__init__(message, expression_kind=kind, suggestion=suggestion)


class PartialFunctionError(ExpressionError):
    """Raised when a partial function is used without proper domain constraints."""

    def __init__(self, func_name: str, domain_info: Optional[str] = None):
        constraint = PARTIAL_FUNCTIONS.get(func_name, f"{func_name} has domain restrictions")
        message = f"Partial function '{func_name}' may be undefined on given domain."
        suggestion = f"{constraint}. Ensure your domain satisfies this constraint."
        if domain_info:
            message += f" Domain: {domain_info}"
        super().__init__(message, expression_kind=func_name, suggestion=suggestion)


def _enhance_bridge_error(message: str) -> str:
    """Enhance bridge error messages with helpful context."""
    # Check for unknown expression kind error
    if "Unknown expression kind:" in message:
        # Extract the kind name
        import re
        match = re.search(r"Unknown expression kind:\s*(\w+)", message)
        if match:
            kind = match.group(1)
            suggestion = _get_suggestion_for_kind(kind)
            enhanced = f"Unknown expression kind: '{kind}'"
            if suggestion:
                enhanced += f"\n  Suggestion: {suggestion}"
            enhanced += f"\n  Supported kinds: {', '.join(SUPPORTED_KINDS[:10])}..."
            return enhanced

    # Check for JSON parse errors
    if "JSON parse error" in message:
        return f"{message}\n  Check that all expression fields are properly formatted."

    # Check for missing fields
    if "Missing" in message and "field" in message:
        return f"{message}\n  Ensure the expression is properly constructed."

    return message


def _get_suggestion_for_kind(kind: str) -> Optional[str]:
    """Get a helpful suggestion for an unsupported expression kind."""
    suggestions = {
        # Common misspellings
        'sine': "Did you mean 'sin'? Use sin(x) for sine.",
        'cosine': "Did you mean 'cos'? Use cos(x) for cosine.",
        'tangent': "Did you mean 'tan'? Use tan(x) for tangent.",
        'arctan': "Did you mean 'atan'? Use atan(x) for arctangent.",
        'arcsin': "arcsin is not yet supported. Consider using atan(x/sqrt(1-x^2)).",
        'arccos': "arccos is not yet supported. Consider using pi/2 - arcsin equivalent.",
        'asin': "asin is not yet supported. Consider using atan(x/sqrt(1-x^2)).",
        'acos': "acos is not yet supported. Consider using pi/2 - asin equivalent.",
        'ln': "Did you mean 'log'? Use log(x) for natural logarithm.",
        'exp2': "exp2 is not directly supported. Use exp(x * log(2)) instead.",
        'log10': "log10 is not directly supported. Use log(x) / log(10) instead.",
        'log2': "log2 is not directly supported. Use log(x) / log(2) instead.",
        'power': "Did you mean 'pow'? Use x ** n for integer powers.",
        'square': "Use x ** 2 or x * x for squaring.",
        'cube': "Use x ** 3 for cubing.",
        'cbrt': "Cube root is not directly supported. Use exp(log(x)/3) for x > 0.",
        'sign': "sign is not supported. Consider using x / abs(x) for x != 0.",
        'floor': "floor is not supported (discontinuous function).",
        'ceil': "ceil is not supported (discontinuous function).",
        'round': "round is not supported (discontinuous function).",
        'mod': "mod is not supported (discontinuous function).",
        'hypot': "hypot is not directly supported. Use sqrt(x^2 + y^2).",
        'atan2': "atan2 is not yet supported. Consider case analysis with atan.",
        'gamma': "gamma function is not yet supported.",
        'lgamma': "lgamma is not yet supported.",
        'bessel': "Bessel functions are not yet supported.",
        'coth': "coth is not directly supported. Use cosh(x)/sinh(x) or 1/tanh(x).",
        'sech': "sech is not directly supported. Use 1/cosh(x).",
        'csch': "csch is not directly supported. Use 1/sinh(x).",
        'asinh': "Did you mean 'arsinh'? Use arsinh(x) for inverse hyperbolic sine.",
        'acosh': "acosh is not yet supported.",
        'arcsinh': "Did you mean 'arsinh'? Use arsinh(x) for inverse hyperbolic sine.",
        'arccosh': "arccosh is not yet supported.",
        'arctanh': "Did you mean 'atanh'? Use atanh(x) for inverse hyperbolic tangent.",
    }
    return suggestions.get(kind.lower())
