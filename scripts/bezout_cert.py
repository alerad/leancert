#!/usr/bin/env python3
"""Generate untrusted LeanCert Bézout certificate data with SymPy.

LeanCert rechecks the printed identity using exact rational arithmetic. This
script is a convenience frontend, not part of the trusted proof path.

Example:
    python scripts/bezout_cert.py --coeffs=-2,0,0,1
"""

from __future__ import annotations

import argparse
import math
from functools import reduce

try:
    import sympy as sp
except ImportError as exc:  # pragma: no cover - depends on the user's frontend
    raise SystemExit("SymPy is required: python -m pip install sympy") from exc


def parse_coeffs(raw: str) -> list[sp.Rational]:
    values = [value.strip() for value in raw.split(",")]
    if not values or any(not value for value in values):
        raise argparse.ArgumentTypeError("expected comma-separated rational coefficients")
    try:
        return [sp.Rational(value) for value in values]
    except (TypeError, ValueError) as exc:
        raise argparse.ArgumentTypeError(str(exc)) from exc


def lcm(values: list[int]) -> int:
    return reduce(math.lcm, values, 1)


def lean_rat(value: sp.Rational) -> str:
    numerator, denominator = int(value.p), int(value.q)
    if denominator == 1:
        return str(numerator)
    return f"({numerator} / {denominator} : ℚ)"


def ascending_coeffs(poly: sp.Poly) -> list[sp.Rational]:
    degree = max(poly.degree(), 0)
    return [sp.Rational(poly.nth(i)) for i in range(degree + 1)]


def qpoly_term(poly: sp.Poly) -> str:
    body = ", ".join(lean_rat(value) for value in ascending_coeffs(poly))
    return f"⟨#[{body}]⟩"


def main() -> None:
    parser = argparse.ArgumentParser(
        description="print an untrusted LeanCert BezoutCert for P and P'"
    )
    parser.add_argument(
        "--coeffs",
        required=True,
        type=parse_coeffs,
        help="ascending coefficients, for example -2,0,0,1 for x^3-2",
    )
    args = parser.parse_args()

    x = sp.Symbol("x")
    expression = sum(value * x**i for i, value in enumerate(args.coeffs))
    polynomial = sp.Poly(expression, x, domain=sp.QQ)
    derivative = polynomial.diff()
    a_expr, b_expr, gcd_expr = sp.gcdex(polynomial, derivative)
    gcd_poly = sp.Poly(gcd_expr, x, domain=sp.QQ)
    if gcd_poly.degree() > 0:
        raise SystemExit("P and P' are not coprime; no nonzero constant certificate exists")

    a_poly = sp.Poly(a_expr, x, domain=sp.QQ)
    b_poly = sp.Poly(b_expr, x, domain=sp.QQ)
    denominators = [int(value.q) for poly in (a_poly, b_poly, gcd_poly)
                    for value in ascending_coeffs(poly)]
    scale = lcm(denominators)
    a_poly = sp.Poly(scale * a_poly.as_expr(), x, domain=sp.QQ)
    b_poly = sp.Poly(scale * b_poly.as_expr(), x, domain=sp.QQ)
    c = sp.Rational(scale * gcd_poly.nth(0))

    print("def certificate : BezoutCert where")
    print(f"  A := {qpoly_term(a_poly)}")
    print(f"  B := {qpoly_term(b_poly)}")
    print(f"  c := {lean_rat(c)}")


if __name__ == "__main__":
    main()
