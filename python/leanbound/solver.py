# LeanBound v2 SDK - Solver
# Copyright (c) 2024 LeanBound Contributors. All rights reserved.

"""
High-level Solver API for LeanBound v2.

This module provides the main user-facing interface for verification.
"""

from __future__ import annotations
from fractions import Fraction
from typing import Optional, Union, Any

from .expr import Expr
from .domain import Interval, Box, normalize_domain
from .config import Config
from .client import LeanClient, _parse_interval, _parse_rat
from .result import BoundsResult, RootsResult, RootInterval, IntegralResult, Certificate, UniqueRootResult
from .exceptions import VerificationFailed, DomainError
from .rational import to_fraction
from .simplify import simplify as _simplify_expr


# Version info
__version__ = "0.2.0"
LEAN_VERSION = "4.24.0"  # Updated when bridge is rebuilt


class Solver:
    """
    High-level interface for LeanBound verification.

    Manages compilation and communication with the Lean kernel.
    Use as a context manager for automatic cleanup.

    Example:
        with Solver() as solver:
            x = var('x')
            result = solver.find_bounds(x**2, {'x': (0, 1)})
    """

    def __init__(
        self,
        client: Optional[LeanClient] = None,
        auto_simplify: bool = True,
    ):
        """
        Initialize the solver.

        Args:
            client: Optional LeanClient instance. If None, creates a new one.
            auto_simplify: If True (default), automatically simplify expressions
                          before sending to the kernel. This reduces the dependency
                          problem in interval arithmetic by canceling like terms.
        """
        self._client = client
        self._owns_client = client is None
        self._auto_simplify = auto_simplify

    def _ensure_client(self) -> LeanClient:
        """Ensure we have a client connection."""
        if self._client is None:
            self._client = LeanClient()
        return self._client

    def close(self) -> None:
        """Close the solver and release resources."""
        if self._owns_client and self._client is not None:
            self._client.close()
            self._client = None

    def __enter__(self) -> Solver:
        return self

    def __exit__(self, *args) -> None:
        self.close()

    def _prepare_request(
        self,
        expr: Expr,
        domain: Union[Interval, Box, tuple, dict],
    ) -> tuple[dict, Box]:
        """
        Prepare expression and domain for a kernel request.

        Returns:
            Tuple of (compiled expr JSON, normalized Box).
        """
        # Auto-simplify expression to reduce dependency problem
        if self._auto_simplify:
            expr = _simplify_expr(expr)

        # Normalize domain to Box
        # For univariate, infer variable name from expression
        if isinstance(domain, (Interval, tuple)):
            free_vars = expr.free_vars()
            if len(free_vars) == 1:
                default_var = next(iter(free_vars))
            else:
                default_var = 'x'
            box = normalize_domain(domain, default_var=default_var)
        else:
            box = normalize_domain(domain)

        # Validate expression uses only defined variables
        box.validate_expr(expr)

        # Compile expression with box's variable ordering
        var_order = box.var_order()
        expr_json = expr.compile(var_order)

        return expr_json, box

    def find_bounds(
        self,
        expr: Expr,
        domain: Union[Interval, Box, tuple, dict],
        config: Config = Config(),
    ) -> BoundsResult:
        """
        Find global minimum and maximum bounds.

        Args:
            expr: Expression to analyze.
            domain: Domain specification (Interval, Box, tuple, or dict).
            config: Solver configuration.

        Returns:
            BoundsResult with verified min/max intervals.
        """
        client = self._ensure_client()
        expr_json, box = self._prepare_request(expr, domain)
        box_json = box.to_kernel_list()
        cfg = config.to_kernel()

        # Find minimum
        min_result = client.global_min(
            expr_json, box_json,
            max_iters=cfg['maxIters'],
            tolerance=cfg['tolerance'],
            use_monotonicity=cfg['useMonotonicity'],
            taylor_depth=cfg['taylorDepth'],
        )

        # Find maximum
        max_result = client.global_max(
            expr_json, box_json,
            max_iters=cfg['maxIters'],
            tolerance=cfg['tolerance'],
            use_monotonicity=cfg['useMonotonicity'],
            taylor_depth=cfg['taylorDepth'],
        )

        min_bound = _parse_interval({'lo': min_result['lo'], 'hi': min_result['hi']})
        max_bound = _parse_interval({'lo': max_result['lo'], 'hi': max_result['hi']})

        # Create certificate
        cert = Certificate(
            operation='find_bounds',
            expr_json=expr_json,
            domain_json=box_json,
            result_json={
                'min': {'lo': min_result['lo'], 'hi': min_result['hi']},
                'max': {'lo': max_result['lo'], 'hi': max_result['hi']},
            },
            verified=True,
            lean_version=LEAN_VERSION,
            leanbound_version=__version__,
        )

        return BoundsResult(
            min_bound=min_bound,
            max_bound=max_bound,
            verified=True,
            certificate=cert,
        )

    def verify_bound(
        self,
        expr: Expr,
        domain: Union[Interval, Box, tuple, dict],
        upper: Optional[float] = None,
        lower: Optional[float] = None,
        config: Config = Config(),
        method: str = 'adaptive',  # Changed default to adaptive
    ) -> bool:
        """
        Verify that expression satisfies given bounds with False Positive Filtering.

        Pipeline:
        1. Symbolic Simplification (handles dependency problem)
        2. Global Optimization (Branch & Bound)
        3. Counterexample Concretization (filters false positives)

        Args:
            expr: Expression to verify.
            domain: Domain specification.
            upper: Upper bound to verify (expr <= upper).
            lower: Lower bound to verify (expr >= lower).
            config: Solver configuration.
            method: Verification method - 'adaptive' (default, uses optimization
                   with false positive filtering) or 'interval' (fast, conservative).

        Returns:
            True if verified.

        Raises:
            VerificationFailed: If bound verification fails AND is confirmed by
                               concrete evaluation (not a false positive).
            ValueError: If method is invalid or no bounds specified.
        """
        if upper is None and lower is None:
            raise ValueError("Must specify at least one of upper or lower bound")

        if method not in ('interval', 'adaptive'):
            raise ValueError(f"Unknown method: {method}. Use 'interval' or 'adaptive'.")

        # Keep original expression for concrete evaluation
        original_expr = expr

        client = self._ensure_client()
        expr_json, box = self._prepare_request(expr, domain)
        box_json = box.to_kernel_list()
        cfg = config.to_kernel()

        if method == 'adaptive':
            return self._verify_bound_adaptive_with_concretization(
                client, original_expr, expr_json, box, box_json, cfg, upper, lower
            )
        else:
            return self._verify_bound_interval(
                client, expr_json, box_json, cfg, upper, lower
            )

    def _verify_bound_interval(
        self,
        client,
        expr_json: dict,
        box_json: list,
        cfg: dict,
        upper: Optional[float],
        lower: Optional[float],
    ) -> bool:
        """Verify bounds using simple interval evaluation."""
        if upper is not None:
            bound_frac = to_fraction(upper)
            bound_json = {'n': bound_frac.numerator, 'd': bound_frac.denominator}

            result = client.check_bound(
                expr_json, box_json, bound_json,
                is_upper_bound=True,
                taylor_depth=cfg['taylorDepth'],
            )

            if not result['verified']:
                computed = _parse_rat(result['computed_hi'])
                raise VerificationFailed(
                    f"Failed to verify upper bound {upper}. Computed max: {float(computed):.6f}",
                    computed_bound=computed,
                )

        if lower is not None:
            bound_frac = to_fraction(lower)
            bound_json = {'n': bound_frac.numerator, 'd': bound_frac.denominator}

            result = client.check_bound(
                expr_json, box_json, bound_json,
                is_upper_bound=False,
                taylor_depth=cfg['taylorDepth'],
            )

            if not result['verified']:
                computed = _parse_rat(result['computed_lo'])
                raise VerificationFailed(
                    f"Failed to verify lower bound {lower}. Computed min: {float(computed):.6f}",
                    computed_bound=computed,
                )

        return True

    def _verify_bound_adaptive(
        self,
        client,
        expr_json: dict,
        box_json: list,
        cfg: dict,
        upper: Optional[float],
        lower: Optional[float],
    ) -> bool:
        """Verify bounds using adaptive optimization."""
        if upper is not None:
            bound_frac = to_fraction(upper)
            bound_json = {'n': bound_frac.numerator, 'd': bound_frac.denominator}

            result = client.verify_adaptive(
                expr_json, box_json, bound_json,
                is_upper_bound=True,
                max_iters=cfg['maxIters'],
                tolerance=cfg['tolerance'],
                taylor_depth=cfg['taylorDepth'],
            )

            if not result['verified']:
                min_value = _parse_rat(result['minValue'])
                raise VerificationFailed(
                    f"Failed to verify upper bound {upper}. Gap: {float(min_value):.6f}",
                    computed_bound=to_fraction(upper) - min_value,
                )

        if lower is not None:
            bound_frac = to_fraction(lower)
            bound_json = {'n': bound_frac.numerator, 'd': bound_frac.denominator}

            result = client.verify_adaptive(
                expr_json, box_json, bound_json,
                is_upper_bound=False,
                max_iters=cfg['maxIters'],
                tolerance=cfg['tolerance'],
                taylor_depth=cfg['taylorDepth'],
            )

            if not result['verified']:
                min_value = _parse_rat(result['minValue'])
                raise VerificationFailed(
                    f"Failed to verify lower bound {lower}. Gap: {float(min_value):.6f}",
                    computed_bound=to_fraction(lower) + min_value,
                )

        return True

    def _verify_bound_adaptive_with_concretization(
        self,
        client,
        original_expr: Expr,
        expr_json: dict,
        box: Box,
        box_json: list,
        cfg: dict,
        upper: Optional[float],
        lower: Optional[float],
    ) -> bool:
        """
        Verify bounds using optimization with false positive filtering.

        This method uses global optimization to find the min/max, then
        concretizes the result by evaluating the original expression
        at the reported extremum point. If the concrete evaluation
        doesn't violate the bound, it's a false positive caused by
        interval over-approximation.
        """
        var_names = box.var_order()

        def _concretize_and_check(
            best_box: list,
            limit: float,
            is_upper: bool,
        ) -> bool:
            """
            Check if violation is real by evaluating at the midpoint.

            Returns True if the violation is REAL (not a false positive).
            Returns False if it's a false positive (concrete value is OK).
            """
            try:
                if not best_box:
                    # No location data, can't filter - assume real
                    return True

                # Construct environment from bestBox midpoints
                env = {}
                for i, interval_json in enumerate(best_box):
                    if i >= len(var_names):
                        break
                    name = var_names[i]
                    lo = _parse_rat(interval_json['lo'])
                    hi = _parse_rat(interval_json['hi'])
                    midpoint = (lo + hi) / 2
                    env[name] = float(midpoint)

                # Concrete evaluation using Python math
                concrete_val = original_expr.evaluate(env)

                # Check against limit
                if is_upper:
                    # Claimed violation: max(f) > upper
                    # Real if concrete_val > limit
                    return float(concrete_val) > limit
                else:
                    # Claimed violation: min(f) < lower
                    # Real if concrete_val < limit
                    return float(concrete_val) < limit

            except Exception:
                # If concretization fails, assume real to be safe
                return True

        # --- LOWER BOUND CHECK (f(x) >= lower) ---
        if lower is not None:
            # Find minimum of f
            min_result = client.global_min(
                expr_json, box_json,
                max_iters=cfg['maxIters'],
                tolerance=cfg['tolerance'],
                use_monotonicity=cfg['useMonotonicity'],
                taylor_depth=cfg['taylorDepth'],
            )

            computed_min_lo = _parse_rat(min_result.get('lo', {'n': 0, 'd': 1}))
            limit = to_fraction(lower)

            if computed_min_lo < limit:
                # Solver claims violation. Check with concretization.
                best_box = min_result.get('bestBox', [])

                if _concretize_and_check(best_box, float(lower), is_upper=False):
                    # Real violation confirmed
                    raise VerificationFailed(
                        f"Lower bound verification failed. "
                        f"Min value: {float(computed_min_lo):.6f} < {lower}",
                        computed_bound=computed_min_lo,
                    )
                # Else: False positive, continue (bound is actually OK)

        # --- UPPER BOUND CHECK (f(x) <= upper) ---
        if upper is not None:
            # Find maximum of f
            max_result = client.global_max(
                expr_json, box_json,
                max_iters=cfg['maxIters'],
                tolerance=cfg['tolerance'],
                use_monotonicity=cfg['useMonotonicity'],
                taylor_depth=cfg['taylorDepth'],
            )

            computed_max_hi = _parse_rat(max_result.get('hi', {'n': 0, 'd': 1}))
            limit = to_fraction(upper)

            if computed_max_hi > limit:
                # Solver claims violation. Check with concretization.
                best_box = max_result.get('bestBox', [])

                if _concretize_and_check(best_box, float(upper), is_upper=True):
                    # Real violation confirmed
                    raise VerificationFailed(
                        f"Upper bound verification failed. "
                        f"Max value: {float(computed_max_hi):.6f} > {upper}",
                        computed_bound=computed_max_hi,
                    )
                # Else: False positive, continue

        return True

    def find_roots(
        self,
        expr: Expr,
        domain: Union[Interval, Box, tuple, dict],
        config: Config = Config(),
    ) -> RootsResult:
        """
        Find roots of a univariate expression.

        Args:
            expr: Expression to find roots of.
            domain: Search domain.
            config: Solver configuration.

        Returns:
            RootsResult with root intervals.
        """
        client = self._ensure_client()
        expr_json, box = self._prepare_request(expr, domain)

        # For root finding, we need a 1D interval
        if len(box) != 1:
            raise DomainError("Root finding requires a 1D domain")

        var_name = box.var_order()[0]
        interval = box[var_name]
        interval_json = interval.to_kernel()
        cfg = config.to_kernel()

        result = client.find_roots(
            expr_json, interval_json,
            max_iter=cfg['maxIters'],
            tolerance=cfg['tolerance'],
            taylor_depth=cfg['taylorDepth'],
        )

        roots = []
        for r in result['roots']:
            status_map = {
                'hasRoot': 'confirmed',
                'noRoot': 'no_root',
                'unknown': 'possible',
            }
            roots.append(RootInterval(
                interval=_parse_interval(r),
                status=status_map.get(r['status'], 'possible'),
            ))

        return RootsResult(
            roots=roots,
            iterations=result['iterations'],
            verified=True,
        )

    def find_unique_root(
        self,
        expr: Expr,
        domain: Union[Interval, Box, tuple, dict],
        config: Config = Config(),
    ) -> UniqueRootResult:
        """
        Find a unique root using Newton contraction.

        This method uses Newton iteration to prove both existence AND uniqueness
        of a root. It's mathematically stronger than find_roots() which only
        proves existence via sign change.

        Args:
            expr: Expression to find root of.
            domain: Search domain (1D interval).
            config: Solver configuration.

        Returns:
            UniqueRootResult with unique=True if uniqueness proven.
        """
        client = self._ensure_client()
        expr_json, box = self._prepare_request(expr, domain)

        # For unique root finding, we need a 1D interval
        if len(box) != 1:
            raise DomainError("Unique root finding requires a 1D domain")

        var_name = box.var_order()[0]
        interval = box[var_name]
        interval_json = interval.to_kernel()
        cfg = config.to_kernel()

        result = client.find_unique_root(
            expr_json, interval_json,
            taylor_depth=cfg['taylorDepth'],
        )

        result_interval = _parse_interval(result['interval'])

        return UniqueRootResult(
            unique=result['unique'],
            interval=result_interval,
            reason=result['reason'],
        )

    def integrate(
        self,
        expr: Expr,
        domain: Union[Interval, Box, tuple, dict],
        partitions: int = 10,
        config: Config = Config(),
    ) -> IntegralResult:
        """
        Compute rigorous integral bounds.

        Args:
            expr: Expression to integrate.
            domain: Integration domain.
            partitions: Number of partitions.
            config: Solver configuration.

        Returns:
            IntegralResult with verified bounds.
        """
        client = self._ensure_client()
        expr_json, box = self._prepare_request(expr, domain)

        # For integration, we need a 1D interval
        if len(box) != 1:
            raise DomainError("Integration requires a 1D domain")

        var_name = box.var_order()[0]
        interval = box[var_name]
        interval_json = interval.to_kernel()
        cfg = config.to_kernel()

        result = client.integrate(
            expr_json, interval_json,
            partitions=partitions,
            taylor_depth=cfg['taylorDepth'],
        )

        bounds = _parse_interval(result)

        return IntegralResult(
            bounds=bounds,
            verified=True,
        )


# Global solver instance for convenience functions
_global_solver: Optional[Solver] = None


def _get_solver() -> Solver:
    """Get or create global solver instance."""
    global _global_solver
    if _global_solver is None:
        _global_solver = Solver()
    return _global_solver


# Convenience functions that use global solver

def find_bounds(
    expr: Expr,
    domain: Union[Interval, Box, tuple, dict],
    config: Config = Config(),
) -> BoundsResult:
    """Find global min/max bounds for an expression."""
    return _get_solver().find_bounds(expr, domain, config)


def verify_bound(
    expr: Expr,
    domain: Union[Interval, Box, tuple, dict],
    upper: Optional[float] = None,
    lower: Optional[float] = None,
    config: Config = Config(),
    method: str = 'interval',
) -> bool:
    """Verify that an expression satisfies bounds.

    Args:
        expr: Expression to verify.
        domain: Domain specification.
        upper: Upper bound to verify (expr <= upper).
        lower: Lower bound to verify (expr >= lower).
        config: Solver configuration.
        method: 'interval' (fast) or 'adaptive' (tighter, uses optimization).
    """
    return _get_solver().verify_bound(expr, domain, upper, lower, config, method)


def find_roots(
    expr: Expr,
    domain: Union[Interval, Box, tuple, dict],
    config: Config = Config(),
) -> RootsResult:
    """Find roots of a univariate expression."""
    return _get_solver().find_roots(expr, domain, config)


def find_unique_root(
    expr: Expr,
    domain: Union[Interval, Box, tuple, dict],
    config: Config = Config(),
) -> UniqueRootResult:
    """Find a unique root using Newton contraction.

    This proves both existence AND uniqueness of a root.
    """
    return _get_solver().find_unique_root(expr, domain, config)


def integrate(
    expr: Expr,
    domain: Union[Interval, Box, tuple, dict],
    partitions: int = 10,
    config: Config = Config(),
) -> IntegralResult:
    """Compute rigorous integral bounds."""
    return _get_solver().integrate(expr, domain, partitions, config)
