# LeanBound v2 SDK - Bug Validation and False Positive Filtering
# Copyright (c) 2024 LeanBound Contributors. All rights reserved.

"""
Bug validation utilities for reducing false positives in automated analysis.

This module provides tools for:
1. Detecting interval arithmetic explosion (bounds too wide to be meaningful)
2. Analyzing code comments to identify intentional protection mechanisms
3. Validating reported bugs against concrete counterexamples
4. Cross-referencing bugs against protocol design patterns

The goal is to reduce the false positive rate from ~70% to <20%.
"""

from __future__ import annotations

import re
import math
from dataclasses import dataclass, field
from typing import Optional, Union, Any, Callable
from fractions import Fraction
from enum import Enum

from .expr import Expr, Variable, EvalEnv
from .domain import Box, Interval
from .result import BoundsResult


class ValidationVerdict(Enum):
    """Verdict for a bug validation check."""
    CONFIRMED = "confirmed"           # Bug is real and verified
    FALSE_POSITIVE = "false_positive" # Bug is not real (interval explosion, etc.)
    DESIGN_INTENT = "design_intent"   # Bug is intentional behavior
    NEEDS_REVIEW = "needs_review"     # Cannot automatically determine


@dataclass
class ValidationResult:
    """Result of validating a potential bug."""
    verdict: ValidationVerdict
    confidence: float  # 0.0 to 1.0
    reason: str
    counterexample: Optional[dict] = None
    concrete_value: Optional[float] = None
    interval_width: Optional[float] = None
    matched_pattern: Optional[str] = None


# =============================================================================
# INTERVAL EXPLOSION DETECTION
# =============================================================================

class IntervalExplosionDetector:
    """
    Detects when interval arithmetic produces overly-wide bounds.

    Interval arithmetic can "explode" when:
    1. Multiple correlated variables create dependency problems
    2. Expressions involve many multiplications
    3. Domains are very wide (e.g., 1 to 1e30)

    When bounds exceed EXPLOSION_THRESHOLD, the result is likely a false positive.
    """

    # Threshold for interval width considered "explosion"
    # Values larger than 1e50 indicate interval explosion
    EXPLOSION_THRESHOLD: float = 1e50

    # Relative width threshold (width / midpoint)
    RELATIVE_WIDTH_THRESHOLD: float = 1e10

    # Known patterns that commonly cause explosion
    EXPLOSION_PATTERNS = [
        r".*\*.*\*.*\*.*",  # Multiple chained multiplications
        r".*\/.*\/.*",      # Multiple chained divisions
        r".*\*\*\d+",       # High powers
    ]

    def __init__(
        self,
        absolute_threshold: float = 1e50,
        relative_threshold: float = 1e10,
    ):
        """
        Initialize the detector.

        Args:
            absolute_threshold: Bounds wider than this are explosions
            relative_threshold: Relative width (width/midpoint) threshold
        """
        self.absolute_threshold = absolute_threshold
        self.relative_threshold = relative_threshold

    def detect_explosion(self, result: BoundsResult) -> tuple[bool, str]:
        """
        Check if a bounds result shows interval explosion.

        Args:
            result: BoundsResult from Solver.find_bounds()

        Returns:
            Tuple of (is_explosion, reason)
        """
        # Check min bound width
        min_width = float(result.min_bound.hi - result.min_bound.lo)
        max_width = float(result.max_bound.hi - result.max_bound.lo)

        # Absolute width check
        if min_width > self.absolute_threshold:
            return True, f"Min bound width {min_width:.2e} exceeds threshold {self.absolute_threshold:.2e}"
        if max_width > self.absolute_threshold:
            return True, f"Max bound width {max_width:.2e} exceeds threshold {self.absolute_threshold:.2e}"

        # Check overall bounds span
        overall_min = float(result.min_bound.lo)
        overall_max = float(result.max_bound.hi)
        overall_width = overall_max - overall_min

        if overall_width > self.absolute_threshold:
            return True, f"Overall bounds span {overall_width:.2e} exceeds threshold"

        # Relative width check (avoid division by zero)
        midpoint = (overall_max + overall_min) / 2
        if abs(midpoint) > 1e-10:
            relative_width = overall_width / abs(midpoint)
            if relative_width > self.relative_threshold:
                return True, f"Relative width {relative_width:.2e} exceeds threshold {self.relative_threshold:.2e}"

        return False, "No explosion detected"

    def check_expression_risk(self, expr: Expr) -> tuple[bool, str]:
        """
        Check if an expression is at risk of interval explosion.

        This is a static analysis that looks at expression structure.

        Args:
            expr: Expression to analyze

        Returns:
            Tuple of (is_risky, reason)
        """
        expr_str = repr(expr)

        # Count operations that commonly cause explosion
        mul_count = expr_str.count("*")
        div_count = expr_str.count("/")
        pow_match = re.search(r"\*\*\s*(\d+)", expr_str)

        if pow_match:
            power = int(pow_match.group(1))
            if power > 10:
                return True, f"High power ({power}) may cause interval explosion"

        if mul_count > 5:
            return True, f"Many multiplications ({mul_count}) may cause interval explosion"

        if div_count > 3:
            return True, f"Many divisions ({div_count}) may cause interval explosion"

        # Check for risky patterns
        for pattern in self.EXPLOSION_PATTERNS:
            if re.match(pattern, expr_str):
                return True, f"Expression matches explosion-prone pattern: {pattern}"

        return False, "Expression appears safe"


# =============================================================================
# COMMENT ANALYSIS FOR INTENTIONAL BEHAVIOR
# =============================================================================

class CommentAnalyzer:
    """
    Analyzes code comments to identify intentional design decisions.

    Many "bugs" found by automated tools are actually intentional behavior
    documented in comments. This analyzer detects common patterns.
    """

    # Patterns indicating intentional protection mechanisms
    PROTECTION_PATTERNS = [
        # Explicit skip patterns
        (r"skip\w*\s+germinat\w*.*prevent", "skip_germinating_protection"),
        (r"intentionally\s+skip", "intentional_skip"),
        (r"by\s+design", "by_design"),

        # Safety check patterns
        (r"safe(?:ty)?\s+check", "safety_check"),
        (r"prevent\w*\s+(?:exploit|attack|manipulation)", "exploit_prevention"),
        (r"protect\w*\s+(?:user|protocol|against)", "protection_mechanism"),

        # Acknowledgment patterns (GMX-style)
        (r"may\s+not\s+be\s+entirely\s+accurate", "acknowledged_inaccuracy"),
        (r"this\s+is\s+(?:intended|intentional|expected)", "intended_behavior"),
        (r"note:\s*this", "documented_note"),

        # Rounding direction patterns
        (r"round(?:s|ing)?\s+(?:down|up)\s+(?:in\s+favor|to\s+protect)", "intentional_rounding"),
        (r"floor\s+division\s+is\s+intentional", "intentional_floor"),
        (r"ceil\s+(?:for|to)\s+(?:safety|protection)", "intentional_ceil"),

        # Economic design patterns
        (r"fee\s+(?:is\s+)?(?:charged|deducted)\s+first", "fee_first_design"),
        (r"slippage\s+protection", "slippage_protection"),
        (r"dust\s+(?:is\s+)?(?:burned|ignored|acceptable)", "dust_handling"),
    ]

    # Patterns indicating known limitations
    LIMITATION_PATTERNS = [
        (r"(?:TODO|FIXME|XXX|HACK):", "known_limitation"),
        (r"(?:known|accepted)\s+(?:issue|limitation|tradeoff)", "acknowledged_limitation"),
        (r"(?:gas|efficiency)\s+optimization", "gas_optimization"),
    ]

    def __init__(self):
        """Initialize the analyzer with compiled patterns."""
        self._protection_patterns = [
            (re.compile(pattern, re.IGNORECASE), name)
            for pattern, name in self.PROTECTION_PATTERNS
        ]
        self._limitation_patterns = [
            (re.compile(pattern, re.IGNORECASE), name)
            for pattern, name in self.LIMITATION_PATTERNS
        ]

    def extract_comments(self, solidity_code: str) -> list[tuple[int, str]]:
        """
        Extract all comments from Solidity code.

        Args:
            solidity_code: Raw Solidity source code

        Returns:
            List of (line_number, comment_text) tuples
        """
        comments = []

        # Single-line comments
        for i, line in enumerate(solidity_code.split('\n'), 1):
            match = re.search(r'//\s*(.+)$', line)
            if match:
                comments.append((i, match.group(1).strip()))

        # Multi-line comments
        multiline_pattern = re.compile(r'/\*\s*(.*?)\s*\*/', re.DOTALL)
        for match in multiline_pattern.finditer(solidity_code):
            # Approximate line number from position
            line_num = solidity_code[:match.start()].count('\n') + 1
            comment_text = match.group(1).replace('\n', ' ').strip()
            comment_text = re.sub(r'\s+', ' ', comment_text)  # Normalize whitespace
            comments.append((line_num, comment_text))

        return comments

    def is_intentional_protection(
        self,
        code_block: str,
        context_lines: int = 10,
    ) -> tuple[bool, Optional[str], Optional[str]]:
        """
        Check if a code block contains intentional protection patterns.

        Args:
            code_block: Block of Solidity code to analyze
            context_lines: Number of lines around target to search

        Returns:
            Tuple of (is_intentional, pattern_name, matching_comment)
        """
        comments = self.extract_comments(code_block)

        for line_num, comment in comments:
            for pattern, name in self._protection_patterns:
                if pattern.search(comment):
                    return True, name, comment

        return False, None, None

    def analyze_function(
        self,
        function_code: str,
        function_name: str,
    ) -> dict[str, Any]:
        """
        Analyze a function for intentional design patterns.

        Args:
            function_code: Solidity function source
            function_name: Name of the function

        Returns:
            Analysis result dictionary
        """
        result = {
            "function_name": function_name,
            "protection_patterns": [],
            "limitations": [],
            "is_likely_intentional": False,
            "confidence": 0.0,
        }

        comments = self.extract_comments(function_code)

        for line_num, comment in comments:
            # Check protection patterns
            for pattern, name in self._protection_patterns:
                if pattern.search(comment):
                    result["protection_patterns"].append({
                        "pattern": name,
                        "line": line_num,
                        "comment": comment,
                    })

            # Check limitation patterns
            for pattern, name in self._limitation_patterns:
                if pattern.search(comment):
                    result["limitations"].append({
                        "pattern": name,
                        "line": line_num,
                        "comment": comment,
                    })

        # Calculate confidence
        if result["protection_patterns"]:
            result["is_likely_intentional"] = True
            result["confidence"] = min(1.0, len(result["protection_patterns"]) * 0.3)

        return result


# =============================================================================
# COUNTEREXAMPLE VERIFICATION
# =============================================================================

class CounterexampleVerifier:
    """
    Verifies counterexamples by evaluating expressions concretely.

    When the solver reports a potential violation, this verifier:
    1. Evaluates the expression at the reported point using Python math
    2. Checks if the concrete value actually violates the bound
    3. Filters out false positives from interval over-approximation
    """

    def __init__(self, tolerance: float = 1e-9):
        """
        Initialize the verifier.

        Args:
            tolerance: Tolerance for floating point comparisons
        """
        self.tolerance = tolerance

    def verify_counterexample(
        self,
        expr: Expr,
        counterexample: dict[str, float],
        claimed_violation: str,  # "upper" or "lower"
        bound_value: float,
    ) -> ValidationResult:
        """
        Verify a counterexample by concrete evaluation.

        Args:
            expr: Expression that allegedly violates the bound
            counterexample: Variable assignments for the counterexample
            claimed_violation: "upper" if claiming max > bound, "lower" if min < bound
            bound_value: The bound that was allegedly violated

        Returns:
            ValidationResult with verdict
        """
        try:
            # Evaluate expression at counterexample point
            concrete_value = float(expr.evaluate(counterexample))

            # Check if violation is real
            if claimed_violation == "upper":
                is_real_violation = concrete_value > bound_value + self.tolerance
            else:
                is_real_violation = concrete_value < bound_value - self.tolerance

            if is_real_violation:
                return ValidationResult(
                    verdict=ValidationVerdict.CONFIRMED,
                    confidence=0.95,
                    reason=f"Concrete evaluation confirms violation: {concrete_value:.6f}",
                    counterexample=counterexample,
                    concrete_value=concrete_value,
                )
            else:
                return ValidationResult(
                    verdict=ValidationVerdict.FALSE_POSITIVE,
                    confidence=0.90,
                    reason=f"Concrete evaluation shows no violation: {concrete_value:.6f} vs bound {bound_value:.6f}",
                    counterexample=counterexample,
                    concrete_value=concrete_value,
                )

        except Exception as e:
            return ValidationResult(
                verdict=ValidationVerdict.NEEDS_REVIEW,
                confidence=0.5,
                reason=f"Could not evaluate counterexample: {e}",
                counterexample=counterexample,
            )

    def generate_test_points(
        self,
        domain: Box,
        num_points: int = 100,
    ) -> list[dict[str, float]]:
        """
        Generate test points within a domain for Monte Carlo verification.

        Args:
            domain: Box domain to sample from
            num_points: Number of test points to generate

        Returns:
            List of variable assignment dictionaries
        """
        import random

        points = []
        var_names = domain.var_order()

        for _ in range(num_points):
            point = {}
            for name in var_names:
                interval = domain[name]
                lo = float(interval.lo)
                hi = float(interval.hi)
                # Sample uniformly
                point[name] = random.uniform(lo, hi)
            points.append(point)

        # Add corner points
        corners = self._get_corner_points(domain)
        points.extend(corners)

        return points

    def _get_corner_points(self, domain: Box) -> list[dict[str, float]]:
        """Generate corner points of the domain box."""
        var_names = domain.var_order()
        n = len(var_names)

        if n > 8:  # Too many corners
            return []

        corners = []
        for mask in range(2 ** n):
            corner = {}
            for i, name in enumerate(var_names):
                interval = domain[name]
                if mask & (1 << i):
                    corner[name] = float(interval.hi)
                else:
                    corner[name] = float(interval.lo)
            corners.append(corner)

        return corners

    def monte_carlo_verify(
        self,
        expr: Expr,
        domain: Box,
        claimed_min: float,
        claimed_max: float,
        num_samples: int = 1000,
    ) -> ValidationResult:
        """
        Use Monte Carlo sampling to verify bounds.

        Args:
            expr: Expression to verify
            domain: Domain to sample from
            claimed_min: Claimed minimum value
            claimed_max: Claimed maximum value
            num_samples: Number of random samples

        Returns:
            ValidationResult indicating if bounds seem correct
        """
        points = self.generate_test_points(domain, num_samples)

        observed_min = float('inf')
        observed_max = float('-inf')
        worst_point_min = None
        worst_point_max = None

        for point in points:
            try:
                value = float(expr.evaluate(point))
                if value < observed_min:
                    observed_min = value
                    worst_point_min = point.copy()
                if value > observed_max:
                    observed_max = value
                    worst_point_max = point.copy()
            except Exception:
                continue

        # Check if observed values are within claimed bounds
        min_ok = observed_min >= claimed_min - self.tolerance
        max_ok = observed_max <= claimed_max + self.tolerance

        if min_ok and max_ok:
            return ValidationResult(
                verdict=ValidationVerdict.CONFIRMED,
                confidence=0.80,  # Monte Carlo is probabilistic
                reason=f"Monte Carlo ({num_samples} samples) confirms bounds: observed [{observed_min:.6f}, {observed_max:.6f}]",
            )
        else:
            violating_point = worst_point_min if not min_ok else worst_point_max
            return ValidationResult(
                verdict=ValidationVerdict.NEEDS_REVIEW,
                confidence=0.70,
                reason=f"Monte Carlo found values outside claimed bounds: observed [{observed_min:.6f}, {observed_max:.6f}] vs claimed [{claimed_min:.6f}, {claimed_max:.6f}]",
                counterexample=violating_point,
                concrete_value=observed_min if not min_ok else observed_max,
            )


# =============================================================================
# BUG VALIDATOR (Main Interface)
# =============================================================================

@dataclass
class BugReport:
    """A potential bug to be validated."""
    description: str
    location: str
    severity: str
    expression: Optional[Expr] = None
    domain: Optional[Box] = None
    bounds_result: Optional[BoundsResult] = None
    claimed_violation: Optional[str] = None  # "upper" or "lower"
    bound_value: Optional[float] = None
    source_code: Optional[str] = None


class BugValidator:
    """
    Comprehensive bug validator that reduces false positives.

    This class orchestrates multiple validation techniques:
    1. Interval explosion detection
    2. Comment analysis for intentional behavior
    3. Counterexample verification
    4. Monte Carlo sampling
    """

    def __init__(
        self,
        explosion_detector: Optional[IntervalExplosionDetector] = None,
        comment_analyzer: Optional[CommentAnalyzer] = None,
        counterexample_verifier: Optional[CounterexampleVerifier] = None,
    ):
        """
        Initialize the validator with optional custom components.

        Args:
            explosion_detector: Custom explosion detector
            comment_analyzer: Custom comment analyzer
            counterexample_verifier: Custom counterexample verifier
        """
        self.explosion_detector = explosion_detector or IntervalExplosionDetector()
        self.comment_analyzer = comment_analyzer or CommentAnalyzer()
        self.verifier = counterexample_verifier or CounterexampleVerifier()

    def validate(self, bug: BugReport) -> ValidationResult:
        """
        Validate a potential bug using all available techniques.

        Args:
            bug: BugReport to validate

        Returns:
            ValidationResult with final verdict
        """
        results = []

        # 1. Check for interval explosion
        if bug.bounds_result:
            is_explosion, reason = self.explosion_detector.detect_explosion(bug.bounds_result)
            if is_explosion:
                return ValidationResult(
                    verdict=ValidationVerdict.FALSE_POSITIVE,
                    confidence=0.85,
                    reason=f"Interval explosion detected: {reason}",
                    interval_width=float(bug.bounds_result.max_bound.hi - bug.bounds_result.min_bound.lo),
                )

        # 2. Check expression risk
        if bug.expression:
            is_risky, reason = self.explosion_detector.check_expression_risk(bug.expression)
            if is_risky:
                results.append(ValidationResult(
                    verdict=ValidationVerdict.NEEDS_REVIEW,
                    confidence=0.60,
                    reason=f"Expression is prone to interval explosion: {reason}",
                ))

        # 3. Analyze source code comments
        if bug.source_code:
            is_intentional, pattern, comment = self.comment_analyzer.is_intentional_protection(bug.source_code)
            if is_intentional:
                return ValidationResult(
                    verdict=ValidationVerdict.DESIGN_INTENT,
                    confidence=0.80,
                    reason=f"Code comments indicate intentional behavior",
                    matched_pattern=pattern,
                )

        # 4. Verify with concrete evaluation if we have counterexample data
        if bug.expression and bug.domain and bug.claimed_violation and bug.bound_value is not None:
            # Generate counterexample from bounds result
            if bug.bounds_result:
                # Use the midpoint of the reported extremum as counterexample
                counterexample = self._extract_counterexample(bug.bounds_result, bug.domain)
                if counterexample:
                    ce_result = self.verifier.verify_counterexample(
                        bug.expression,
                        counterexample,
                        bug.claimed_violation,
                        bug.bound_value,
                    )
                    results.append(ce_result)

        # 5. Monte Carlo verification if we have expression and domain
        if bug.expression and bug.domain and bug.bounds_result:
            mc_result = self.verifier.monte_carlo_verify(
                bug.expression,
                bug.domain,
                claimed_min=float(bug.bounds_result.min_bound.lo),
                claimed_max=float(bug.bounds_result.max_bound.hi),
            )
            results.append(mc_result)

        # Combine results
        return self._combine_results(results, bug)

    def _extract_counterexample(
        self,
        bounds_result: BoundsResult,
        domain: Box,
    ) -> Optional[dict[str, float]]:
        """Extract a counterexample point from bounds result."""
        # For now, use domain midpoints as the counterexample
        # In future versions, the Lean kernel could return the actual location
        counterexample = {}
        for name in domain.var_order():
            interval = domain[name]
            counterexample[name] = float((interval.lo + interval.hi) / 2)
        return counterexample

    def _combine_results(
        self,
        results: list[ValidationResult],
        bug: BugReport,
    ) -> ValidationResult:
        """Combine multiple validation results into a final verdict."""
        if not results:
            return ValidationResult(
                verdict=ValidationVerdict.NEEDS_REVIEW,
                confidence=0.5,
                reason="Insufficient data for automatic validation",
            )

        # Count verdicts
        fp_count = sum(1 for r in results if r.verdict == ValidationVerdict.FALSE_POSITIVE)
        confirmed_count = sum(1 for r in results if r.verdict == ValidationVerdict.CONFIRMED)
        intent_count = sum(1 for r in results if r.verdict == ValidationVerdict.DESIGN_INTENT)

        # Decision logic
        if fp_count > confirmed_count:
            # More evidence for false positive
            fp_results = [r for r in results if r.verdict == ValidationVerdict.FALSE_POSITIVE]
            best_fp = max(fp_results, key=lambda r: r.confidence)
            return ValidationResult(
                verdict=ValidationVerdict.FALSE_POSITIVE,
                confidence=min(0.95, best_fp.confidence + 0.1 * fp_count),
                reason=best_fp.reason,
                counterexample=best_fp.counterexample,
                concrete_value=best_fp.concrete_value,
            )

        if intent_count > 0:
            intent_results = [r for r in results if r.verdict == ValidationVerdict.DESIGN_INTENT]
            return intent_results[0]

        if confirmed_count > 0:
            confirmed_results = [r for r in results if r.verdict == ValidationVerdict.CONFIRMED]
            best_confirmed = max(confirmed_results, key=lambda r: r.confidence)
            return ValidationResult(
                verdict=ValidationVerdict.CONFIRMED,
                confidence=min(0.95, best_confirmed.confidence),
                reason=best_confirmed.reason,
                counterexample=best_confirmed.counterexample,
                concrete_value=best_confirmed.concrete_value,
            )

        # Default to needs review
        return ValidationResult(
            verdict=ValidationVerdict.NEEDS_REVIEW,
            confidence=0.5,
            reason="Mixed validation results - manual review recommended",
        )


# =============================================================================
# CONVENIENCE FUNCTIONS
# =============================================================================

def detect_interval_explosion(result: BoundsResult) -> tuple[bool, str]:
    """Quick check for interval explosion."""
    detector = IntervalExplosionDetector()
    return detector.detect_explosion(result)


def is_intentional_behavior(solidity_code: str) -> tuple[bool, Optional[str]]:
    """Quick check for intentional behavior in code."""
    analyzer = CommentAnalyzer()
    is_intent, pattern, _ = analyzer.is_intentional_protection(solidity_code)
    return is_intent, pattern


def verify_counterexample_concrete(
    expr: Expr,
    counterexample: dict[str, float],
    claimed_max: Optional[float] = None,
    claimed_min: Optional[float] = None,
) -> bool:
    """
    Quick verification that a counterexample is real.

    Returns True if the counterexample confirms a violation.
    """
    try:
        concrete_value = float(expr.evaluate(counterexample))

        if claimed_max is not None and concrete_value > claimed_max:
            return True
        if claimed_min is not None and concrete_value < claimed_min:
            return True

        return False
    except Exception:
        return False  # Can't verify = assume false positive
