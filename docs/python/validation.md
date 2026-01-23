# Bug Validation Framework

LeanCert includes a validation framework to filter false positives from counter-example searches.

## The Problem

Static analysis and interval arithmetic can report "violations" that aren't real bugs:

- **Interval explosion**: Wide bounds due to the dependency problem
- **Precision artifacts**: Floating-point rounding in the checker
- **Intentional behavior**: Code that's designed to handle edge cases

The validation framework helps distinguish real bugs from false alarms.

## Quick Example

```python
import leancert as lc
from leancert.validation import BugValidator, BugReport, Box

# Expression that might have issues
x = lc.var('x')
expr = 1 / (x - 1)  # Singularity at x = 1

# Find potential violations
result = lc.find_bounds(expr, {'x': (0.5, 1.5)})

# Create a bug report
bug = BugReport(
    description="Potential division by zero",
    location="math_utils.py:42",
    severity="high",
    expression=expr,
    domain=Box({'x': (0.5, 1.5)}),
    bounds_result=result,
    claimed_violation="unbounded output"
)

# Validate if the issue is real
validator = BugValidator()
result = validator.validate(bug)

print(result)
# ValidationResult(
#   verdict=ValidationVerdict.CONFIRMED,
#   confidence=0.8,
#   reason="Monte Carlo sampling confirms bounds"
# )
```

## Components

### `BugValidator`

Main entry point for validation.

```python
from leancert.validation import BugValidator, BugReport

validator = BugValidator()
result = validator.validate(bug)  # Takes a BugReport object
```

**Constructor parameters:**

```python
validator = BugValidator(
    explosion_detector=None,       # Optional custom IntervalExplosionDetector
    comment_analyzer=None,         # Optional custom CommentAnalyzer
    counterexample_verifier=None   # Optional custom CounterexampleVerifier
)
```

### `IntervalExplosionDetector`

Detects if bounds blew up due to interval arithmetic limitations, not actual unboundedness.

```python
import leancert as lc
from leancert.validation import IntervalExplosionDetector

x = lc.var('x')
detector = IntervalExplosionDetector()

# First compute bounds
result = lc.find_bounds(x * x - x * x, {'x': (-1, 1)})

# Check if wide bounds are due to dependency problem
is_explosion, reason = detector.detect_explosion(result)
print(f"Is explosion: {is_explosion}, Reason: {reason}")
```

You can also use the convenience function:

```python
is_explosion, reason = lc.detect_interval_explosion(result)
```

**Common explosion patterns:**
- `x - x` -> should be 0, interval gives wide bounds
- `x * (1/x)` -> should be 1, interval gives wide bounds
- Correlated variables in LayerNorm

### `CounterexampleVerifier`

Concretely evaluates the expression at reported counter-example points using Monte Carlo sampling.

```python
from leancert.validation import CounterexampleVerifier

verifier = CounterexampleVerifier()

# Monte Carlo verification over the domain
is_confirmed, observed_min, observed_max = verifier.monte_carlo_verify(
    expr=x**2,
    domain={'x': (-2, 2)},
    n_samples=1000
)

# Or verify a specific counterexample point
is_real = verifier.verify_counterexample(
    expr=x**2,
    point={'x': 2.0},
    claimed_value=3.0,
    is_upper=True
)
# Returns True - x²=4 really does exceed 3
```

Convenience function for concrete verification:

```python
is_real = lc.verify_counterexample_concrete(
    expr=x**2,
    counterexample={'x': 2.0},
    claimed_max=3.0
)
```

### `CommentAnalyzer`

Checks code context for indicators that behavior is intentional.

```python
from leancert.validation import CommentAnalyzer

analyzer = CommentAnalyzer()

code_context = """
# NOTE: This can return infinity for x near 0
# This is expected behavior - caller handles it
def f(x):
    return 1/x
"""

is_intentional, pattern = analyzer.is_intentional_protection(code_context)
# Returns (True, "expected behavior") - comment indicates intentional behavior
```

Convenience function:

```python
is_intentional, matched_pattern = lc.is_intentional_behavior(code_context)
```

**Detected patterns:**
- `# expected`, `# intentional`, `# by design`
- `# TODO: handle edge case`
- `# FIXME` (indicates known issue)
- Overflow/underflow protection comments

## ValidationResult

Result of validation:

```python
@dataclass
class ValidationResult:
    verdict: ValidationVerdict      # Enum: CONFIRMED, FALSE_POSITIVE, DESIGN_INTENT, NEEDS_REVIEW
    confidence: float               # 0.0 to 1.0
    reason: str                     # Human-readable explanation
    counterexample: dict | None     # Concrete input triggering issue (if found)
    concrete_value: float | None    # Actual computed value at counterexample
    interval_width: float | None    # Width of the interval bounds
    matched_pattern: str | None     # Pattern matched (for design intent)
```

### `ValidationVerdict` Enum

```python
class ValidationVerdict(Enum):
    CONFIRMED = "confirmed"           # Real bug confirmed
    FALSE_POSITIVE = "false_positive" # Interval explosion or precision artifact
    DESIGN_INTENT = "design_intent"   # Code comments indicate intentional behavior
    NEEDS_REVIEW = "needs_review"     # Uncertain, manual review recommended
```

## Validation Pipeline

The `BugValidator` runs multiple checks:

```
Reported Issue
      |
      v
+------------------+
| Interval         |--> If explosion detected,
| Explosion Check  |    likely false positive
+------------------+
      |
      v
+------------------+
| Counterexample   |--> Concrete evaluation
| Verification     |    confirms or refutes
+------------------+
      |
      v
+------------------+
| Comment          |--> Check for intentional
| Analysis         |    behavior markers
+------------------+
      |
      v
   Verdict
```

## BugReport

Structured bug report for validation:

```python
@dataclass
class BugReport:
    description: str                    # Human-readable description
    location: str                       # File and line (e.g., "utils.py:42")
    severity: str                       # "low", "medium", "high", "critical"
    expression: Expr | None = None      # The expression with potential issue
    domain: Box | None = None           # Input domain
    bounds_result: BoundsResult | None = None  # Result from find_bounds
    claimed_violation: str | None = None       # Type of violation claimed
    bound_value: float | None = None    # The bound that was violated
    source_code: str | None = None      # Source code context for comment analysis
```

## Integration with CI

```python
import leancert as lc
from leancert.validation import BugValidator, BugReport, Box, ValidationVerdict

def check_expression(expr, domain, location):
    """Check an expression for real bugs, filtering false positives."""
    validator = BugValidator()

    # Run interval analysis
    bounds = lc.find_bounds(expr, domain)

    # Create bug report
    bug = BugReport(
        description="Potential bound violation",
        location=location,
        severity="medium",
        expression=expr,
        domain=Box(domain),
        bounds_result=bounds
    )

    # Validate
    result = validator.validate(bug)

    if result.verdict == ValidationVerdict.CONFIRMED and result.confidence > 0.8:
        return bug  # Real bug
    return None

# In CI pipeline
x = lc.var('x')
bug = check_expression(1/x, {'x': (-1, 1)}, "math.py:10")
if bug:
    print(f"Found real bug at {bug.location}")
    sys.exit(1)
```

## Example: Filtering False Positives

```python
import leancert as lc
from leancert.validation import BugValidator, BugReport, Box, ValidationVerdict

x = lc.var('x')

# Case 1: False positive - interval explosion
expr1 = (x + 1) * (x - 1) - (x*x - 1)  # Algebraically 0
result1 = lc.find_bounds(expr1, {'x': (-10, 10)})

bug1 = BugReport(
    description="Large bounds detected",
    location="test.py:10",
    severity="medium",
    expression=expr1,
    domain=Box({'x': (-10, 10)}),
    bounds_result=result1
)

validator = BugValidator()
verdict1 = validator.validate(bug1)
print(f"Case 1: {verdict1.verdict}")  # FALSE_POSITIVE or CONFIRMED with low confidence

# Case 2: Real bug - division by zero possible
expr2 = 1 / x
result2 = lc.find_bounds(expr2, {'x': (-1, 1)})

bug2 = BugReport(
    description="Division may be undefined",
    location="test.py:20",
    severity="high",
    expression=expr2,
    domain=Box({'x': (-1, 1)}),
    bounds_result=result2
)

verdict2 = validator.validate(bug2)
print(f"Case 2: {verdict2.verdict}")  # CONFIRMED (x=0 causes real issue)
```
