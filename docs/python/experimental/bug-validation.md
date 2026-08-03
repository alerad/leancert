# Bug-Report Triage

LeanCert includes utilities for ranking suspected numerical bugs: interval
explosion detection, concrete-point evaluation, Monte Carlo sampling, and
comment-pattern analysis.

!!! danger "Diagnostic only"
    **Stability:** Experimental · **Authority:** Heuristic · **Proof value:**
    None unless a separate checked operation returns mathematical evidence

```python
import leancert as lc

source = """
function quote(uint amount) internal pure returns (uint) {
    // Floor division is intentional for slippage protection.
    return amount / 100;
}
"""

intentional, pattern, comment = (
    lc.CommentAnalyzer().is_intentional_protection(source)
)
print(intentional, pattern, comment)
```

This can route a report to a human reviewer, but comment prose cannot prove
that code is safe or that an observed violation is intentional.

For combined triage, construct a `BugReport` with the alleged expression,
domain, claimed violation, optional bound result, and optional source text,
then call `BugValidator.validate()`.

Interpret conservatively:

- Monte Carlo success never establishes a universal claim;
- a midpoint sample can miss a nearby counterexample;
- failure to reproduce is not proof of absence;
- a `FALSE_POSITIVE` diagnostic verdict is not a Lean theorem; and
- only a rigorously enclosed violating point justifies mathematical rejection.

This page is intentionally outside the primary proving tutorial. It serves
auditors and research tooling without blurring heuristic triage with the
checked Bridge boundary.
