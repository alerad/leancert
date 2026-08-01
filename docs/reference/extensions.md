# Downstream enclosure extensions

`LeanCert.Tactic.Extension` is the registration boundary for checked enclosure
rules defined outside LeanCert. The initial protocol supports unary real
functions. It lets a downstream package register a candidate generator, a
Boolean checker, and a soundness theorem without extending LeanCert's internal
expression datatype.

The semantic `leancert` front door executes imported rules transactionally for
unary interval bounds. The lightweight `LeanCert.Tactic.Extension` import still
contains only registration and inspection. Import `LeanCert.Tactic.Enclosure`
where only the focused `enclosure_bound` tactic is needed; this avoids loading
the semantic router and unrelated solver families.

## Trust boundary

A rule has three parts:

1. The **candidate generator** proposes an output interval. It is untrusted and
   may return a typed domain obstruction or inconclusive result.
2. The **Boolean checker** validates the proposed interval.
3. The **soundness theorem** turns a successful check into semantic interval
   membership.

Only the theorem establishes the mathematical result. A wrong candidate is
rejected by the checker; it cannot make the registered theorem unsound.

## Registering a unary rule

```lean
import LeanCert.Tactic.Extension
import LeanCert.Tactic.Enclosure

namespace DownstreamExtensionExample

open LeanCert.Core LeanCert.Tactic.Extension

noncomputable def positiveBranch (x : ℝ) : ℝ :=
  if x ≤ 0 then 0 else x

def positiveBranchCandidate (request : UnaryEnclosureRequest) :
    Except EnclosureCandidateFailure IntervalRat :=
  if 0 < request.input.lo then .ok request.input
  else .error <| .domainObstruction "input interval is not strictly positive"

def checkPositiveBranch (request : UnaryEnclosureRequest) (output : IntervalRat) : Bool :=
  decide (0 < request.input.lo) && decide (output = request.input)

@[leancert_enclosure positiveBranchCandidate, priority := 1200]
theorem positiveBranch_mem
    {request : UnaryEnclosureRequest} {x : ℝ} {output : IntervalRat}
    (hx : x ∈ request.input)
    (hcheck : checkPositiveBranch request output = true) :
    positiveBranch x ∈ output := by
  simp only [checkPositiveBranch, Bool.and_eq_true, decide_eq_true_eq] at hcheck
  rcases hcheck with ⟨hpositive, rfl⟩
  have hxpositive : 0 < x := by
    exact lt_of_lt_of_le (by exact_mod_cast hpositive) hx.1
  simpa [positiveBranch, not_le.mpr hxpositive] using hx

example : ∀ x ∈ Set.Icc (0 : ℝ) 1, positiveBranch (x + 1) ≤ 2 := by
  enclosure_bound (trust := kernel)

example : ∀ x ∈ Set.Icc (0 : ℝ) 1,
    Real.exp (positiveBranch (x + 1)) + x < 9 := by
  enclosure_bound? (trust := kernel)

end DownstreamExtensionExample
```

The theorem schema is intentionally exact. The attribute validates:

- a candidate of type `UnaryEnclosureCandidate`;
- a checker of type `UnaryEnclosureChecker`;
- a declared function of type `ℝ → ℝ`;
- the input hypothesis `x ∈ request.input`;
- the checker hypothesis `checker request output = true`;
- the conclusion `f x ∈ output`;
- that the soundness declaration is a proved, `sorry`-free theorem.

Malformed rules fail where the attribute is declared, rather than later during
tactic execution. Rules for the same function are ordered by descending
priority and then deterministically by theorem name.

Candidate failures also participate in routing. Return `.inconclusive` when a
particular rule cannot construct a useful enclosure and a lower-priority rule
may still succeed. Reserve `.domainObstruction` for a genuine mathematical
precondition failure: it is terminal and prevents LeanCert from masking an
invalid domain by continuing with another strategy. Candidate exceptions and
verification-infrastructure failures are terminal internal errors.

## Inspecting the registry

Use the command without an argument to list every imported rule, or provide a
function to filter the output:

```lean
import LeanCert.Tactic.Extension

#print_leancert_rules
```

```text
Registered LeanCert enclosure rules:
DownstreamExtensionExample.positiveBranch
  theorem: DownstreamExtensionExample.positiveBranch_mem
  checker: DownstreamExtensionExample.checkPositiveBranch
  candidate: DownstreamExtensionExample.positiveBranchCandidate
  priority: 1200
  kind: unary ℝ → ℝ enclosure
```

Metaprogramming clients may query `getUnaryEnclosureRules` for one function or
`getAllUnaryEnclosureRules` for the complete deterministic registry.

## Current scope

The first protocol deliberately covers unary `ℝ → ℝ` enclosure rules in
univariate interval bounds with rational endpoints and a rational constant on
the other side of the comparison. Registered applications may be nested.
LeanCert treats their checked results as proof-carrying atoms and reifies the
surrounding expression against those atoms, so ordinary supported arithmetic
and transcendental operations may appear outside registered calls. The
quantified variable may also occur independently elsewhere in that expression.

When a registered candidate is rejected, or when its checked enclosure is too
coarse to prove the final comparison, `enclosure_bound` (and the `leancert`
router strategy it exposes) bisects the rational input
interval and retries up to the configured `(subdivisions := n)` depth. Every
retained leaf closes its own registered checker, and the resulting complete
child theorems are combined by a generic interval-cover theorem.
`enclosure_bound?`
reports the configured and deepest depths, boxes examined, certified leaves,
certificate count, composition steps, and verification route. Use `leancert?`
for the larger semantic-router report. Domain obstructions and unsupported
operations remain terminal rather than being reclassified as numerical
imprecision.

Operations outside LeanCert's core expression fragment are not yet covered.
