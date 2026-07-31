# Downstream enclosure extensions

`LeanCert.Tactic.Extension` is the registration boundary for checked enclosure
rules defined outside LeanCert. The initial protocol supports unary real
functions. It lets a downstream package register a candidate generator, a
Boolean checker, and a soundness theorem without extending LeanCert's internal
expression datatype.

Registration and inspection are available now. Automatic execution of these
rules by `leancert` is a separate follow-up layer; registering a rule does not
yet change tactic routing.

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

namespace DownstreamExtensionExample

open LeanCert.Core LeanCert.Tactic.Extension

def shifted (x : ℝ) : ℝ := x + 1

def shiftedCandidate (request : UnaryEnclosureRequest) :
    Except EnclosureCandidateFailure IntervalRat :=
  .ok <| IntervalRat.add request.input (IntervalRat.singleton 1)

def checkShifted (request : UnaryEnclosureRequest) (output : IntervalRat) : Bool :=
  decide (output = IntervalRat.add request.input (IntervalRat.singleton 1))

@[leancert_enclosure candidate := shiftedCandidate, priority := 1200]
theorem shifted_mem
    {request : UnaryEnclosureRequest} {x : ℝ} {output : IntervalRat}
    (hx : x ∈ request.input)
    (hcheck : checkShifted request output = true) :
    shifted x ∈ output := by
  have hout : output = IntervalRat.add request.input (IntervalRat.singleton 1) :=
    of_decide_eq_true hcheck
  rw [hout]
  simpa [shifted] using IntervalRat.mem_add hx (IntervalRat.mem_singleton 1)

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

## Inspecting the registry

Use the command without an argument to list every imported rule, or provide a
function to filter the output:

```lean
import LeanCert.Tactic.Extension

#print_leancert_rules
```

```text
Registered LeanCert enclosure rules:
DownstreamExtensionExample.shifted
  theorem: DownstreamExtensionExample.shifted_mem
  checker: DownstreamExtensionExample.checkShifted
  candidate: DownstreamExtensionExample.shiftedCandidate
  priority: 1200
  kind: unary ℝ → ℝ enclosure
```

Metaprogramming clients may query `getUnaryEnclosureRules` for one function or
`getAllUnaryEnclosureRules` for the complete deterministic registry.

## Current scope

The first protocol deliberately covers only unary `ℝ → ℝ` enclosure rules.
Binary operations, derivative rules, monotonicity rules, and automatic
compositional execution are not implied by this interface. They can be added
without changing the meaning of existing unary registrations.
