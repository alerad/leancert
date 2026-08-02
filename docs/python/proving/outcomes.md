# Typed Outcomes

LeanCert does not encode every mathematical non-success as `False`. The result
type tells you exactly what was established.

| Outcome | Meaning |
|---|---|
| `Verified` | Every requested bound was accepted by the checked route |
| `Rejected` | A rigorously checked point enclosure violates the requested bound |
| `Inconclusive` | Available enclosures did not decide the claim |
| `DomainObstruction` | The checked evaluator could not establish domain validity |
| `Unsupported` | No negotiated checked route supports the expression or claim shape |
| `VerifiedSystemRoot` | Exact Krawczyk evidence proves one unique system root in the box |
| `CandidateRejected` | An untrusted Krawczyk candidate failed; the mathematical claim remains open |
| `VerifiedEventualBound` | A fixed cutoff certificate proves the complete tail |
| `InconclusiveEventualBound` | The checked route did not close the supplied/discovered cutoff |

## Pattern-match the outcome

```python
import leancert as lc

match result:
    case lc.Verified():
        print("proved", result.claim_id)
    case lc.Rejected(counterexample=counterexample):
        print("disproved at", counterexample.values)
    case lc.Inconclusive(reason=reason):
        print("claim remains open:", reason)
    case lc.DomainObstruction(reason=reason):
        print("domain issue:", reason)
    case lc.Unsupported(reason=reason):
        print("unsupported:", reason)
```

## Truthiness is not the primary API

Some compatibility objects implement Boolean conversion. New code should use
`isinstance` or structural matching so that an unsupported operation is never
confused with a refuted proposition.

## Candidate rejection is not refutation

Search algorithms propose boxes, points, cutoffs, or preconditioners. Rejecting
one proposal says only that this proposal did not certify the claim. A genuine
`Rejected` bound contains a checked counterexample enclosure.
