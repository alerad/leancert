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
| `VerifiedRootExistence` | A checked sign-change certificate proves a scalar root exists in the interval |
| `VerifiedUniqueRoot` | A checked interval-Newton certificate proves exactly one scalar root exists |
| `VerifiedRootExclusion` | A checked enclosure proves the interval contains no scalar root |
| `ScalarRootCandidateRejected` | The supplied scalar-root interval failed its requested checker; the claim remains open |
| `VerifiedEventualBound` | A fixed cutoff certificate proves the complete tail |
| `InconclusiveEventualBound` | The checked route did not close the supplied/discovered cutoff |
| `VerifiedIntegralEquality` | Exact rational-polynomial integration proves the requested equality |
| `VerifiedIntegralBound` | A fixed checked partition proves the requested one-sided integral bound |
| `IntegralCandidateRejected` | The requested exact or fixed integral candidate failed its checker |
| `InconclusiveIntegral` | Partition discovery exhausted its configured budget without closing the bound |
| `IntegralDomainObstruction` | The integration checker could not establish its domain requirements |
| `UnsupportedIntegral` | The integral shape or integrand is outside the negotiated checked route |

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

The scalar-root and integral candidate-rejection variants follow the same
rule: they report that the supplied fixed candidate did not certify the claim;
they do not manufacture a replay certificate for a different proposition.
