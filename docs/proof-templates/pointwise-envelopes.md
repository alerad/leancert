# Pointwise Envelopes

Use `PointwiseEnvelope` for real-variable estimates over `x : ℝ` directly, not
for natural-indexed summatory endpoints.  It is the real-variable sibling of
`AsympEnv`.

```text
function on a domain
+ main approximation
+ nonnegative error radius
= pointwise lower and upper bounds
```

Core API:

```text
PointwiseEnvelope
PointwiseEnvelope.lower
PointwiseEnvelope.upper
PointwiseEnvelope.lower_le_value
PointwiseEnvelope.value_le_upper
PointwiseEnvelope.weakenError
```
The basic theorem shape is:

```lean
#check LeanCert.ANT.Asymp.PointwiseEnvelope.lower_le_value
#check LeanCert.ANT.Asymp.PointwiseEnvelope.value_le_upper
```
If an envelope proves `|f x - main x| ≤ err x` on a domain, these theorems give:

```text
main x - err x ≤ f x
f x ≤ main x + err x
```

Algebra:

```lean
#check LeanCert.ANT.Asymp.PointwiseEnvelope.add
#check LeanCert.ANT.Asymp.PointwiseEnvelope.neg
#check LeanCert.ANT.Asymp.PointwiseEnvelope.sub
#check LeanCert.ANT.Asymp.PointwiseEnvelope.constMul
```
To convert a discrete summatory `AsympEnv` into a real-variable floor envelope:

```lean
#check LeanCert.ANT.Asymp.AsympEnv.toPointwiseFloorEnvelope
```
Detailed API reference: [Asymptotic Envelope Certificates](../certificates/ant-asymp.md).

Next:

- For natural-indexed summatory estimates, see
  [Asymptotic Envelopes](asymptotic-envelopes.md).
- For ANT transforms that consume these envelopes, see
  [ANT Asymptotic Transforms](../domains/ant/asymptotic-ant.md).
- For trust status, see
  [Verification Status](../architecture/verification-status.md).
