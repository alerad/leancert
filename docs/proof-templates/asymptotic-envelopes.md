# Asymptotic Envelopes

Use `AsympEnv` when a summatory function has a main term and nonnegative error
term:

```text
sequence
+ main term
+ nonnegative error term
= reusable summatory envelope
```

Core API:

```lean
AsympEnv
AsympEnv.lower
AsympEnv.upper
AsympEnv.weakenError
AsympEnv.add
AsympEnv.neg
AsympEnv.sub
AsympEnv.constMul
```

The lower and upper endpoint theorems turn the absolute-error certificate into
usable inequalities.

ANT-specific transforms built on `AsympEnv` are documented in
[Domain Libraries → ANT Asymptotic](../domains/ant/asymptotic-ant.md).

Detailed API reference: [Asymptotic Envelope Certificates](../certificates/ant-asymp.md).

Next:

- For real-variable estimates over `x : ℝ`, see
  [Pointwise Envelopes](pointwise-envelopes.md).
- For ANT transforms built from `AsympEnv`, see
  [ANT Asymptotic Transforms](../domains/ant/asymptotic-ant.md).
- For trust status, see
  [Verification Status](../architecture/verification-status.md).
