# Eventual Bounds and Cutoff Discovery

LeanCert can certify a supported inequality over an infinite natural-number
tail and, for existential goals, discover a usable cutoff automatically.

```lean
import LeanCert.Tactic

-- The cutoff is part of the theorem statement.
example : ∀ n : Nat, 100 ≤ n → (1 : ℝ) / n ≤ 1 / 100 := by
  eventual_bound

-- Supply a stable cutoff explicitly.
example : ∃ N : Nat, ∀ n ≥ N, (3 : ℝ) / n ^ 2 ≤ 3 / 100 := by
  eventual_bound using 10

-- Or let the semantic front door discover and certify one.
example : ∃ N : Nat, ∀ n ≥ N, (3 : ℝ) / n ^ 2 ≤ 1 / 1000 := by
  leancert
```

## Supported theorem family

The current certificate language recognizes upper bounds of the form

\[
  \frac{q}{n^k} \le c
\]

over `Nat`, where `q` and `c` are rational constants, `q` is nonnegative, and
`k` and the cutoff are positive natural numbers. Both `N ≤ n` and `n ≥ N`
tail hypotheses are accepted.

This scope is intentionally narrow. General logarithmic or exponential tails,
real-valued tail domains, compositional domination rules, and AD/inversion tail
proofs are not implemented by this tactic yet.

## Why one cutoff proves the infinite tail

The trusted validity boundary consists of:

- `checkReciprocalPowerUpper`, an exact-rational Boolean checker; and
- `verify_reciprocal_power_upper`, the Golden Theorem interpreting an accepted
  check as a theorem for every `n` beyond the cutoff.

The checker establishes the endpoint inequality. The Golden Theorem uses the
symbolic monotonicity of nonnegative reciprocal powers to transport that bound
across the entire infinite tail. No sampled floating-point values are part of
the proof.

## Automatic discovery is untrusted

For an existential goal without `using N`, LeanCert searches for a candidate:

1. exponential search finds a verified upper bracket;
2. bounded binary refinement narrows the bracket; and
3. the selected cutoff is replayed through the exact checker before proof
   construction.

The search algorithm is deliberately outside the trusted mathematical
boundary. A bug in search can make automation fail or return a nonminimal
cutoff, but it cannot prove a false tail statement.

Use `maxIterations` to bound the number of candidate checks:

```lean
import LeanCert.Tactic

example : ∃ N : Nat, ∀ n ≥ N, (3 : ℝ) / n ^ 2 ≤ 1 / 1000 := by
  leancert (maxIterations := 64)
```

If the budget expires after a valid upper bracket has been found, LeanCert may
return that independently verified upper cutoff while reporting that
minimality refinement was incomplete. If no valid bracket was found, the
attempt is inconclusive and leaves the original goal unchanged.

## Inspecting and stabilizing discovery

Use `leancert?` or `eventual_bound?` to see the cutoff, number of checked
candidates, final bracket, refinement status, checker, and verifier:

```lean
import LeanCert.Tactic

example : ∃ N : Nat, ∀ n ≥ N, (3 : ℝ) / n ^ 2 ≤ 1 / 1000 := by
  leancert?
```

The report suggests an explicit proof such as:

```text
by
  eventual_bound using 55
```

That explicit form avoids rerunning discovery and is useful when maintaining a
stable downstream proof.

## Failure meanings

- **Rejected explicit cutoff:** the endpoint inequality is false at the
  supplied `N`; choose a larger cutoff or revise the claim.
- **Search exhausted:** increase `maxIterations` or supply a cutoff with
  `using N`.
- **Unsupported tail:** rewrite the goal into the supported reciprocal-power
  family or prove a more general tail theorem separately.
- **Invalid parameters:** negative coefficients, zero exponents, and
  impossible nonnegative-tail bounds are rejected before proof construction.

For finite-interval inequalities instead, use [`leancert`](leancert.md) or
[`certify_bound`](bounds.md). For main-term/error-term asymptotic certificates,
see [Asymptotic Envelopes](../proof-templates/asymptotic-envelopes.md).
