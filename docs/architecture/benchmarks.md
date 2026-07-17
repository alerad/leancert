# Benchmark harness

LeanCert includes a small compiled benchmark runner for comparing evaluator
performance without mixing timing code into correctness tests:

```sh
lake build leancert-bench
lake exe leancert-bench
```

The default `smoke` suite exercises three representative workloads:

- arithmetic denominator growth;
- nested transcendental evaluation;
- affine dependency tracking.

Each workload contains internal evaluator cases and checked public-API cases.
This separates backend kernel cost from validation and dispatch overhead while
retaining the same expression and input box.

## Commands

```sh
# List the quick cases
lake exe leancert-bench --list

# Run the complete evaluator/backend matrix
lake exe leancert-bench --suite evaluation

# Select one family of cases
lake exe leancert-bench --suite evaluation --case nested_sin

# Emit raw samples for later analysis
lake exe leancert-bench \
  --suite evaluation --samples 15 --warmups 3 --format jsonl \
  > benchmark-results.jsonl
```

Human mode reports the median, median absolute deviation, p10, and p90. Timing
is normalized per evaluator call. JSONL mode retains every sample together
with:

- exact rational endpoints and width;
- endpoint numerator and denominator bit lengths;
- AST node count, depth, and variable arity;
- requested and selected backend;
- benchmark parameters and inner iteration count.

The harness currently measures compiled interval evaluation only. It does not
yet claim to measure tactic elaboration, kernel checking, peak memory, adaptive
algorithm counters, or end-to-end theorem build time. Existing legacy
benchmark roots remain available while their useful workloads are migrated.
