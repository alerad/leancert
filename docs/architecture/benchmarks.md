# Benchmark harness

LeanCert includes a small compiled benchmark runner for comparing evaluator
performance without mixing timing code into correctness tests:

```sh
lake build leancert-bench
lake exe leancert-bench
```

The default `smoke` suite exercises representative workloads from:

- arithmetic denominator growth;
- nested transcendental evaluation;
- checked Rational and Dyadic automatic differentiation;
- affine dependency tracking.

Each workload contains internal evaluator cases and checked public-API cases.
This separates backend kernel cost from validation and dispatch overhead while
retaining the same expression and input box.

The larger suites are split by purpose:

- `heavy` retains the explicit backend matrix at moderately larger sizes;
- `scaling` follows selected public Auto workloads to sizes that expose growth
  trends without spending time on deliberately unsuitable backends;
- `full` combines evaluator, heavy, and scaling cases but excludes seconds-scale
  algorithms;
- `end-to-end` measures checked Li₂-style partitioned integration from 100 to
  2300 cells and complete nonlinear-system root checks;
- `krawczyk` isolates interval-Jacobian construction, rational matrix/norm
  assembly, and the complete checked certificate path;
- `all` includes every suite, including the seconds-scale integration cases.

## Commands

```sh
# List the quick cases
lake exe leancert-bench --list

# Run the complete evaluator/backend matrix
lake exe leancert-bench --suite evaluation

# Compare checked Rational and Dyadic AD, including denominator growth
lake exe leancert-bench --suite ad --samples 15 --warmups 3

# Run the moderately larger explicit-backend matrix
lake exe leancert-bench --suite heavy

# Run curated public-Auto scaling families
lake exe leancert-bench --suite scaling

# Run evaluator matrices and scaling families (no seconds-scale algorithms)
lake exe leancert-bench --suite full

# Run Li₂-style checked partition integration (recommended sample count)
lake exe leancert-bench \
  --suite end-to-end --samples 3 --warmups 1

# Profile nonlinear-system certification phases
lake exe leancert-bench --suite krawczyk --samples 15 --warmups 3

# Run absolutely everything
lake exe leancert-bench --suite all

# Select one family of cases
lake exe leancert-bench --suite evaluation --case nested_sin

# Emit raw samples for later analysis
lake exe leancert-bench \
  --suite evaluation --samples 15 --warmups 3 --format jsonl \
  > benchmark-results.jsonl

# Run evaluator and scaling suites and write a readable Markdown report
lake exe leancert-bench \
  --suite full --samples 15 --warmups 3 --format markdown \
  > benchmark-results.md

# Write a separate report for seconds-scale checked algorithms
lake exe leancert-bench \
  --suite end-to-end --samples 3 --warmups 1 --format markdown \
  > benchmark-end-to-end.md
```

Human and Markdown modes report the median, median absolute deviation, p10,
and p90. Markdown mode also includes the result status, selected backend, and
enclosure width in a table suitable for a pull request or benchmark artifact.
The table also reports benchmark tier plus expression AST size and depth so
scaling points are explicit. Long exact rational widths are summarized with
their approximate binary scale and endpoint bit sizes, while the JSONL output
retains the exact value.
Timing is normalized per benchmark action. JSONL mode retains every sample
together with:

- exact rational endpoints and width;
- endpoint numerator and denominator bit lengths;
- AST node count, depth, and variable arity;
- requested and selected backend;
- benchmark parameters and inner iteration count.

The `end-to-end` tier measures the checked computational algorithm underlying
the expensive Li₂ theorem, not compilation of the theorem itself. The harness
does not yet claim to measure tactic elaboration, kernel checking, peak memory,
adaptive algorithm counters, or full theorem build time. Use
`time lake build Li2Verified` when the complete elaboration and checking path is
the quantity of interest. Existing legacy benchmark roots remain available
while their useful workloads are migrated.
