# Roadmap

LeanCert's current public claims are documented in the
[trust model](architecture/trust-model.md) and
[verification-status table](architecture/verification-status.md). The items
below are convergence work, not features claimed as complete.

## Extensible checked enclosures

**Current state:** downstream modules can register and inspect typed unary
`ℝ → ℝ` enclosure candidates, Boolean checkers, and `sorry`-free soundness
theorems without modifying LeanCert's internal expression datatype. `leancert`
executes imported rules for unary interval bounds, supports nested registered
applications, and composes their checked results through ordinary core
expressions. Rejected or comparison-inconclusive candidates are retried through
checked rational subdivision with retained leaf provenance.

**Possible next milestone:** extend the protocol beyond enclosure rules only
when downstream use cases establish a concrete need for additional rule kinds.

**Evidence:** an external function certified end to end through an imported
rule, with rejected-candidate fallback and complete `leancert?` provenance.

## Checked-backend capability parity

**Current state:** Rational, Dyadic, and Affine backends deliberately have
different supported operations and performance profiles.

**Milestone:** publish a generated capability matrix and close high-value
gaps without hiding backend selection or fallback.

**Evidence:** backend-specific correctness tests and checked public API
examples for each newly supported operation.

## Quantitative asymptotics

**Current state:** `eventual_bound` checks explicit positive cutoffs and can
discover witnesses for existential natural-number upper bounds on nonnegative
rational multiples of reciprocal powers. Discovery uses bounded exponential
search and binary refinement, then replays the candidate through the same
exact-rational checker. The Golden Theorem proves the infinite tail by
symbolic monotonicity. The `leancert` router recognizes this theorem family,
and reports preserve the cutoff and search provenance.

**Possible next milestone:** grow the typed tail-rule language from
demonstrated downstream needs, starting with compositional domination rules or
carefully scoped logarithmic and exponential tails.

**Evidence:** fixed-cutoff and discovered-cutoff regression theorems, exact and
budget-limited search tests, rejected cutoff tests, semantic-router coverage,
and `eventual_bound?`/`leancert?` provenance.

## Nonlinear-system roots

**Current state:** `system_unique_root` generates rational Krawczyk centers and
preconditioners for square systems in the checked-AD fragment. It uses
singleton point-Jacobian enclosures, pivoted Gauss--Jordan inversion, bounded
interval-Newton refinement, and fixed-precision candidate rounding. The
semantic router invokes it directly for the canonical `∃!` system goal.
`system_unique_root using cert` remains the manual path. Both pass through
`krawczykCheck` and `verify_unique_system_root`; search data is never trusted.

**Possible next milestone:** expose the checked system-root operation through
the bridge and let external numerical frontends supply stronger candidates.
Adaptive box refinement remains separate: it requires existence in one box and
root exclusion over the complement to preserve uniqueness in the original box.

**Evidence:** automatic translated, coupled transcendental, cyclic 3D, generic
4D, and refinement-requiring exponential systems; exact and singular matrix
inversion tests; mutation tests for every checker stage; dimension-limit,
budget, unsupported-AD, conjunction-order, trust-route, and rollback tests.

## Matrix positivity certificates

**Current state:** exact rational Gram and LDLᵀ certificates prove finite real
matrix positive-semidefiniteness and positive-definiteness. Dedicated tactics
and `leancert` share transactional typed outcomes, single-pass candidate
discovery, retained pivot telemetry, and configurable certificate
verification. Finite feature Gram matrices and positive diagonal
regularization have stable structural APIs.

**Possible next milestone:** add independently checked approximate residual
certificates and uniform interval-matrix positivity only after quantitative
perturbation theorems and representative downstream problems establish the
required interface.

**Evidence:** exact PSD, rank-deficient PSD, PD, indefinite rejection,
Gram/kernel, trust-mode, router, public-import, and trust-manifest tests.

## Stronger quantified ML theorems

**Current state:** ML certificate components prove the precise structural and
bound properties stated by their theorems; they are not a blanket
end-to-end model-correctness claim.

**Milestone:** connect more model-level specifications to checked layer and
quantized-inference bounds.

**Evidence:** exported quantified theorems over inputs, with explicit
assumptions and trust-manifest entries.

## Large integration certificates

**Current state:** exact polynomial integration and checked partition
integration are available; large partition certificates can be expensive,
especially under kernel-only checking.

**Milestone:** reduce certificate construction and verification cost while
preserving the same Golden-Theorem boundary and explicit trust selection.

**Evidence:** versioned benchmark baselines with toolchain, machine, revision,
and warm/cold metadata.

## Downstream applications

**Current state:** LeanCert includes ANT, QProduct, certified-table, and ML
infrastructure plus interface tests derived from downstream use.

**Milestone:** expand maintained applications while keeping the stable
numerical API small and domain assumptions explicit.

**Evidence:** downstream interface contracts, compiled application examples,
and published theorem statements rather than source-line counts.
