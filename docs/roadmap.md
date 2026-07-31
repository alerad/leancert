# Roadmap

LeanCert's current public claims are documented in the
[trust model](architecture/trust-model.md) and
[verification-status table](architecture/verification-status.md). The items
below are convergence work, not features claimed as complete.

## Extensible checked enclosures

**Current state:** downstream modules can register and inspect typed unary
`ℝ → ℝ` enclosure candidates, Boolean checkers, and `sorry`-free soundness
theorems without modifying LeanCert's internal expression datatype. `leancert`
executes imported rules for unary interval bounds whose registered applications
have checked, reifiable inner arguments.

**Milestone:** extend compositional execution through surrounding registered or
built-in operations, then add adaptive subdivision for inconclusive downstream
candidates.

**Evidence:** an external function certified end to end through an imported
rule, with rejected-candidate fallback and complete `leancert?` provenance.

## Checked-backend capability parity

**Current state:** Rational, Dyadic, and Affine backends deliberately have
different supported operations and performance profiles.

**Milestone:** publish a generated capability matrix and close high-value
gaps without hiding backend selection or fallback.

**Evidence:** backend-specific correctness tests and checked public API
examples for each newly supported operation.

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
