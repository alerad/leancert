# Experimental Search and Synthesis

These APIs are valuable research tools, but they mix checked numerical
subroutines with untrusted candidate generation and generated proof text. Use
the [capability matrix](capabilities.md) to avoid treating every successful
search result as a replayable theorem.

## Quantifier and witness synthesis

The SDK can search for:

- a bound witnessing an `exists-forall` pattern;
- minimum, maximum, and scalar-root candidates;
- thresholds for selected epsilon values;
- epsilon/delta candidates using derivative enclosures; and
- sign certificates over boxes.

Some final numerical subclaims are checked by Bridge operations. Generated
Lean strings are not automatically authoritative unless separately compiled
against the intended theorem. In particular, finding thresholds for a finite
list of epsilon values is not a proof of a universally quantified statement
over every positive epsilon.

## Counterexample discovery

Adaptive bound checking can ask a global optimizer for a candidate point,
refine it locally, and then submit a point box to the checked bound operation.
Only a rigorously enclosed violation becomes `Rejected`. A plausible point
that does not check remains candidate information.

## Bug-triage utilities

`IntervalExplosionDetector`, `CounterexampleVerifier`, `CommentAnalyzer`, and
`BugValidator` can help rank reports, evaluate concrete points, sample a
domain, and recognize Solidity comments suggesting intentional protections.

These are diagnostics:

- Monte Carlo success never establishes a universal property;
- failure to reproduce a violation never proves a report false;
- comment text never overrides mathematical evidence; and
- the midpoint currently used by one validator may miss a nearby violation.

Keep diagnostic verdicts separate from LeanCert's typed proof outcomes in user
interfaces and stored reports.

## Proof sketches

Legacy `Certificate.render_proof_sketch()`, adaptive `lean_proof`, and witness
`to_lean_tactic()` methods produce human-readable starting points. They are not
the same artifact as `Verified.export_lean_project()` and should not be
advertised as independently checked until a Lean build accepts them.
