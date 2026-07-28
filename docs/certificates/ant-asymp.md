# Asymptotic Envelope Certificates

The `LeanCert.ANT.Asymp` layer, also called the Certified Asymptotic Envelope
Engine in design notes, packages summatory functions as main terms plus
nonnegative error terms and provides transform kernels for analytic number
theory workflows.

## Import

```lean
import LeanCert.ANT.Asymp
```

or through the aggregate ANT import:

```lean
import LeanCert.ANT
```

## What An Asymptotic Envelope Certifies

An `AsympEnv` packages a sequence, a cutoff, a main term, and an error term:

```lean
structure AsympEnv where
  seq : Nat → ℝ
  cutoff : Nat
  mainTerm : Expr
  errorTerm : Expr
  cert :
    ∀ N, cutoff ≤ N →
      |prefixSum seq (N + 1) - evalAtNat mainTerm N| ≤ evalAtNat errorTerm N
  error_nonneg :
    ∀ N, cutoff ≤ N → 0 ≤ evalAtNat errorTerm N
```

The certificate means that for every natural endpoint `N ≥ cutoff`,

```text
|sum_{n ≤ N} seq n - mainTerm(N)| ≤ errorTerm(N)
```

The nonnegativity field ensures the error term is a genuine envelope radius.

## Core API

The semantic core lives in `LeanCert.ANT.Asymp.Env`.

| API | Purpose |
|---|---|
| `evalAtNat` | evaluate a univariate `Expr` at a natural endpoint |
| `AsympEnv.summatory` | summatory function `prefixSum seq (N + 1)` |
| `AsympEnv.summatoryReal` | real endpoint form, interpreted by flooring |
| `AsympEnv.lower` | lower endpoint `mainTerm - errorTerm` |
| `AsympEnv.upper` | upper endpoint `mainTerm + errorTerm` |
| `AsympEnv.weakenError` | replace an error term by a pointwise larger one |
| `AsympEnv.shiftCutoff` | raise the cutoff |
| `AsympEnv.add` | add two envelopes |
| `AsympEnv.neg` | negate an envelope |
| `AsympEnv.sub` | subtract envelopes |
| `AsympEnv.constMul` | multiply an envelope by a rational scalar |

The lower and upper endpoint theorems are:

```lean
#check LeanCert.ANT.Asymp.AsympEnv.lower_le_summatory
#check LeanCert.ANT.Asymp.AsympEnv.summatory_le_upper
#check LeanCert.ANT.Asymp.AsympEnv.lowerReal_le_summatoryReal
#check LeanCert.ANT.Asymp.AsympEnv.summatoryReal_le_upperReal
```
## Pointwise Error Envelopes

`PointwiseEnvelope` is the real-variable sibling of `AsympEnv`.  It certifies:

```text
|f x - main x| <= error x
```

on an arbitrary real domain, with a proof that `error` is nonnegative on that
domain.

Core API:

```lean
#check LeanCert.ANT.Asymp.PointwiseEnvelope.lower
#check LeanCert.ANT.Asymp.PointwiseEnvelope.upper
#check LeanCert.ANT.Asymp.PointwiseEnvelope.lower_le_value
#check LeanCert.ANT.Asymp.PointwiseEnvelope.value_le_upper
#check LeanCert.ANT.Asymp.PointwiseEnvelope.weakenError
```
Algebra:

```lean
#check LeanCert.ANT.Asymp.PointwiseEnvelope.add
#check LeanCert.ANT.Asymp.PointwiseEnvelope.neg
#check LeanCert.ANT.Asymp.PointwiseEnvelope.sub
#check LeanCert.ANT.Asymp.PointwiseEnvelope.constMul
```
The algebra keeps the common-domain and nonnegative-error obligations inside
the certificate object.  This is the preferred target for explicit real-variable
estimates that are not naturally discrete summatory functions.

To turn a summatory `AsympEnv` into a real-variable pointwise envelope using the
existing floor semantics, use:

```lean
#check LeanCert.ANT.Asymp.AsympEnv.toPointwiseFloorEnvelope
#check LeanCert.ANT.Asymp.AsympEnv.toPointwiseFloorEnvelope_cert
```
## Stieltjes-Abel Transforms

The Stieltjes-Abel kernel certifies weighted summatory transforms.

```text
weightedPrefixSumReal
abelTransformOfPrefixReal
weightedPrefixSumReal_eq_abelTransformOfPrefixReal
```
The generic payload is:

```text
structure StieltjesCert (A : AsympEnv) where
  weight : Nat → ℝ
  cutoff : Nat
  mainTerm : Expr
  errorTerm : Expr
  cert :
    ∀ N, cutoff ≤ N →
      |weightedPrefixSumReal A.seq weight N - evalAtNat mainTerm N| ≤
        evalAtNat errorTerm N
  error_nonneg :
    ∀ N, cutoff ≤ N → 0 ≤ evalAtNat errorTerm N
```

The common analytic-number-theory weight `1 / n` has a specialized API:

```text
oneOverNWeight
oneOverNExpr
OneOverNStieltjesCert
verify_one_over_n_stieltjes_envelope
```
`OneOverNStieltjesCert` requires `1 ≤ cutoff`, so certified endpoints avoid
treating the `n = 0` convention as part of the analytic statement.

Golden theorem:

```text
verify_stieltjes_envelope
```
## Dirichlet Hyperbola Transforms

The hyperbola layer provides an exact finite pair-sum specification and a
certificate bridge for Dirichlet-convolution-style summatory functions.

```text
hyperbolaPairs
hyperbolaPairSum
hyperbolaLeft
hyperbolaBottom
hyperbolaOverlap
hyperbolaPairSum_eq_left_add_bottom_sub_overlap
```
`hyperbolaPairs` is specification-level, not an execution-level evaluator: it
enumerates an `N × N` rectangle before filtering.

Transform certificates use:

```text
HyperbolaCert
verify_dirichlet_hyperbola_envelope
```
To expose a conventional convolution sequence, provide the finite divisor-pair
identity through:

```text
DirichletConvolutionBridge
verify_dirichlet_convolution_envelope
```
The reusable discrete derivative helper is:

```text
discreteDerivative
prefixSum_discreteDerivative
```
## Dyadic Error-Domination Checkers

Generated transform certificates often produce a detailed error expression that
should be dominated by a simpler target error.  The dyadic checker layer proves
expression domination on intervals, slabs, and slab-plus-tail covers.

Raw computable checkers:

```text
checkExprLeOnIntervalDyadic
checkExprLeOnSlabsDyadic
```
Soundness-facing certificate packages:

```text
ExprLeOnIntervalDyadicCert
ExprLeOnSlabsDyadicCert
```
Coverage structures:

```text
NatSlabCover
SlabTailCert
SlabTailCert.covered_or_tail
```
Verifier bridges:

```text
verify_expr_le_on_interval_dyadic
verify_expr_le_on_slabs_dyadic
verify_expr_le_on_nat_slab_cover_dyadic
verify_expr_le_with_slab_tail_dyadic
verify_stieltjes_error_le_target_with_slab_tail_dyadic
verify_hyperbola_error_le_target_with_slab_tail_dyadic
```
## Slab And Table Inequality Certificates

For explicit PNT estimates and generated numerical tables, the dyadic slab
checker is packaged as a small certificate API:

```text
SlabInequalityCert
SlabInequalityCert.verify
```
`SlabInequalityCert` proves:

```text
∀ I ∈ slabs, ∀ x ∈ Set.Icc (I.lo : ℝ) I.hi,
  Expr.eval (fun _ => x) lhs ≤ Expr.eval (fun _ => x) rhs
```
The table-oriented wrapper uses the generic `TableCert` traversal:

```text
InequalityTableRow
checkInequalityTableRow
InequalityTableCert
InequalityTableCert.verify
InequalityTableCert.failingIndices
```
Rows remain proof-free data.  The table certificate carries the support and
precision side conditions once over row membership, while `native_decide` checks
the row booleans.

## Pattern: Generate, Dominate, Weaken

The usual envelope workflow is:

1. Build or generate a transform certificate.
2. Prove or check that the generated error is bounded by a simpler target error.
3. Use `AsympEnv.weakenError` to expose the simpler target envelope.

For example, a `OneOverNStieltjesCert` can be converted into an envelope, its
generated error can be checked against `Expr.const 1` on a slab-plus-tail cover,
and the resulting envelope can be weakened to the public error term.

## Toy Examples

The repository contains two complete, compiled toy developments:

- `LeanCert/Test/AsympTransforms.lean` constructs the sequence concentrated at
  `1`, its exact `1 / n` weighted-sum certificate, and the weakened envelope.
- `LeanCert/Test/AsympCheckers.lean` constructs a slab-plus-tail certificate
  proving that the generated error `0` is dominated by the public error `1`.

The concrete certificate types used by those examples are checked here:

```lean
#check LeanCert.ANT.Asymp.OneOverNStieltjesCert
#check LeanCert.ANT.Asymp.SlabTailCert
```

Production certificates usually generate the transform payload and slab
coverage mechanically.

## Current Scope

This layer currently includes semantic envelope algebra, pointwise floor
envelopes, Stieltjes-Abel kernels, Dirichlet-hyperbola kernels, dyadic slab/tail
domination checks, pointwise-envelope algebra, and table-oriented slab
inequality certificates. High-level automated asymptotic derivation is not yet
part of this layer.
