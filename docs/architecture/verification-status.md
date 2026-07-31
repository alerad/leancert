# Verification Status

LeanCert's production path is built around checked computations and theorems
that lift successful checks to mathematical propositions. The table below
states the actual boundary for each major subsystem. A successful checker is
verified; search and certificate generation may still fail or be inconclusive.

One compatibility exception is important: the lightweight imported Li₂ aliases
use two explicitly allowlisted placeholders. Their matching proofs are built in
a separate CI target, but the aliases are not kernel-linked to those proof
constants. See the final row for the exact qualification.

## Production Verification Status

| Component | Checked entry point | Correctness bridge | Qualification |
|---|---|---|---|
| Backend-independent interval evaluation | `LeanCert.evalInterval` | `LeanCert.evalInterval_correct` in `API/Eval.lean` | Returns structured `EvalError`; missing list coordinates are fixed to zero. |
| Rational interval evaluation | `LeanCert.Backend.Rational.eval` | `LeanCert.Backend.Rational.eval_correct` in `API/Backend.lean` | The shared dispatcher requires the fixed Rational Taylor depth. |
| Dyadic interval evaluation | `LeanCert.Backend.Dyadic.eval` | `LeanCert.Backend.Dyadic.eval_correct` in `API/Backend.lean` | Requires a nonpositive rounding exponent. |
| Affine interval evaluation | `LeanCert.Backend.Affine.eval` | `LeanCert.Backend.Affine.eval_correct` in `API/Backend.lean` | Preserves correlation where implemented; some operations conservatively fall back to interval enclosures. |
| Automatic differentiation | `evalDualChecked`, `derivIntervalChecked`, `Optimization.gradientIntervalChecked` | `evalDualChecked_val_correct`, `derivIntervalChecked_correct`, `gradientIntervalChecked_correct` | Domain and unsupported-operation failures are returned rather than accepted as enclosures. |
| Global optimization | `LeanCert.globalMinimize`, `LeanCert.globalMaximize` | `LeanCert.globalMinimize_correct`, `LeanCert.globalMaximize_correct` in `API/Optimization.lean` | Proves a global lower or upper bound, not attainment or that `bestBox` contains an optimizer. |
| Root existence | `RootFinding.checkSignChange` | `RootFinding.verify_sign_change` in `Validity/Bounds.lean` | The theorem also uses the stated continuity hypotheses. |
| Root uniqueness | `RootFinding.checkNewtonContractsCore` | `RootFinding.verify_unique_root_computable` in `Validity/Bounds.lean` | Uses checked contraction data and the theorem's support/continuity hypotheses. |
| Root exclusion | `RootFinding.checkNoRoot` | `RootFinding.verify_no_root` in `Validity/Bounds.lean` | A true nonvanishing certificate proves no root on the interval. |
| Recursive interval subdivision | fixed `checkUpperBound`, `checkLowerBound`, `checkStrictUpperBound`, or `checkStrictLowerBound` leaf certificates | matching `verify_*_Icc_core` theorems in `Validity/Bounds` | Candidate enclosures guide subdivision; each retained leaf is independently certified once through the shared verification boundary. Exhaustion, rejection, domain obstruction, and transport failure remain distinct typed outcomes. |
| Exact polynomial integration | `QPoly.checkExactIntegral` | `QPoly.integral_eq_of_check` in `Engine/Algebra/QPolyIntegral.lean` | Exact for supported rational polynomials. |
| Router partition integration | fixed-candidate `checkIntegralPartitionUpperBound`, `checkIntegralPartitionLowerBound` | `integral_partition_upper_of_check`, `integral_partition_lower_of_check` in `Validity/Integration.lean` | Untrusted exponential search runs once and retains its chosen partition count and enclosure. Only that fixed candidate is closed through the shared configurable verification route. |
| Dyadic-list partition integration | `checkIntegralBoundsDyadicList` | `integral_bounds_of_check_dyadic_list` in `Validity/IntegrationDyadic.lean` | Separate lower-level checker validating domains and complete partition coverage. |
| Finite sums | checked `checkFinSum*` and `checkWitnessSum*` functions | matching `verify_finsum_*_checked` and `verify_witness_sum_*` theorems | Candidate evaluation distinguishes domain obstruction from an insufficient enclosure. The retained combined certificate is closed once, transactionally, through the shared verification boundary. |
| Generic tables | `TableCert.checkAll` | `TableCert.verify` in `Engine/Table.lean` | Generated rows remain untrusted until every row check succeeds. |
| ANT and QProduct templates | certificate structures and exact observers | nearby `verify_*` and consequence theorems | Projects must supply the analytic estimates and convergence/envelope hypotheses required by each template. |
| Dense and elementwise neural-network bounds | interval forward functions | `Layer.mem_forwardInterval`, `TwoLayerNet.mem_forwardInterval`, and activation membership theorems | Soundness requires the dimension, input-membership, and precision premises in each theorem. |
| Transformer attention | `scaledDotProductAttention` | `mem_scaledDotProductAttention` in `ML/Attention.lean` | Currently proves an output-length relation, not elementwise semantic enclosure. |
| Quantized inference | `QuantizedLayer.forwardQuantized` | `QuantizedLayer.forwardQuantized_sound` | Currently proves lower endpoints do not exceed upper endpoints; it is not a real-forward containment theorem. |
| Lightweight Li₂ interface | `LeanCert.CertifiedBounds.Li2.lower`, `.upper` | matching `Li2Verified.li2_lower_verified`, `.li2_upper_verified` in the separate `Li2Verified` target | The imported aliases intentionally use two allowlisted placeholders. CI builds the matching proofs and checks statement identity, but this is not a kernel link between the aliases and those proof terms. |

Backend selection and certificate verification are independent. Rational,
Dyadic, and Affine are numerical backends. `kernel`, `native`, and `auto`
choose how an executable certificate is discharged.

## Proof Template Verification Status

Proof templates organize reusable certificate structure. Some have executable
checkers; others expose mathematical obligations that a project must supply.

| Template | Verified part | Project-supplied boundary |
|---|---|---|
| `TableCert` | Generic traversal and row-soundness lifting | A sound checker for each row's semantic claim |
| `AsympEnv` | Lower/upper envelope consequences and algebra | The certificate proof for the summatory estimate |
| `PointwiseEnvelope` | Pointwise lower/upper consequences and algebra | The pointwise error proof on the domain |
| Exact product-integral certificates | Exact rational finite checkers and soundness theorems | The finite certificate data |
| ConstantFactory exact observers | Finite observer identity for disjoint base/perturbation data | Disjointness and observer-checker obligations |
| ConstantFactory interval banks | Observer theorem from kernel-bank correctness | Exact or analytic proofs of kernel interval correctness |
| `ContourShiftCert` | Orientation and limit algebra for stable finite residue data | Rectangle identities, residue values, decay, and convergence |

## Trust and placeholder audit

The repository's audit tests pin the expected axiom sets of representative
public theorems and sweep the environment for locally introduced axioms.
Textual guards reject unallowlisted `sorry` and `axiom` declarations. The two
Li₂ compatibility placeholders are deliberately named in that allowlist; they
must not be described as kernel-checked aliases.

For a theorem in a downstream project, inspect its actual dependency set:

```lean
import LeanCert.Tactic

theorem verification_status_log2 : Real.log 2 < 7 / 10 := by
  leancert (trust := kernel)

#print axioms verification_status_log2
```

`native` certificate verification additionally trusts Lean's native compiler
path. `kernel` does not silently fall back. `auto` may select native execution
according to its configured cost policy and reports that decision through the
verification diagnostics.
