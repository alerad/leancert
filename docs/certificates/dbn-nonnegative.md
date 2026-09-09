# Newman nonnegativity: `0 ≤ Lambda`

The unconditional lower bound for the repository's **existing actual DBN
threshold** is proved in `LeanCert/Analysis/DBN/DobnerLimit.lean`:

```lean
import LeanCert.Analysis.DBN.DobnerLimit

open LeanCert.Analysis.DBN

example : 0 ≤ Lambda := Lambda_nonneg
example : Lambda ∈ Set.Icc (0 : ℝ) (1/2) :=
  ⟨Lambda_nonneg, Lambda_le_half⟩

example {t : ℝ} (ht : t < 0) : ∃ z : ℂ, H t z = 0 ∧ z.im ≠ 0 :=
  nonreal_zero_of_lt_Lambda (lt_of_lt_of_le ht Lambda_nonneg)
```

`Lambda` is still `sInf realZeroTimes` from `DBN/Threshold.lean`; neither the
heat integral `H` nor the threshold was replaced by a surrogate definition.
The final theorem has **no approximation, envelope, or certificate premise**.
Its axiom dependencies are only `propext`, `Classical.choice`, and `Quot.sound`.
There is no `sorry`, custom analytic axiom, or native-evaluation trust in this
proof chain.

This proves Newman's side, `Lambda ≥ 0`. It does **not** establish the
additional RH-side bound `Lambda ≤ 0`, nor claim `Lambda = 0`.

## The analytic gap that was closed

For fixed damping `a>0` and strip width `M≥0`, set `L=log(k+1)` and use the
positive contour `Re(z)=max(2,Re(s)+2aL)`. Center its imaginary coordinate at
`Im(s)`. The actual normalized kernel has the joint bound

```text
|K(s,L,v)| ≤ C exp(-aL²/4) exp(-v²/(32a)),
```

for one `C>0` and one height threshold, simultaneously for every `L≥0`,
every real `v`, and every `s` in the strip above that threshold. This is
`centeredKernel_joint_majorant`, not an assumed certificate field.

Its proof combines:

- The previously proved relative Gamma/xi-Gamma estimates with Gaussian
  absorption on the local region.
- A new elementary real Gamma growth bound, derived using factorials and
  the tangent inequality for the real logarithm, without complex Stirling.
- A coarse global kernel bound whose positive growth is only linear in
  height; the remote-contour or large-index quadratic decay absorbs it.
- Exact cancellation before estimating the logarithmic normalization.

See [the linear-cutoff derivation](dbn-linear-cutoff-completion.md) for the
inequalities and constants.

## Limit assembly

`upperStripFilter M` encodes increasing imaginary height while retaining
`|Re(s)|≤M`. It makes the uniform quantifiers explicit without taking a
potentially troublesome supremum inside an integral.

1. Prove convergence of each fixed-index **residual kernel**, using the
   relative Gamma theorem. The individual kernels may still oscillate.
2. Use the joint majorant and dominated convergence for the contour integral.
3. Evaluate the comparison Gaussian exactly.
4. Integrate the index majorant, convert it to the existing telescoping
   Dirichlet envelope, and apply dominated convergence to the infinite sum.
5. Convert strip-filter convergence to locally uniform convergence on upward
   translates of every compact set.

Thus the concrete approximation is now a theorem:

```lean
import LeanCert.Analysis.DBN.DobnerLimit

open LeanCert.Analysis.DBN

example {a : ℝ} (ha : 0 < a) : NormalizedHeatApproximation a :=
  normalizedHeatApproximation ha
```

The existing recurrence, zero-transfer, and threshold connector then proves
`Lambda_nonneg`.

## Files and checks

- `DBN/DobnerLinearBounds.lean`: Gamma growth, linear-normalized ratio bounds.
- `DBN/DobnerCenteredKernel.lean`: exact centered kernel and joint majorant.
- `DBN/DobnerLimit.lean`: integral/series limits and the unconditional theorem.
- `LeanCert/Test/DBNNonnegative.lean`: direct endpoint and intermediate regression tests.
- `Tests/TrustManifest.lean`, `Tests/AxiomAudit.lean`: kernel-trust and axiom pins.

```sh
lean-runtime build --no-cache LeanCert LeanCert.Test.DBNNonnegative
lean-runtime check --using . Tests/TrustManifest.lean
lean-runtime check --using . Tests/AxiomAudit.lean
python3 scripts/check_test_wiring.py
```
