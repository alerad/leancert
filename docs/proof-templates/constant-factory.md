# Perturbation Observers With ConstantFactory

`LeanCert.ConstantFactory` implements a perturbation-observer proof template.

Use it when many constants are obtained by starting from a fixed base object,
reusing certified kernel moments for that base, and applying finite perturbation
algebra.

The proof pattern is:

```text
base kernel moments
+ finite perturbation expansion
+ exact or interval observer sums
= certified constant for many related products
```

In the current implementation, the base object is a q-product profile.  For a
base set `R` and a disjoint perturbation set `Q`, ConstantFactory proves finite
identities for:

```lean
F (R ∪ Q)
```

by reducing them to certified moments of `R`.

The q-product implementation is the first instance of this template; the
reusable idea is to separate stable base-kernel certification from cheap finite
perturbation verification.

Core APIs:

```lean
observerIntegralRat_eq_F_union
verify_constantFactory_interval
KernelIntervalBank
F_union_mem_observerInterval
```

Taylor-model integral certificates can be used to produce kernel enclosures,
but fully automatic Taylor-backed kernel-bank construction is a future
constructor layer.

Detailed API reference: [ConstantFactory Certificates](../certificates/constants.md).

Next:

- For exact finite product-integral identities, see
  [Exact Product-Integral Certificates](qproduct-finite-integrals.md).
- For prime-indexed limit arguments on top of finite q-products, see
  [QProduct Prime Limits](../domains/qproduct-prime-limits.md).
- For trust status, see
  [Verification Status](../architecture/verification-status.md).
