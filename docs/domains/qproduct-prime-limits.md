# QProduct Prime Limits

QProduct prime-limit certificates add limit, monotonicity, sandwich, and tail
arguments on top of finite q-product/product-integral certificates.

Use this page when the statement is not merely a finite product integral, but a
prime-limit or limiting q-product theorem.

Recommended import:

```lean
import LeanCert.QProduct
```

The typical workflow is:

```text
exact finite truncation
+ monotonicity or sandwich theorem
+ explicit tail bound
= directed-limit enclosure
```

LeanCert provides the generic directed-limit verifier and the q-product
truncation and tail theorems. The final proof retains only checked finite data
and the analytic hypotheses required by those theorems.

Finite product-integral template:

[Exact Product-Integral Certificates](../proof-templates/qproduct-finite-integrals.md)

Detailed API reference:

[QProduct Certificates](../certificates/qproduct.md)
