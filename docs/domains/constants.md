# Constants Domain Library

Constant-related workflows currently use ConstantFactory as a perturbation
observer template over q-product moments.

Recommended imports:

```lean
import LeanCert.ConstantFactory
import LeanCert.ConstantFactory.IntervalBank
```

Use the exact observer API when the required moments reduce to rational
arithmetic. Use an interval kernel bank when a project supplies checked
enclosures for reusable base moments. In both cases, the project provides the
base data and disjoint perturbation set; LeanCert supplies the finite observer
identity and interval composition.

Start with the proof template:

[Perturbation Observers With ConstantFactory](../proof-templates/constant-factory.md)

Detailed API reference:

[ConstantFactory Certificates](../certificates/constants.md)
