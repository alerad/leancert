# Machine-Learning Verification

LeanCert Python can rationalize model parameters, export selected PyTorch
structures, and compute checked forward interval enclosures for sequential
ReLU networks.

!!! info "Capability status"
    **ReLU forward enclosures:** Programmatic checked operation ·
    **PyTorch conversion:** Untrusted preprocessing ·
    **Transformer support:** Experimental Lean source export

## A small ReLU network

```python
import numpy as np

import leancert as lc
from leancert.nn import Layer, TwoLayerReLUNetwork

hidden = Layer.from_numpy(
    weights=np.array([[2.0, -2.0], [-2.0, 2.0]]),
    bias=np.array([0.0, 0.0]),
    activation="relu",
)
output = Layer.from_numpy(
    weights=np.array([[1.0, 1.0]]),
    bias=np.array([0.0]),
    activation="none",
)
network = TwoLayerReLUNetwork(hidden, output, input_names=["x0", "x1"])

enclosures = lc.forward_interval(
    network,
    {"x0": (-1, 1), "x1": (-1, 1)},
    precision=-80,
)
print(enclosures)
```

`verify_nn_bounds` is a convenience wrapper that checks requested limits
against those output enclosures. It returns a Boolean rather than the v1
semantic `ProofResult` hierarchy.

## PyTorch conversion

Install the optional dependency:

```bash
pip install 'leancert[pytorch]'
```

The SDK can extract:

- two-layer linear/ReLU/linear models;
- sequential multi-layer perceptrons; and
- selected Transformer encoder feed-forward and LayerNorm structures.

Floating parameters are rationalized with a configurable denominator limit.
Conversion is candidate preparation, not a proof that the rationalized model
is semantically identical to every behavior of the original runtime model.
Record the source-model identity and rationalization policy in serious audits.

## Transformer scope

`TransformerBlock` currently models a simplified encoder feed-forward portion
without attention. The exporter can emit Lean definitions and optionally use
Affine LayerNorm infrastructure, but this is not a claim that arbitrary
end-to-end PyTorch Transformers are automatically verified by
`forward_interval`.

## Backends

The Python `forward_interval` convenience API currently targets the Bridge's
Dyadic sequential-network endpoint. Rational and Affine expression backends do
not imply selectable end-to-end NN propagation through this function.
