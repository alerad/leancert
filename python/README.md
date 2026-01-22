# LeanCert

Formal verification for numerical Python code, powered by Lean4.

Write Python, get mathematical proofs. LeanCert proves properties about your code for *all* inputs, not just test samples.

## Installation

```bash
pip install leancert
```

That's it! The package includes pre-built binaries - no Lean installation required.

## Quick Start

```python
import leancert as lc

# Define a symbolic expression
x = lc.var('x')
expr = x**2 + lc.sin(x)

# Verify a bound holds for ALL x in [-2, 2]
verified = lc.verify_bound(expr, {'x': (-2, 2)}, lower=-0.25)
print(verified)  # True - mathematically proven!

# Find rigorous bounds
result = lc.find_bounds(expr, {'x': (-2, 2)})
print(f"min in [{result.min_lo}, {result.min_hi}]")
print(f"max in [{result.max_lo}, {result.max_hi}]")
```

## Neural Network Verification

Verify properties of neural networks across entire input domains:

```python
import leancert as lc
from leancert.nn import TwoLayerReLUNetwork, Layer
import numpy as np

# Create/load a neural network
layer1 = Layer.from_numpy(
    weights=np.array([[2.0, -2.0], [-2.0, 2.0]]),
    bias=np.array([0.0, 0.0]),
    activation='relu'
)
layer2 = Layer.from_numpy(
    weights=np.array([[1.0, 1.0]]),
    bias=np.array([0.0]),
    activation='none'
)
network = TwoLayerReLUNetwork(layer1=layer1, layer2=layer2)

# Prove output bounds for ALL inputs in domain
verified = lc.verify_nn_bounds(
    network,
    {'x0': (-1, 1), 'x1': (-1, 1)},
    output_lower=-5,
    output_upper=5,
)
print(verified)  # True - proven for every possible input!
```

## Key Features

- **Interval Arithmetic**: Rigorous bounds using machine-verified Lean4 kernel
- **Neural Networks**: Verify ReLU networks, transformers
- **Root Finding**: Locate and isolate roots with guaranteed correctness
- **Integration**: Compute integral bounds
- **PyTorch Import**: Load weights directly from PyTorch models

## Supported Functions

`sin`, `cos`, `tan`, `exp`, `log`, `sqrt`, `abs`, `sinh`, `cosh`, `tanh`, `atan`, `erf`, `sinc`, and more.

## Why LeanCert?

Traditional testing samples inputs: `f(0.5)`, `f(1.0)`, etc. You can never test `f(0.7)` and the infinitely many values in between.

LeanCert uses interval arithmetic to prove properties for *all* inputs simultaneously. The heavy lifting happens in Lean4's kernel, which has a small, trusted core verified to be mathematically sound.

## Links

- [Documentation](https://leancert.readthedocs.io)
- [GitHub](https://github.com/leanbound/leancert)
- [Examples](https://github.com/leanbound/leancert/tree/main/python/examples)

## License

Apache 2.0
