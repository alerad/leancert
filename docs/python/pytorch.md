# PyTorch Export

Export trained PyTorch models to Lean for formal verification.

## Overview

LeanCert can verify properties of neural networks, but first you need to convert your PyTorch model to Lean's representation. The `leancert.nn` module handles this conversion.

## Quick Example

```python
import torch
import torch.nn as nn
import leancert as lc

# Your trained PyTorch model
class MyNetwork(nn.Module):
    def __init__(self):
        super().__init__()
        self.fc1 = nn.Linear(2, 4)
        self.fc2 = nn.Linear(4, 1)

    def forward(self, x):
        x = torch.relu(self.fc1(x))
        return self.fc2(x)

model = MyNetwork()
model.load_state_dict(torch.load("model.pt"))

# Convert to LeanCert
net = lf.nn.from_pytorch(model, input_names=['x1', 'x2'])

# Export to Lean code
lean_code = net.export_lean(
    name="myNetwork",
    namespace="MyProject.Networks",
)

print(lean_code)
```

## Output

The exported Lean code looks like:

```lean
import LeanCert.ML.Network

namespace MyProject.Networks

def myNetwork : List Layer := [
  { weights := [[1/2, -3/4], [1/8, 5/16], ...],
    bias := [1/32, -1/64, ...] },
  { weights := [[7/8, -1/2, 3/4, 1/4]],
    bias := [0] }
]

end MyProject.Networks
```

## API Reference

### `from_pytorch`

```python
lf.nn.from_pytorch(
    model: nn.Module,
    input_names: List[str],
    max_denominator: int = 1000
) -> Network
```

**Parameters:**

| Parameter | Type | Description |
|-----------|------|-------------|
| `model` | `nn.Module` | Trained PyTorch model |
| `input_names` | `List[str]` | Names for input variables |
| `max_denominator` | `int` | Max denominator for rational approximation |

**Supported layers:**
- `nn.Linear`
- `nn.ReLU`
- `nn.Sigmoid` (converted to interval bounds)

### `export_lean`

```python
net.export_lean(
    name: str,
    namespace: str = "LeanCert.Examples",
    include_imports: bool = True
) -> str
```

**Parameters:**

| Parameter | Type | Description |
|-----------|------|-------------|
| `name` | `str` | Lean definition name |
| `namespace` | `str` | Lean namespace |
| `include_imports` | `bool` | Include import statements |

### `Layer.from_numpy`

For direct NumPy array import:

```python
import numpy as np

weights = np.array([[1.0, -0.5], [0.25, 0.75]])
bias = np.array([0.1, -0.2])

layer = lf.nn.Layer.from_numpy(weights, bias, max_denominator=100)
```

## Rational Approximation

Neural network weights are floats, but Lean verification uses exact rationals. LeanCert approximates each weight as a fraction:

```python
# float 0.333... becomes 1/3
# float 0.142857... becomes 1/7
```

The `max_denominator` parameter controls precision:

| `max_denominator` | Precision | Verification Speed |
|-------------------|-----------|-------------------|
| 100 | Low | Fast |
| 1000 | Medium | Medium |
| 10000 | High | Slow |

**Tip:** Start with `max_denominator=100` for quick verification, increase if bounds are too loose.

## Verification Workflow

```python
# 1. Export model
net = lf.nn.from_pytorch(model, ['x'])
lean_code = net.export_lean(name="classifier")

# 2. Save to file
with open("MyNetwork.lean", "w") as f:
    f.write(lean_code)

# 3. In Lean, verify properties
```

```lean
-- MyNetwork.lean (generated)
import LeanCert.ML.Network

def classifier : List Layer := [...]

-- Verify robustness
theorem classifier_robust :
    ∀ x ∈ inputDomain, ∀ δ ∈ perturbation,
    classifier.forward (x + δ) = classifier.forward x := by
  -- Use interval propagation
  native_decide
```

## Supported Architectures

| Architecture | Support |
|--------------|---------|
| Feedforward (MLP) | Full |
| Convolutional | Flatten first |
| RNN/LSTM | Not supported |
| Transformer | Manual conversion |

For transformers, use the `LeanCert.ML.Transformer` module directly in Lean.

## Example: MNIST Classifier

```python
import torch
import torch.nn as nn
import leancert as lc

class MNISTNet(nn.Module):
    def __init__(self):
        super().__init__()
        self.fc1 = nn.Linear(784, 128)
        self.fc2 = nn.Linear(128, 10)

    def forward(self, x):
        x = torch.relu(self.fc1(x))
        return self.fc2(x)

# Load trained model
model = MNISTNet()
model.load_state_dict(torch.load("mnist.pt"))

# Export with reasonable precision
net = lf.nn.from_pytorch(
    model,
    input_names=[f'pixel_{i}' for i in range(784)],
    max_denominator=1000
)

# Generate Lean code
lean_code = net.export_lean(
    name="mnistClassifier",
    namespace="MNIST"
)

# Save
with open("MNISTClassifier.lean", "w") as f:
    f.write(lean_code)
```

## Transformer Export

LeanCert supports exporting Transformer architectures for formal verification.

### Quick Example

```python
import torch
import torch.nn as nn
import leancert as lc

# Create a PyTorch transformer
encoder_layer = nn.TransformerEncoderLayer(d_model=64, nhead=4)
transformer = nn.TransformerEncoder(encoder_layer, num_layers=2)

# Export to LeanCert
encoder = lc.nn.from_pytorch_transformer(transformer)

# Generate Lean code with affine arithmetic for tight LayerNorm bounds
lean_code = encoder.export_lean(
    name="myTransformer",
    namespace="MyProject.Transformers",
    input_domain={f"x{i}": (-1, 1) for i in range(64)},
    use_affine_layernorm=True,  # Use affine arithmetic for tighter bounds
)
```

### `from_pytorch_transformer`

```python
lc.nn.from_pytorch_transformer(
    model: nn.Module,
    input_names: List[str] = None,
    max_denominator: int = 10000,
    description: str = ""
) -> TransformerEncoder
```

**Parameters:**

| Parameter | Type | Description |
|-----------|------|-------------|
| `model` | `nn.Module` | PyTorch transformer model |
| `input_names` | `List[str]` | Names for input variables (default: x0, x1, ...) |
| `max_denominator` | `int` | Max denominator for rational approximation |
| `description` | `str` | Optional description for documentation |

**Supported architectures:**

- `nn.TransformerEncoder` with `nn.TransformerEncoderLayer`
- Custom models with `norm1`/`norm2` and `linear1`/`linear2` attributes
- BERT-style models with `encoder.layer[i]` structure

### Transformer Components

The export creates these Lean structures:

#### `LayerNormParams`

```python
lc.nn.LayerNormParams.from_numpy(
    gamma: np.ndarray,   # Scale parameter
    beta: np.ndarray,    # Shift parameter
    epsilon: float = 1e-6,
    max_denom: int = 10000
)
```

#### `FFNBlock`

Feed-forward network with GELU activation:

```python
lc.nn.FFNBlock.from_numpy(
    w1: np.ndarray,  # First linear weights
    b1: np.ndarray,  # First linear bias
    w2: np.ndarray,  # Second linear weights
    b2: np.ndarray,  # Second linear bias
    max_denom: int = 10000
)
```

#### `TransformerBlock`

A single transformer layer (LayerNorm → FFN → Residual → LayerNorm):

```python
block = lc.nn.TransformerBlock(
    ln1=layer_norm_params_1,
    ffn=ffn_block,
    ln2=layer_norm_params_2
)
```

#### `TransformerEncoder`

Complete encoder with multiple blocks:

```python
encoder = lc.nn.TransformerEncoder(
    blocks=[block1, block2, ...],
    final_ln=optional_final_layernorm,
    input_names=["x0", "x1", ...]
)
```

### Affine Arithmetic for LayerNorm

Standard interval arithmetic can produce loose bounds for LayerNorm due to the "dependency problem" - the mean and variance are computed from the same input, creating correlations that interval arithmetic ignores.

LeanCert provides **affine arithmetic** for tighter LayerNorm bounds:

```python
# Enable affine arithmetic (recommended for transformers)
lean_code = encoder.export_lean(
    name="transformer",
    use_affine_layernorm=True  # Uses forwardIntervalTight
)
```

This uses `LeanCert.ML.LayerNormAffine` which tracks linear correlations between variables.

### Generated Lean Code

The export generates Lean code that:

1. Defines rational weight/bias matrices
2. Creates `TransformerBlock` structures
3. Provides well-formedness proofs
4. Computes output bounds via interval propagation

```lean
-- Generated code example
import LeanCert.ML.Transformer
import LeanCert.ML.LayerNormAffine

namespace MyProject.Transformers

-- Layer definitions...

def myTransformerBlocks : List TransformerBlock := [...]

def myTransformerForward (x : IntervalVector) : IntervalVector :=
  myTransformerBlocks.foldl (fun acc blk => blk.forwardIntervalTight acc (-53)) x

#eval myTransformerOutputBounds.map (fun I => (I.lo.toRat, I.hi.toRat))

end MyProject.Transformers
```

## Limitations

1. **Float precision**: Rational approximation introduces small errors. Verify that `max_denominator` is sufficient for your use case.

2. **Large models**: Models with millions of parameters generate large Lean files. Consider verifying critical subnetworks.

3. **Activations**: Only ReLU, Sigmoid, and GELU are directly supported. Other activations need manual interval implementations.

4. **Attention**: Self-attention mechanisms are verified in Lean (`LeanCert.ML.Attention`) but not automatically extracted from PyTorch. Export the FFN portion and verify attention separately.
