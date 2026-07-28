# Neural Network & Transformer Verification

LeanCert includes verified neural network verification based on interval propagation and DeepPoly relaxations, with support for modern architectures including Transformers.

## Overview

The ML module provides:

- **Interval Propagation**: Sound overapproximation of neural network outputs
- **DeepPoly Relaxations**: Tight linear bounds for ReLU and sigmoid activations
- **Transformer Support**: Multi-Head Attention, LayerNorm, GELU, Residual connections
- **Verified Soundness**: The component-level soundness theorems listed below
  are formally proved in Lean

## Supported Architectures

| Architecture | Components | Status |
|--------------|------------|--------|
| Feedforward (MLP) | Linear, ReLU, Sigmoid | Elementwise enclosure theorems |
| Transformer primitives | LayerNorm, GELU | Elementwise enclosure theorems |
| Attention and full transformer blocks | Attention, residual composition | Implemented; current public theorem coverage is structural rather than a full elementwise enclosure |

## Quick Example

```lean
import LeanCert.ML.Network

open LeanCert.ML

-- Define a simple 2-layer network
def myNet : TwoLayerNet := {
  layer1 := { weights := [[1, -1], [0, 1]], bias := [0, 0] }
  layer2 := { weights := [[1, 1]], bias := [0] }
}

-- Input interval: x₁ ∈ [-1, 1], x₂ ∈ [0, 1]
def inputBox : IntervalVector := [
  IntervalDyadic.ofIntervalRat ⟨-1, 1, by norm_num⟩ (-53),
  IntervalDyadic.ofIntervalRat ⟨0, 1, by norm_num⟩ (-53)
]

-- Propagate intervals through the network
def outputBounds := myNet.forwardInterval inputBox
```

## Architecture

### Layer Structure

A dense layer computes $y = \text{ReLU}(Wx + b)$:

```lean
structure Layer where
  weights : List (List ℚ)  -- Weight matrix (rows)
  bias : List ℚ            -- Bias vector
```

### Soundness Theorem

The exact theorem guarantees that interval propagation is sound:

```lean
#check Layer.mem_forwardInterval
#check TwoLayerNet.mem_forwardInterval
```

These theorems require well-formed dimensions, componentwise input membership,
a nonpositive precision, and bounded index proofs. Their conclusions give
componentwise membership of every real output in the computed interval output.

## Activation Functions

### ReLU

ReLU interval propagation uses the simple rule:

$$
\text{ReLU}([l, u]) = [\max(0, l), \max(0, u)]
$$

```lean
#check IntervalVector.relu
#check IntervalVector.mem_relu
```

### Sigmoid

Sigmoid uses the conservative closed enclosure $\sigma(x) \in [0, 1]$:

```lean
#check IntervalVector.sigmoid
#check IntervalVector.mem_sigmoid
```

## DeepPoly Relaxations

For tighter bounds, the module implements DeepPoly-style linear relaxations.

### ReLU Triangle Relaxation

For the "crossing case" where $l < 0 < u$, ReLU is bounded by:

- **Lower**: $y \geq 0$
- **Upper**: The line through $(l, 0)$ and $(u, u)$

```lean
#check LeanCert.ML.Symbolic.relu_relaxation_sound
```

### Sigmoid Monotonicity Bounds

Since sigmoid is strictly monotone:

$$
\sigma(l) \leq \sigma(x) \leq \sigma(u) \quad \text{for } x \in [l, u]
$$

```lean
#check LeanCert.ML.Symbolic.sigmoid_relaxation_sound
```

### GELU Activation

LeanCert's Transformer interval path uses the common tanh approximation to
GELU:

$$
\text{GELU}(x) = 0.5 \cdot x \cdot (1 + \tanh(\sqrt{2/\pi} \cdot (x + 0.044715 \cdot x^3)))
$$

```lean
#check LeanCert.ML.Transformer.geluInterval
#check LeanCert.ML.Transformer.mem_geluInterval
```

For the erf-based formulation, use `LeanCert.ML.ErfGELU`.

## Transformer Components

### Self-Attention

LeanCert implements interval propagation for scaled dot-product attention:

$$
\text{Attention}(Q, K, V) = \text{softmax}\left(\frac{Q \cdot K^T}{\sqrt{d_k}}\right) \cdot V
$$

```lean
import LeanCert.ML.Attention

#check LeanCert.ML.Attention.mem_scaledDotProductAttention
```

Despite its historical name, the current
`mem_scaledDotProductAttention` theorem proves an output-length relation; its
elementwise membership hypotheses are explicitly omitted in the implementation.
Do not treat it as a complete semantic enclosure theorem.

### Layer Normalization

Interval bounds for LayerNorm are computed soundly:

```lean
import LeanCert.ML.Transformer

#check LeanCert.ML.Transformer.mem_layerNorm_forwardInterval
```

**Note**: Standard interval arithmetic may overestimate LayerNorm bounds due to variable correlation (the mean and variance are computed from the same input).

### Affine Arithmetic for Tight LayerNorm Bounds

To address the dependency problem in LayerNorm, LeanCert provides `LeanCert.ML.LayerNormAffine` which uses **affine arithmetic** to track linear correlations between variables:

```lean
import LeanCert.ML.LayerNormAffine

-- Affine LayerNorm is exposed through the parameter object.
#check LeanCert.ML.Transformer.LayerNormParams.forwardAffine
#check LeanCert.ML.Transformer.mem_forwardAffine

-- Transformer blocks use it in the tighter interval path.
#check LeanCert.ML.Transformer.TransformerBlock.forwardIntervalTight
```

**Key insight**: In LayerNorm, the centering operation `x - μ` creates
correlated outputs. Standard interval arithmetic loses some of that
correlation; affine arithmetic retains linear correlation information. Exact
numerical comparisons depend on the vector box, dimension, `gamma`, `beta`,
`epsilon`, precision, and output coordinate, so no parameter-free bound is
claimed here.

Use `TransformerBlock.forwardIntervalTight` for the tightest bounds on transformer layers.

## Optimized Implementation

For larger networks, `LeanCert.ML.Optimized` provides structure-of-arrays
storage, split-sign matrix operations, common-exponent aligned inputs, and
quantized layers. Performance depends on workload and should be measured with
the repository benchmark harness rather than inferred from fixed multipliers.

```lean
import LeanCert.ML.Optimized

open LeanCert.ML.Optimized

#check QuantizedLayer.forwardQuantized
#check QuantizedLayer.forwardQuantized_sound
```

## Verification Status

| Component | Status |
|-----------|--------|
| `mem_forwardInterval` (layer soundness) | ✓ Fully verified |
| `mem_relu` | ✓ Fully verified |
| `mem_sigmoid` | ✓ Fully verified |
| `relu_relaxation_sound` (DeepPoly ReLU) | ✓ Fully verified |
| `sigmoid_relaxation_sound` (DeepPoly Sigmoid) | ✓ Fully verified |
| Quantized split-sign propagation (`forwardQuantized_sound`) | Proves computed lower endpoints do not exceed computed upper endpoints |
| Attention output | Structural length theorem; full elementwise enclosure theorem not yet exposed |
| Other optimized representations and conversions | Check the exact component theorem before relying on a semantic guarantee |

## Use Cases

- **Robustness Verification**: Prove that small input perturbations don't change the output class
- **Safety Certification**: Verify that outputs stay within safe bounds
- **Lipschitz Estimation**: Bound the sensitivity of the network to input changes

## Files

| File | Description |
|------|-------------|
| `ML/Network.lean` | Layer and network definitions |
| `ML/IntervalVector.lean` | Activation functions (ReLU, sigmoid) |
| `ML/Symbolic/ReLU.lean` | DeepPoly ReLU relaxation |
| `ML/Symbolic/Sigmoid.lean` | DeepPoly sigmoid relaxation |
| `ML/Optimized.lean` | High-performance implementations |
| `ML/LayerNormAffine.lean` | Affine arithmetic for tight LayerNorm bounds |
| `ML/Transformer.lean` | Full transformer block definitions |
| `ML/Attention.lean` | Scaled dot-product attention verification |
| `ML/Softmax.lean` | Softmax interval propagation |
