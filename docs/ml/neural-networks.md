# Neural Network Verification

LeanBound includes a verified neural network verification module based on interval propagation and DeepPoly relaxations.

## Overview

The ML module provides:

- **Interval Propagation**: Sound overapproximation of neural network outputs
- **DeepPoly Relaxations**: Tight linear bounds for ReLU and sigmoid activations
- **Verified Soundness**: All propagation theorems are formally proved in Lean

## Quick Example

```lean
import LeanBound.ML.Network

open LeanBound.ML

-- Define a simple 2-layer network
def myNet : TwoLayerNet := {
  layer1 := { weights := [[1, -1], [0, 1]], bias := [0, 0] }
  layer2 := { weights := [[1, 1]], bias := [0] }
}

-- Input interval: x₁ ∈ [-1, 1], x₂ ∈ [0, 1]
def inputBox : IntervalVector := [
  IntervalDyadic.ofRat (-1) 1,
  IntervalDyadic.ofRat 0 1
]

-- Propagate intervals through the network
def outputBounds := myNet.forwardInterval inputBox
```

## Architecture

### Layer Structure

A dense layer computes \\( y = \text{ReLU}(Wx + b) \\):

```lean
structure Layer where
  weights : List (List ℚ)  -- Weight matrix (rows)
  bias : List ℚ            -- Bias vector
```

### Soundness Theorem

The key theorem guarantees that interval propagation is sound:

```lean
theorem mem_forwardInterval {l : Layer} {xs : List ℝ} {Is : IntervalVector}
    (hwf : l.WellFormed)
    (hdim : l.inputDim = Is.length)
    (hxlen : xs.length = Is.length)
    (hmem : ∀ i, xs[i] ∈ Is[i]) :
    ∀ i, (forwardReal l xs)[i] ∈ (forwardInterval l Is)[i]
```

This says: if every real input is contained in its corresponding interval, then every real output is contained in its corresponding output interval.

## Activation Functions

### ReLU

ReLU interval propagation uses the simple rule:

\\[
\text{ReLU}([l, u]) = [\max(0, l), \max(0, u)]
\\]

```lean
def relu (I : IntervalDyadic) : IntervalDyadic where
  lo := Dyadic.max 0 I.lo
  hi := Dyadic.max 0 I.hi

theorem mem_relu {x : ℝ} {I : IntervalDyadic} (hx : x ∈ I) :
    max 0 x ∈ relu I
```

### Sigmoid

Sigmoid uses the conservative bound \\( \sigma(x) \in (0, 1) \\):

```lean
def sigmoid (_I : IntervalDyadic) : IntervalDyadic where
  lo := 0
  hi := 1

theorem mem_sigmoid {x : ℝ} {I : IntervalDyadic} (_hx : x ∈ I) :
    Real.sigmoid x ∈ sigmoid I
```

## DeepPoly Relaxations

For tighter bounds, the module implements DeepPoly-style linear relaxations.

### ReLU Triangle Relaxation

For the "crossing case" where \\( l < 0 < u \\), ReLU is bounded by:

- **Lower**: \\( y \geq 0 \\)
- **Upper**: The line through \\( (l, 0) \\) and \\( (u, u) \\)

```lean
theorem upper_bound_valid (l u : ℚ) (x : ℝ)
    (hl : l < 0) (hu : 0 < u) (hx_mem : l ≤ x ∧ x ≤ u) :
    max 0 x ≤ (crossingUpperBound l u).eval x
```

### Sigmoid Monotonicity Bounds

Since sigmoid is strictly monotone:

\\[
\sigma(l) \leq \sigma(x) \leq \sigma(u) \quad \text{for } x \in [l, u]
\\]

```lean
theorem sigmoid_relaxation_sound (l u x : ℝ) (h : l ≤ x ∧ x ≤ u) :
    sigmoid l ≤ sigmoid x ∧ sigmoid x ≤ sigmoid u
```

## Optimized Implementation

For real-world networks, the `LeanBound.ML.Optimized` module provides:

| Optimization | Speedup | Description |
|--------------|---------|-------------|
| Structure-of-Arrays | ~5x | Cache-efficient interval storage |
| Split-Sign Decomposition | ~2x | Branch-free interval matrix multiply |
| Common Exponent Alignment | ~10-50x | Pure integer (GMP) arithmetic |

```lean
import LeanBound.ML.Optimized

open LeanBound.ML.Optimized

-- Create quantized network for fast propagation
def qnet := QuantizedNet.ofLayers myLayers

-- Fast interval propagation
def output := qnet.forward alignedInput
```

## Verification Status

| Component | Status |
|-----------|--------|
| `mem_forwardInterval` (layer soundness) | ✓ Fully verified |
| `mem_relu` | ✓ Fully verified |
| `mem_sigmoid` | ✓ Fully verified |
| `relu_relaxation_sound` (DeepPoly ReLU) | ✓ Fully verified |
| `sigmoid_relaxation_sound` (DeepPoly Sigmoid) | ✓ Fully verified |
| Optimized implementations | Computationally correct, proofs in progress |

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
