# LeanCert Neural Network Export Module
# Copyright (c) 2024 LeanCert Contributors. All rights reserved.

"""
Neural network export and verification support.

This module provides tools for exporting trained neural networks to Lean
for formal verification of their properties.

Example:
    >>> import torch
    >>> import leancert as lb
    >>>
    >>> # Train your PyTorch model
    >>> model = MyNetwork()
    >>> # ... training ...
    >>>
    >>> # Export to Lean
    >>> net = lb.nn.from_pytorch(model, input_names=['x'])
    >>> lean_code = net.export_lean(
    ...     name="myNetwork",
    ...     namespace="MyProject",
    ...     input_domain={"x": (0, 1)},
    ... )
    >>>
    >>> # Save to file
    >>> with open("MyNetwork.lean", "w") as f:
    ...     f.write(lean_code)
"""

from dataclasses import dataclass, field
from fractions import Fraction
from typing import List, Optional, Dict, Tuple, Union
import numpy as np

__all__ = [
    "Layer",
    "TwoLayerReLUNetwork",
    "SequentialNetwork",
    "from_pytorch",
    "from_pytorch_sequential",
    "float_to_rational",
    # Transformer components
    "LayerNormParams",
    "LinearLayer",
    "FFNBlock",
    "TransformerBlock",
    "TransformerEncoder",
    "from_pytorch_transformer",
]


def float_to_rational(x: float, max_denom: int = 10000) -> Tuple[int, int]:
    """Convert float to rational with bounded denominator.

    Args:
        x: Float value to convert
        max_denom: Maximum denominator for the rational approximation

    Returns:
        Tuple of (numerator, denominator)
    """
    frac = Fraction(float(x)).limit_denominator(max_denom)
    return (frac.numerator, frac.denominator)


def _format_lean_rational(num: int, denom: int, parens_for_neg_int: bool = False) -> str:
    """Format as Lean rational literal.

    Args:
        num: Numerator
        denom: Denominator
        parens_for_neg_int: If True, wrap negative integers in parentheses
                           (needed for function arguments like `mkInterval (-1) 1`)
    """
    if denom == 1:
        if num < 0 and parens_for_neg_int:
            return f"({num})"
        return str(num)
    elif num < 0:
        return f"((({num}) : ℚ) / {denom})"
    else:
        return f"(({num} : ℚ) / {denom})"


@dataclass
class Layer:
    """A single dense layer with weights and biases.

    Attributes:
        weights: Weight matrix as list of rows, each row is list of rationals (num, denom)
        bias: Bias vector as list of rationals (num, denom)
        activation: Activation function name ('relu', 'none')
    """
    weights: List[List[Tuple[int, int]]]
    bias: List[Tuple[int, int]]
    activation: str = "relu"

    @property
    def input_dim(self) -> int:
        """Input dimension (number of columns in weight matrix)."""
        if not self.weights:
            return 0
        return len(self.weights[0])

    @property
    def output_dim(self) -> int:
        """Output dimension (number of rows in weight matrix)."""
        return len(self.weights)

    @classmethod
    def from_numpy(
        cls,
        weights: np.ndarray,
        bias: np.ndarray,
        activation: str = "relu",
        max_denom: int = 10000,
    ) -> "Layer":
        """Create layer from numpy arrays.

        Args:
            weights: Weight matrix of shape (output_dim, input_dim)
            bias: Bias vector of shape (output_dim,)
            activation: Activation function name
            max_denom: Maximum denominator for rational conversion
        """
        weight_rats = [
            [float_to_rational(v, max_denom) for v in row]
            for row in weights
        ]
        bias_rats = [float_to_rational(v, max_denom) for v in bias]
        return cls(weights=weight_rats, bias=bias_rats, activation=activation)


@dataclass
class TwoLayerReLUNetwork:
    """A two-layer ReLU network for verification.

    Architecture: input -> Linear -> ReLU -> Linear -> output

    Attributes:
        layer1: First layer (with ReLU activation)
        layer2: Second layer (no activation)
        input_names: Names for input variables
        description: Optional description for documentation
    """
    layer1: Layer
    layer2: Layer
    input_names: List[str] = field(default_factory=lambda: ["x"])
    description: str = ""

    @property
    def input_dim(self) -> int:
        """Input dimension."""
        return self.layer1.input_dim

    @property
    def hidden_dim(self) -> int:
        """Hidden layer dimension."""
        return self.layer1.output_dim

    @property
    def output_dim(self) -> int:
        """Output dimension."""
        return self.layer2.output_dim

    def export_lean(
        self,
        name: str = "network",
        namespace: str = "LeanCert.Examples.ML",
        input_domain: Optional[Dict[str, Tuple[float, float]]] = None,
        pi_approx: Tuple[int, int] = (355, 113),
        precision: int = -53,
        include_proofs: bool = True,
        training_error: Optional[float] = None,
    ) -> str:
        """Export network to Lean code with verification scaffolding.

        Args:
            name: Name for the network definition (e.g., "sineNet")
            namespace: Lean namespace
            input_domain: Dict mapping variable names to (lo, hi) bounds
            pi_approx: Rational approximation of pi as (num, denom)
            precision: Dyadic precision for interval arithmetic
            include_proofs: Whether to include well-formedness proofs
            training_error: Optional training error to document

        Returns:
            Complete Lean source code as string
        """
        lines = []

        # Header
        lines.append("/-")
        lines.append("Copyright (c) 2025 LeanCert Contributors. All rights reserved.")
        lines.append("Released under AGPL-3.0 license as described in the file LICENSE.")
        lines.append("Authors: LeanCert Contributors (auto-generated)")
        lines.append("-/")
        lines.append("import LeanCert.ML.Network")
        lines.append("")
        lines.append("set_option linter.unnecessarySeqFocus false")
        lines.append("")

        # Documentation
        lines.append("/-!")
        lines.append(f"# Neural Network: {name}")
        lines.append("")
        if self.description:
            lines.append(self.description)
            lines.append("")
        lines.append("## Architecture")
        lines.append("")
        lines.append(f"- **Input**: {self.input_dim} dimensions")
        lines.append(f"- **Hidden**: {self.hidden_dim} neurons with ReLU activation")
        lines.append(f"- **Output**: {self.output_dim} dimensions")
        lines.append("")
        if training_error is not None:
            lines.append("## Training Results")
            lines.append("")
            lines.append(f"- Max approximation error: {training_error:.6f}")
            lines.append("")
        lines.append("## Verification")
        lines.append("")
        lines.append("This file provides formal verification that the network output")
        lines.append("is bounded for all inputs in the specified domain.")
        lines.append("-/")
        lines.append("")

        # Namespace
        lines.append(f"namespace {namespace}")
        lines.append("")
        lines.append("open LeanCert.Core")
        lines.append("open LeanCert.ML")
        lines.append("open IntervalVector")
        lines.append("")

        # Layer 1 weights
        lines.append(f"/-- Layer 1: {self.input_dim} → {self.hidden_dim} -/")
        lines.append(f"def {name}Layer1Weights : List (List ℚ) := [")
        for i, row in enumerate(self.layer1.weights):
            row_strs = [_format_lean_rational(n, d) for (n, d) in row]
            comma = "," if i < len(self.layer1.weights) - 1 else ""
            lines.append(f"  [{', '.join(row_strs)}]{comma}")
        lines.append("]")
        lines.append("")

        # Layer 1 bias
        bias_strs = [_format_lean_rational(n, d) for (n, d) in self.layer1.bias]
        lines.append(f"def {name}Layer1Bias : List ℚ := [{', '.join(bias_strs)}]")
        lines.append("")

        lines.append(f"def {name}Layer1 : Layer where")
        lines.append(f"  weights := {name}Layer1Weights")
        lines.append(f"  bias := {name}Layer1Bias")
        lines.append("")

        # Layer 2 weights
        lines.append(f"/-- Layer 2: {self.hidden_dim} → {self.output_dim} -/")
        lines.append(f"def {name}Layer2Weights : List (List ℚ) := [")
        for i, row in enumerate(self.layer2.weights):
            row_strs = [_format_lean_rational(n, d) for (n, d) in row]
            comma = "," if i < len(self.layer2.weights) - 1 else ""
            lines.append(f"  [{', '.join(row_strs)}]{comma}")
        lines.append("]")
        lines.append("")

        # Layer 2 bias
        bias_strs = [_format_lean_rational(n, d) for (n, d) in self.layer2.bias]
        lines.append(f"def {name}Layer2Bias : List ℚ := [{', '.join(bias_strs)}]")
        lines.append("")

        lines.append(f"def {name}Layer2 : Layer where")
        lines.append(f"  weights := {name}Layer2Weights")
        lines.append(f"  bias := {name}Layer2Bias")
        lines.append("")

        # Network definition
        lines.append(f"/-- The {name} network -/")
        lines.append(f"def {name} : TwoLayerNet where")
        lines.append(f"  layer1 := {name}Layer1")
        lines.append(f"  layer2 := {name}Layer2")
        lines.append("")

        if include_proofs:
            # Well-formedness proofs
            lines.append("/-! ## Well-formedness Proofs -/")
            lines.append("")
            lines.append(f"theorem {name}Layer1_wf : {name}Layer1.WellFormed := by")
            lines.append("  constructor")
            lines.append("  · intro row hrow")
            lines.append(f"    simp only [{name}Layer1, {name}Layer1Weights, Layer.inputDim] at *")
            lines.append("    fin_cases hrow <;> rfl")
            lines.append("  · rfl")
            lines.append("")
            lines.append(f"theorem {name}Layer2_wf : {name}Layer2.WellFormed := by")
            lines.append("  constructor")
            lines.append("  · intro row hrow")
            lines.append(f"    simp only [{name}Layer2, {name}Layer2Weights, Layer.inputDim] at *")
            lines.append("    fin_cases hrow <;> rfl")
            lines.append("  · rfl")
            lines.append("")
            lines.append(f"theorem {name}_wf : {name}.WellFormed := by")
            lines.append("  constructor")
            lines.append(f"  · exact {name}Layer1_wf")
            lines.append("  constructor")
            lines.append(f"  · exact {name}Layer2_wf")
            lines.append(f"  · simp [{name}, {name}Layer1, {name}Layer2, {name}Layer1Weights, {name}Layer2Weights,")
            lines.append(f"         Layer.inputDim, Layer.outputDim, {name}Layer1Bias]")
            lines.append("")

        if input_domain:
            # Input domain and bounds
            lines.append("/-! ## Input Domain and Output Bounds -/")
            lines.append("")
            lines.append("/-- Helper to create dyadic interval -/")
            lines.append(f"def mkInterval (lo hi : ℚ) (h : lo ≤ hi := by norm_num) (prec : Int := {precision}) : IntervalDyadic :=")
            lines.append("  IntervalDyadic.ofIntervalRat ⟨lo, hi, h⟩ prec")
            lines.append("")

            # Build input domain
            domain_parts = []
            for var_name in self.input_names:
                if var_name in input_domain:
                    lo, hi = input_domain[var_name]
                    lo_rat = float_to_rational(lo)
                    hi_rat = float_to_rational(hi)
                    lo_str = _format_lean_rational(*lo_rat, parens_for_neg_int=True)
                    hi_str = _format_lean_rational(*hi_rat, parens_for_neg_int=True)
                    domain_parts.append(f"mkInterval {lo_str} {hi_str}")

            lines.append(f"/-- Input domain -/")
            lines.append(f"def {name}InputDomain : IntervalVector := [{', '.join(domain_parts)}]")
            lines.append("")

            lines.append(f"/-- Computed output bounds for the entire input domain -/")
            lines.append(f"def {name}OutputBounds : IntervalVector :=")
            lines.append(f"  TwoLayerNet.forwardInterval {name} {name}InputDomain ({precision})")
            lines.append("")
            lines.append(f"#eval {name}OutputBounds.map (fun I => (I.lo.toRat, I.hi.toRat))")
            lines.append("")

        lines.append(f"end {namespace}")

        return "\n".join(lines)


@dataclass
class SequentialNetwork:
    """An N-layer ReLU network for verification.

    Architecture: input -> [Linear -> ReLU]* -> Linear -> output

    All intermediate layers use ReLU activation. The final layer has no activation.

    Attributes:
        layers: List of Layer objects
        input_names: Names for input variables
        description: Optional description for documentation
    """
    layers: List[Layer]
    input_names: List[str] = field(default_factory=lambda: ["x"])
    description: str = ""

    @property
    def input_dim(self) -> int:
        """Input dimension."""
        if not self.layers:
            return 0
        return self.layers[0].input_dim

    @property
    def output_dim(self) -> int:
        """Output dimension."""
        if not self.layers:
            return 0
        return self.layers[-1].output_dim

    @property
    def num_layers(self) -> int:
        """Number of layers."""
        return len(self.layers)

    @property
    def hidden_dims(self) -> List[int]:
        """Hidden layer dimensions."""
        return [layer.output_dim for layer in self.layers[:-1]]

    def to_json(self) -> dict:
        """Convert to JSON-serializable dict for bridge communication."""
        return {
            "weights": [
                [[n / d for n, d in row] for row in layer.weights]
                for layer in self.layers
            ],
            "biases": [
                [n / d for n, d in layer.bias]
                for layer in self.layers
            ],
        }

    def export_lean(
        self,
        name: str = "network",
        namespace: str = "LeanCert.Examples.ML",
        input_domain: Optional[Dict[str, Tuple[float, float]]] = None,
        precision: int = -53,
        include_proofs: bool = True,
    ) -> str:
        """Export network to Lean code with verification scaffolding.

        Args:
            name: Name for the network definition
            namespace: Lean namespace
            input_domain: Dict mapping variable names to (lo, hi) bounds
            precision: Dyadic precision for interval arithmetic
            include_proofs: Whether to include well-formedness proofs

        Returns:
            Complete Lean source code as string
        """
        lines = []

        # Header
        lines.append("/-")
        lines.append("Copyright (c) 2025 LeanCert Contributors. All rights reserved.")
        lines.append("Released under AGPL-3.0 license as described in the file LICENSE.")
        lines.append("Authors: LeanCert Contributors (auto-generated)")
        lines.append("-/")
        lines.append("import LeanCert.ML.Distillation")
        lines.append("")
        lines.append("set_option linter.unnecessarySeqFocus false")
        lines.append("")

        # Documentation
        lines.append("/-!")
        lines.append(f"# Neural Network: {name}")
        lines.append("")
        if self.description:
            lines.append(self.description)
            lines.append("")
        lines.append("## Architecture")
        lines.append("")
        lines.append(f"- **Input**: {self.input_dim} dimensions")
        for i, dim in enumerate(self.hidden_dims):
            lines.append(f"- **Hidden {i+1}**: {dim} neurons with ReLU activation")
        lines.append(f"- **Output**: {self.output_dim} dimensions")
        lines.append("")
        lines.append("## Verification")
        lines.append("")
        lines.append("This file provides formal verification that the network output")
        lines.append("is bounded for all inputs in the specified domain.")
        lines.append("-/")
        lines.append("")

        # Namespace
        lines.append(f"namespace {namespace}")
        lines.append("")
        lines.append("open LeanCert.Core")
        lines.append("open LeanCert.ML")
        lines.append("open LeanCert.ML.Distillation")
        lines.append("open IntervalVector")
        lines.append("")

        # Export each layer
        for i, layer in enumerate(self.layers):
            in_dim = layer.input_dim
            out_dim = layer.output_dim
            is_last = (i == len(self.layers) - 1)
            activation = "none" if is_last else "ReLU"

            lines.append(f"/-- Layer {i+1}: {in_dim} → {out_dim} ({activation}) -/")
            lines.append(f"def {name}Layer{i+1}Weights : List (List ℚ) := [")
            for j, row in enumerate(layer.weights):
                row_strs = [_format_lean_rational(n, d) for (n, d) in row]
                comma = "," if j < len(layer.weights) - 1 else ""
                lines.append(f"  [{', '.join(row_strs)}]{comma}")
            lines.append("]")
            lines.append("")

            bias_strs = [_format_lean_rational(n, d) for (n, d) in layer.bias]
            lines.append(f"def {name}Layer{i+1}Bias : List ℚ := [{', '.join(bias_strs)}]")
            lines.append("")

            lines.append(f"def {name}Layer{i+1} : Layer where")
            lines.append(f"  weights := {name}Layer{i+1}Weights")
            lines.append(f"  bias := {name}Layer{i+1}Bias")
            lines.append("")

        # Network definition
        layer_names = [f"{name}Layer{i+1}" for i in range(len(self.layers))]
        lines.append(f"/-- The {name} network ({self.num_layers} layers) -/")
        lines.append(f"def {name} : SequentialNet where")
        lines.append(f"  layers := [{', '.join(layer_names)}]")
        lines.append("")

        if include_proofs:
            # Well-formedness proofs for each layer
            lines.append("/-! ## Well-formedness Proofs -/")
            lines.append("")

            for i, layer in enumerate(self.layers):
                lines.append(f"theorem {name}Layer{i+1}_wf : {name}Layer{i+1}.WellFormed := by")
                lines.append("  constructor")
                lines.append("  · intro row hrow")
                lines.append(f"    simp only [{name}Layer{i+1}, {name}Layer{i+1}Weights, Layer.inputDim] at *")
                lines.append("    fin_cases hrow <;> rfl")
                lines.append("  · rfl")
                lines.append("")

        if input_domain:
            # Input domain and bounds
            lines.append("/-! ## Input Domain and Output Bounds -/")
            lines.append("")
            lines.append(f"def mkInterval (lo hi : ℚ) (h : lo ≤ hi := by norm_num) (prec : Int := {precision}) : IntervalDyadic :=")
            lines.append("  IntervalDyadic.ofIntervalRat ⟨lo, hi, h⟩ prec")
            lines.append("")

            # Build input domain
            domain_parts = []
            for var_name in self.input_names:
                if var_name in input_domain:
                    lo, hi = input_domain[var_name]
                    lo_rat = float_to_rational(lo)
                    hi_rat = float_to_rational(hi)
                    lo_str = _format_lean_rational(*lo_rat, parens_for_neg_int=True)
                    hi_str = _format_lean_rational(*hi_rat, parens_for_neg_int=True)
                    domain_parts.append(f"mkInterval {lo_str} {hi_str}")

            lines.append(f"/-- Input domain -/")
            lines.append(f"def {name}InputDomain : IntervalVector := [{', '.join(domain_parts)}]")
            lines.append("")

            lines.append(f"/-- Computed output bounds for the entire input domain -/")
            lines.append(f"def {name}OutputBounds : IntervalVector :=")
            lines.append(f"  SequentialNet.forwardInterval {name} {name}InputDomain ({precision})")
            lines.append("")
            lines.append(f"#eval {name}OutputBounds.map (fun I => (I.lo.toRat, I.hi.toRat))")
            lines.append("")

        lines.append(f"end {namespace}")

        return "\n".join(lines)

    @classmethod
    def from_two_layer(cls, net: "TwoLayerReLUNetwork") -> "SequentialNetwork":
        """Convert a TwoLayerReLUNetwork to SequentialNetwork."""
        return cls(
            layers=[net.layer1, net.layer2],
            input_names=net.input_names,
            description=net.description,
        )


def from_pytorch_sequential(
    model,
    input_names: List[str] = None,
    max_denom: int = 10000,
    description: str = "",
) -> SequentialNetwork:
    """Create a SequentialNetwork from a PyTorch model with N linear layers.

    The model should be a sequence of Linear layers with optional ReLU activations.
    Supports nn.Sequential, or models with numbered layer attributes.

    Args:
        model: PyTorch nn.Module
        input_names: Names for input variables (default: ['x0', 'x1', ...])
        max_denom: Maximum denominator for rational conversion
        description: Optional description for documentation

    Returns:
        SequentialNetwork ready for Lean export

    Raises:
        ImportError: If PyTorch is not available
        ValueError: If no Linear layers found
    """
    try:
        import torch
        import torch.nn as nn
    except ImportError:
        raise ImportError(
            "PyTorch is required for from_pytorch_sequential(). "
            "Install with: pip install torch"
        )

    # Find all Linear layers
    linear_layers = []

    # Method 1: nn.Sequential or iterable
    if hasattr(model, '__iter__'):
        for module in model:
            if isinstance(module, nn.Linear):
                linear_layers.append(module)

    # Method 2: Direct children
    if not linear_layers:
        for child in model.children():
            if isinstance(child, nn.Linear):
                linear_layers.append(child)

    # Method 3: All modules (recursive)
    if not linear_layers:
        linear_layers = [m for m in model.modules() if isinstance(m, nn.Linear)]

    if not linear_layers:
        raise ValueError(
            "Could not find any Linear layers in model. "
            "Model should contain nn.Linear modules."
        )

    # Convert to Layer objects
    layers = []
    for i, linear in enumerate(linear_layers):
        w = linear.weight.detach().cpu().numpy()
        b = linear.bias.detach().cpu().numpy() if linear.bias is not None else np.zeros(linear.out_features)
        # All layers except last use ReLU
        activation = "none" if i == len(linear_layers) - 1 else "relu"
        layers.append(Layer.from_numpy(w, b, activation=activation, max_denom=max_denom))

    # Default input names
    if input_names is None:
        input_dim = layers[0].input_dim
        input_names = [f"x{i}" for i in range(input_dim)]

    return SequentialNetwork(
        layers=layers,
        input_names=input_names,
        description=description,
    )


###############################################################################
# Transformer Components
###############################################################################

@dataclass
class LayerNormParams:
    """Layer Normalization parameters.

    LayerNorm computes: (x - μ) / √(σ² + ε) * γ + β

    Attributes:
        gamma: Scale parameter γ (list of rationals)
        beta: Shift parameter β (list of rationals)
        epsilon: Numerical stability constant ε > 0
    """
    gamma: List[Tuple[int, int]]
    beta: List[Tuple[int, int]]
    epsilon: Tuple[int, int] = (1, 1000000)  # 1e-6 default

    @property
    def dim(self) -> int:
        """Dimension (length of gamma/beta)."""
        return len(self.gamma)

    @classmethod
    def from_numpy(
        cls,
        gamma: np.ndarray,
        beta: np.ndarray,
        epsilon: float = 1e-6,
        max_denom: int = 10000,
    ) -> "LayerNormParams":
        """Create LayerNormParams from numpy arrays.

        Args:
            gamma: Scale parameter array
            beta: Shift parameter array
            epsilon: Numerical stability constant
            max_denom: Maximum denominator for rational conversion
        """
        gamma_rats = [float_to_rational(v, max_denom) for v in gamma.flatten()]
        beta_rats = [float_to_rational(v, max_denom) for v in beta.flatten()]
        # Use larger denominator for epsilon to preserve small values
        # and ensure it's at least 1/10000000 for numerical stability
        eps_rat = float_to_rational(max(epsilon, 1e-7), 10000000)
        # Ensure epsilon is positive (norm_num can prove 1/n > 0)
        if eps_rat[0] <= 0:
            eps_rat = (1, 10000000)  # Fallback to small positive value
        return cls(gamma=gamma_rats, beta=beta_rats, epsilon=eps_rat)

    def export_lean(self, name: str) -> str:
        """Export to Lean definition."""
        lines = []

        # Gamma
        gamma_strs = [_format_lean_rational(n, d) for (n, d) in self.gamma]
        lines.append(f"def {name}Gamma : List ℚ := [{', '.join(gamma_strs)}]")

        # Beta
        beta_strs = [_format_lean_rational(n, d) for (n, d) in self.beta]
        lines.append(f"def {name}Beta : List ℚ := [{', '.join(beta_strs)}]")

        # Epsilon
        eps_str = _format_lean_rational(*self.epsilon)
        lines.append(f"def {name}Epsilon : ℚ := {eps_str}")

        # LayerNormParams structure
        lines.append(f"def {name} : LayerNormParams where")
        lines.append(f"  gamma := {name}Gamma")
        lines.append(f"  beta := {name}Beta")
        lines.append(f"  epsilon := {name}Epsilon")
        # Use simp to unfold the definition before norm_num can prove positivity
        lines.append(f"  epsilon_pos := by simp only [{name}Epsilon]; norm_num")

        return "\n".join(lines)


@dataclass
class LinearLayer:
    """A linear layer without activation.

    Computes: y = W·x + b

    Attributes:
        weights: Weight matrix as list of rows
        bias: Bias vector
    """
    weights: List[List[Tuple[int, int]]]
    bias: List[Tuple[int, int]]

    @property
    def input_dim(self) -> int:
        if not self.weights:
            return 0
        return len(self.weights[0])

    @property
    def output_dim(self) -> int:
        return len(self.weights)

    @classmethod
    def from_numpy(
        cls,
        weights: np.ndarray,
        bias: np.ndarray,
        max_denom: int = 10000,
    ) -> "LinearLayer":
        """Create from numpy arrays."""
        weight_rats = [
            [float_to_rational(v, max_denom) for v in row]
            for row in weights
        ]
        bias_rats = [float_to_rational(v, max_denom) for v in bias]
        return cls(weights=weight_rats, bias=bias_rats)

    def export_lean(self, name: str) -> str:
        """Export to Lean definition."""
        lines = []

        # Weights
        lines.append(f"def {name}Weights : List (List ℚ) := [")
        for i, row in enumerate(self.weights):
            row_strs = [_format_lean_rational(n, d) for (n, d) in row]
            comma = "," if i < len(self.weights) - 1 else ""
            lines.append(f"  [{', '.join(row_strs)}]{comma}")
        lines.append("]")

        # Bias
        bias_strs = [_format_lean_rational(n, d) for (n, d) in self.bias]
        lines.append(f"def {name}Bias : List ℚ := [{', '.join(bias_strs)}]")

        # Layer structure
        lines.append(f"def {name} : Layer where")
        lines.append(f"  weights := {name}Weights")
        lines.append(f"  bias := {name}Bias")

        return "\n".join(lines)


@dataclass
class FFNBlock:
    """Feed-Forward Network block with GELU activation.

    Architecture: Linear -> GELU -> Linear

    This is the MLP component used in Transformer blocks.

    Attributes:
        linear1: First linear layer (hidden expansion)
        linear2: Second linear layer (projection back)
        description: Optional description
    """
    linear1: LinearLayer
    linear2: LinearLayer
    description: str = ""

    @property
    def input_dim(self) -> int:
        return self.linear1.input_dim

    @property
    def hidden_dim(self) -> int:
        return self.linear1.output_dim

    @property
    def output_dim(self) -> int:
        return self.linear2.output_dim

    @classmethod
    def from_numpy(
        cls,
        w1: np.ndarray,
        b1: np.ndarray,
        w2: np.ndarray,
        b2: np.ndarray,
        max_denom: int = 10000,
        description: str = "",
    ) -> "FFNBlock":
        """Create FFNBlock from numpy arrays."""
        linear1 = LinearLayer.from_numpy(w1, b1, max_denom)
        linear2 = LinearLayer.from_numpy(w2, b2, max_denom)
        return cls(linear1=linear1, linear2=linear2, description=description)

    def export_lean(self, name: str) -> str:
        """Export to Lean definition."""
        lines = []

        # Linear layers
        lines.append(self.linear1.export_lean(f"{name}Linear1"))
        lines.append("")
        lines.append(self.linear2.export_lean(f"{name}Linear2"))
        lines.append("")

        # FFNBlock structure
        lines.append(f"/-- FFN Block: {self.input_dim} → {self.hidden_dim} → {self.output_dim} -/")
        lines.append(f"def {name} : FFNBlock where")
        lines.append(f"  linear1 := {name}Linear1")
        lines.append(f"  linear2 := {name}Linear2")
        lines.append(f"  dims_match := by simp [{name}Linear1, {name}Linear2, {name}Linear1Weights, {name}Linear2Weights, Layer.inputDim, Layer.outputDim, {name}Linear1Bias]")

        return "\n".join(lines)


@dataclass
class TransformerBlock:
    """A Transformer encoder block (simplified, without attention).

    Architecture: LN1 → FFN → Residual → LN2

    This represents the feed-forward portion of a Transformer layer.
    Full attention support requires additional components.

    Attributes:
        ln1: Pre-FFN layer normalization
        ffn: Feed-forward network
        ln2: Post-FFN layer normalization
        description: Optional description
    """
    ln1: LayerNormParams
    ffn: FFNBlock
    ln2: LayerNormParams
    description: str = ""

    @property
    def dim(self) -> int:
        """Model dimension."""
        return self.ln1.dim

    @property
    def hidden_dim(self) -> int:
        """FFN hidden dimension."""
        return self.ffn.hidden_dim

    def export_lean(self, name: str) -> str:
        """Export to Lean definition."""
        lines = []

        # LayerNorm 1
        lines.append(f"/-- Pre-FFN LayerNorm -/")
        lines.append(self.ln1.export_lean(f"{name}LN1"))
        lines.append("")

        # FFN
        lines.append(f"/-- Feed-Forward Network -/")
        lines.append(self.ffn.export_lean(f"{name}FFN"))
        lines.append("")

        # LayerNorm 2
        lines.append(f"/-- Post-FFN LayerNorm -/")
        lines.append(self.ln2.export_lean(f"{name}LN2"))
        lines.append("")

        # TransformerBlock structure
        lines.append(f"/-- Transformer Block: dim={self.dim}, hidden={self.hidden_dim} -/")
        lines.append(f"def {name} : TransformerBlock where")
        lines.append(f"  ln1 := {name}LN1")
        lines.append(f"  ffn := {name}FFN")
        lines.append(f"  ln2 := {name}LN2")

        return "\n".join(lines)


@dataclass
class TransformerEncoder:
    """A Transformer encoder with multiple blocks.

    Architecture: [TransformerBlock]* → Final LN

    Attributes:
        blocks: List of transformer blocks
        final_ln: Optional final layer normalization
        input_names: Names for input variables
        description: Optional description
    """
    blocks: List[TransformerBlock]
    final_ln: Optional[LayerNormParams] = None
    input_names: List[str] = field(default_factory=lambda: ["x"])
    description: str = ""

    @property
    def num_layers(self) -> int:
        return len(self.blocks)

    @property
    def dim(self) -> int:
        if self.blocks:
            return self.blocks[0].dim
        return 0

    @property
    def hidden_dim(self) -> int:
        if self.blocks:
            return self.blocks[0].hidden_dim
        return 0

    def export_lean(
        self,
        name: str = "transformer",
        namespace: str = "LeanCert.Examples.ML",
        input_domain: Optional[Dict[str, Tuple[float, float]]] = None,
        precision: int = -53,
        use_affine_layernorm: bool = True,
    ) -> str:
        """Export transformer to Lean code.

        Args:
            name: Name for the transformer definition
            namespace: Lean namespace
            input_domain: Dict mapping variable names to (lo, hi) bounds
            precision: Dyadic precision for interval arithmetic
            use_affine_layernorm: Use affine arithmetic for tighter LayerNorm bounds

        Returns:
            Complete Lean source code as string
        """
        lines = []

        # Header
        lines.append("/-")
        lines.append("Copyright (c) 2025 LeanCert Contributors. All rights reserved.")
        lines.append("Released under AGPL-3.0 license as described in the file LICENSE.")
        lines.append("Authors: LeanCert Contributors (auto-generated)")
        lines.append("-/")

        # Imports
        lines.append("import LeanCert.ML.Transformer")
        if use_affine_layernorm:
            lines.append("import LeanCert.ML.LayerNormAffine")
        lines.append("")
        lines.append("set_option linter.unnecessarySeqFocus false")
        lines.append("")

        # Documentation
        lines.append("/-!")
        lines.append(f"# Transformer Encoder: {name}")
        lines.append("")
        if self.description:
            lines.append(self.description)
            lines.append("")
        lines.append("## Architecture")
        lines.append("")
        lines.append(f"- **Layers**: {self.num_layers}")
        lines.append(f"- **Model Dimension**: {self.dim}")
        lines.append(f"- **FFN Hidden Dimension**: {self.hidden_dim}")
        if use_affine_layernorm:
            lines.append("")
            lines.append("## Affine Arithmetic")
            lines.append("")
            lines.append("LayerNorm uses affine arithmetic for tight bounds by tracking")
            lines.append("correlations between variables. This avoids the \"dependency problem\"")
            lines.append("where standard interval arithmetic loses correlation information.")
        lines.append("-/")
        lines.append("")

        # Namespace
        lines.append(f"namespace {namespace}")
        lines.append("")
        lines.append("open LeanCert.Core")
        lines.append("open LeanCert.ML")
        lines.append("open LeanCert.ML.Transformer")
        lines.append("open IntervalVector")
        lines.append("")

        # Export each block
        for i, block in enumerate(self.blocks):
            lines.append(f"/-! ## Layer {i + 1} -/")
            lines.append("")
            lines.append(block.export_lean(f"{name}Block{i + 1}"))
            lines.append("")

        # Final LayerNorm if present
        if self.final_ln is not None:
            lines.append(f"/-- Final LayerNorm -/")
            lines.append(self.final_ln.export_lean(f"{name}FinalLN"))
            lines.append("")

        # Blocks list
        lines.append(f"/-- All transformer blocks -/")
        block_names = [f"{name}Block{i + 1}" for i in range(self.num_layers)]
        lines.append(f"def {name}Blocks : List TransformerBlock := [{', '.join(block_names)}]")
        lines.append("")

        # Input domain if provided
        if input_domain:
            lines.append("/-! ## Input Domain and Verification -/")
            lines.append("")
            lines.append(f"def mkInterval (lo hi : ℚ) (h : lo ≤ hi := by norm_num) (prec : Int := {precision}) : IntervalDyadic :=")
            lines.append("  IntervalDyadic.ofIntervalRat ⟨lo, hi, h⟩ prec")
            lines.append("")

            # Build input domain
            domain_parts = []
            for var_name in self.input_names[:self.dim]:
                if var_name in input_domain:
                    lo, hi = input_domain[var_name]
                    lo_rat = float_to_rational(lo)
                    hi_rat = float_to_rational(hi)
                    lo_str = _format_lean_rational(*lo_rat, parens_for_neg_int=True)
                    hi_str = _format_lean_rational(*hi_rat, parens_for_neg_int=True)
                    domain_parts.append(f"mkInterval {lo_str} {hi_str}")
                else:
                    # Default domain [-1, 1]
                    domain_parts.append("mkInterval (-1) 1")

            # Pad with defaults if needed
            while len(domain_parts) < self.dim:
                domain_parts.append("mkInterval (-1) 1")

            lines.append(f"/-- Input domain -/")
            lines.append(f"def {name}Input : IntervalVector := [{', '.join(domain_parts)}]")
            lines.append("")

            # Forward pass function
            if use_affine_layernorm:
                lines.append(f"/-- Forward pass with affine arithmetic for tight LayerNorm bounds -/")
                lines.append(f"def {name}Forward (x : IntervalVector) (prec : Int := {precision}) : IntervalVector :=")
                lines.append(f"  {name}Blocks.foldl (fun acc blk => blk.forwardIntervalTight acc prec) x")
            else:
                lines.append(f"/-- Forward pass with standard interval arithmetic -/")
                lines.append(f"def {name}Forward (x : IntervalVector) (prec : Int := {precision}) : IntervalVector :=")
                lines.append(f"  {name}Blocks.foldl (fun acc blk => blk.forwardInterval acc prec) x")
            lines.append("")

            lines.append(f"/-- Computed output bounds -/")
            lines.append(f"def {name}OutputBounds : IntervalVector := {name}Forward {name}Input ({precision})")
            lines.append("")
            lines.append(f"#eval {name}OutputBounds.map (fun I => (I.lo.toRat, I.hi.toRat))")
            lines.append("")

        lines.append(f"end {namespace}")

        return "\n".join(lines)


def from_pytorch(
    model,
    input_names: List[str] = None,
    max_denom: int = 10000,
    description: str = "",
) -> TwoLayerReLUNetwork:
    """Create a TwoLayerReLUNetwork from a PyTorch model.

    The PyTorch model must have exactly two linear layers accessible as
    `model.layer1` and `model.layer2`, or `model.fc1` and `model.fc2`,
    or the first two Linear modules found.

    Args:
        model: PyTorch nn.Module with two linear layers
        input_names: Names for input variables (default: ['x'])
        max_denom: Maximum denominator for rational conversion
        description: Optional description for documentation

    Returns:
        TwoLayerReLUNetwork ready for Lean export

    Raises:
        ImportError: If PyTorch is not available
        ValueError: If model structure is not supported
    """
    try:
        import torch
        import torch.nn as nn
    except ImportError:
        raise ImportError(
            "PyTorch is required for from_pytorch(). "
            "Install with: pip install torch"
        )

    if input_names is None:
        input_names = ["x"]

    # Try to find the two linear layers
    layer1_module = None
    layer2_module = None

    # Method 1: Direct attributes
    for name1, name2 in [("layer1", "layer2"), ("fc1", "fc2"), ("linear1", "linear2")]:
        if hasattr(model, name1) and hasattr(model, name2):
            l1, l2 = getattr(model, name1), getattr(model, name2)
            if isinstance(l1, nn.Linear) and isinstance(l2, nn.Linear):
                layer1_module = l1
                layer2_module = l2
                break

    # Method 2: Find first two Linear modules
    if layer1_module is None:
        linear_layers = [m for m in model.modules() if isinstance(m, nn.Linear)]
        if len(linear_layers) >= 2:
            layer1_module = linear_layers[0]
            layer2_module = linear_layers[1]

    if layer1_module is None or layer2_module is None:
        raise ValueError(
            "Could not find two Linear layers in model. "
            "Model should have layer1/layer2, fc1/fc2, or at least two nn.Linear modules."
        )

    # Extract weights
    w1 = layer1_module.weight.detach().cpu().numpy()
    b1 = layer1_module.bias.detach().cpu().numpy()
    w2 = layer2_module.weight.detach().cpu().numpy()
    b2 = layer2_module.bias.detach().cpu().numpy()

    # Create layers
    layer1 = Layer.from_numpy(w1, b1, activation="relu", max_denom=max_denom)
    layer2 = Layer.from_numpy(w2, b2, activation="none", max_denom=max_denom)

    return TwoLayerReLUNetwork(
        layer1=layer1,
        layer2=layer2,
        input_names=input_names,
        description=description,
    )


def from_pytorch_transformer(
    model,
    input_names: List[str] = None,
    max_denom: int = 10000,
    description: str = "",
) -> TransformerEncoder:
    """Create a TransformerEncoder from a PyTorch model.

    Supports extraction from:
    - `nn.TransformerEncoder` with `nn.TransformerEncoderLayer`
    - Custom models with `layer_norm1`, `layer_norm2`, `linear1`, `linear2` attributes
    - BERT-style models with `encoder.layer[i]` structure

    Args:
        model: PyTorch nn.Module with transformer structure
        input_names: Names for input variables
        max_denom: Maximum denominator for rational conversion
        description: Optional description for documentation

    Returns:
        TransformerEncoder ready for Lean export

    Raises:
        ImportError: If PyTorch is not available
        ValueError: If model structure is not supported

    Example:
        >>> import torch.nn as nn
        >>> import leancert as lb
        >>>
        >>> # Create a PyTorch transformer
        >>> encoder_layer = nn.TransformerEncoderLayer(d_model=64, nhead=4)
        >>> transformer = nn.TransformerEncoder(encoder_layer, num_layers=2)
        >>>
        >>> # Export to LeanCert
        >>> encoder = lb.nn.from_pytorch_transformer(transformer)
        >>> lean_code = encoder.export_lean(
        ...     name="myTransformer",
        ...     input_domain={"x0": (-1, 1), "x1": (-1, 1)},
        ... )
    """
    try:
        import torch
        import torch.nn as nn
    except ImportError:
        raise ImportError(
            "PyTorch is required for from_pytorch_transformer(). "
            "Install with: pip install torch"
        )

    if input_names is None:
        input_names = [f"x{i}" for i in range(64)]  # Default names

    blocks = []

    # Method 1: Standard nn.TransformerEncoder
    if hasattr(model, 'layers'):
        for layer in model.layers:
            block = _extract_transformer_layer(layer, max_denom)
            if block is not None:
                blocks.append(block)

    # Method 2: BERT-style with encoder.layer
    elif hasattr(model, 'encoder') and hasattr(model.encoder, 'layer'):
        for layer in model.encoder.layer:
            block = _extract_bert_layer(layer, max_denom)
            if block is not None:
                blocks.append(block)

    # Method 3: Direct list of layers
    elif hasattr(model, '__iter__'):
        for layer in model:
            if hasattr(layer, 'norm1') or hasattr(layer, 'layer_norm1'):
                block = _extract_transformer_layer(layer, max_denom)
                if block is not None:
                    blocks.append(block)

    # Method 4: Single TransformerEncoderLayer
    elif hasattr(model, 'norm1') or hasattr(model, 'layer_norm1'):
        block = _extract_transformer_layer(model, max_denom)
        if block is not None:
            blocks.append(block)

    if not blocks:
        raise ValueError(
            "Could not extract transformer blocks from model. "
            "Model should be nn.TransformerEncoder, have layers attribute, "
            "or be a TransformerEncoderLayer with norm1/norm2 and linear1/linear2."
        )

    # Extract final layer norm if present
    final_ln = None
    if hasattr(model, 'norm') and model.norm is not None:
        final_ln = _extract_layer_norm(model.norm, max_denom)

    # Determine input dimension
    dim = blocks[0].dim if blocks else 0
    actual_input_names = input_names[:dim] if dim > 0 else input_names

    return TransformerEncoder(
        blocks=blocks,
        final_ln=final_ln,
        input_names=actual_input_names,
        description=description,
    )


def _extract_layer_norm(ln_module, max_denom: int) -> Optional[LayerNormParams]:
    """Extract LayerNorm parameters from a PyTorch LayerNorm module."""
    try:
        import torch.nn as nn
    except ImportError:
        return None

    if not isinstance(ln_module, nn.LayerNorm):
        return None

    gamma = ln_module.weight.detach().cpu().numpy()
    beta = ln_module.bias.detach().cpu().numpy()
    epsilon = ln_module.eps

    return LayerNormParams.from_numpy(gamma, beta, epsilon, max_denom)


def _extract_ffn_block(layer, max_denom: int) -> Optional[FFNBlock]:
    """Extract FFN block from a transformer layer."""
    try:
        import torch.nn as nn
    except ImportError:
        return None

    linear1 = None
    linear2 = None

    # Try common naming conventions
    for name1, name2 in [
        ('linear1', 'linear2'),
        ('fc1', 'fc2'),
        ('intermediate.dense', 'output.dense'),
        ('mlp.fc1', 'mlp.fc2'),
        ('mlp.c_fc', 'mlp.c_proj'),
    ]:
        l1 = _get_nested_attr(layer, name1)
        l2 = _get_nested_attr(layer, name2)
        if isinstance(l1, nn.Linear) and isinstance(l2, nn.Linear):
            linear1 = l1
            linear2 = l2
            break

    if linear1 is None or linear2 is None:
        # Try finding by type
        linears = [m for m in layer.modules() if isinstance(m, nn.Linear)]
        if len(linears) >= 2:
            # Assume first two are the FFN (skip attention projections)
            # This is a heuristic; more robust extraction would analyze dimensions
            for i, l1 in enumerate(linears[:-1]):
                for l2 in linears[i+1:]:
                    if l1.out_features == l2.in_features:
                        linear1 = l1
                        linear2 = l2
                        break
                if linear1 is not None:
                    break

    if linear1 is None or linear2 is None:
        return None

    w1 = linear1.weight.detach().cpu().numpy()
    b1 = linear1.bias.detach().cpu().numpy() if linear1.bias is not None else np.zeros(linear1.out_features)
    w2 = linear2.weight.detach().cpu().numpy()
    b2 = linear2.bias.detach().cpu().numpy() if linear2.bias is not None else np.zeros(linear2.out_features)

    return FFNBlock.from_numpy(w1, b1, w2, b2, max_denom)


def _extract_transformer_layer(layer, max_denom: int) -> Optional[TransformerBlock]:
    """Extract TransformerBlock from a PyTorch TransformerEncoderLayer."""
    try:
        import torch.nn as nn
    except ImportError:
        return None

    # Extract LayerNorms
    ln1 = None
    ln2 = None

    for name1, name2 in [
        ('norm1', 'norm2'),
        ('layer_norm1', 'layer_norm2'),
        ('ln_1', 'ln_2'),
        ('layernorm1', 'layernorm2'),
    ]:
        l1 = getattr(layer, name1, None)
        l2 = getattr(layer, name2, None)
        if isinstance(l1, nn.LayerNorm) and isinstance(l2, nn.LayerNorm):
            ln1 = _extract_layer_norm(l1, max_denom)
            ln2 = _extract_layer_norm(l2, max_denom)
            break

    if ln1 is None or ln2 is None:
        return None

    # Extract FFN
    ffn = _extract_ffn_block(layer, max_denom)
    if ffn is None:
        return None

    return TransformerBlock(ln1=ln1, ffn=ffn, ln2=ln2)


def _extract_bert_layer(layer, max_denom: int) -> Optional[TransformerBlock]:
    """Extract TransformerBlock from a BERT-style layer."""
    try:
        import torch.nn as nn
    except ImportError:
        return None

    # BERT structure: attention -> LayerNorm -> FFN -> LayerNorm
    ln1 = None
    ln2 = None

    # Try BERT naming conventions
    if hasattr(layer, 'attention') and hasattr(layer.attention, 'output'):
        ln1_module = getattr(layer.attention.output, 'LayerNorm', None)
        if ln1_module is not None:
            ln1 = _extract_layer_norm(ln1_module, max_denom)

    if hasattr(layer, 'output'):
        ln2_module = getattr(layer.output, 'LayerNorm', None)
        if ln2_module is not None:
            ln2 = _extract_layer_norm(ln2_module, max_denom)

    if ln1 is None or ln2 is None:
        # Fallback: find any LayerNorm modules
        layer_norms = [m for m in layer.modules() if isinstance(m, nn.LayerNorm)]
        if len(layer_norms) >= 2:
            ln1 = _extract_layer_norm(layer_norms[0], max_denom)
            ln2 = _extract_layer_norm(layer_norms[1], max_denom)

    if ln1 is None or ln2 is None:
        return None

    # Extract FFN
    ffn = _extract_ffn_block(layer, max_denom)
    if ffn is None:
        return None

    return TransformerBlock(ln1=ln1, ffn=ffn, ln2=ln2)


def _get_nested_attr(obj, attr_path: str):
    """Get a nested attribute like 'intermediate.dense'."""
    parts = attr_path.split('.')
    for part in parts:
        obj = getattr(obj, part, None)
        if obj is None:
            return None
    return obj
