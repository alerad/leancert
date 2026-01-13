#!/usr/bin/env python3
"""
Train a neural network to approximate sin(x) on [0, π] using PyTorch.
Export weights as exact rationals for Lean verification.
"""

import torch
import torch.nn as nn
import numpy as np
from fractions import Fraction

class SineNet(nn.Module):
    """Simple ReLU network: 1 → 16 → 1"""
    def __init__(self):
        super().__init__()
        self.layer1 = nn.Linear(1, 16)
        self.layer2 = nn.Linear(16, 1)
        self.relu = nn.ReLU()

    def forward(self, x):
        x = self.relu(self.layer1(x))
        x = self.layer2(x)
        return x

def train_model():
    print("=" * 60)
    print("Training Sine Approximator with PyTorch")
    print("=" * 60)

    # Set seed for reproducibility
    torch.manual_seed(42)
    np.random.seed(42)

    # Create model
    model = SineNet()

    # Training data: sin(x) on [0, π]
    n_samples = 1000
    X = torch.linspace(0, np.pi, n_samples).reshape(-1, 1)
    y = torch.sin(X)

    print(f"\nArchitecture: 1 → 16 → 1 (ReLU)")
    print(f"Training samples: {n_samples}")

    # Training setup
    criterion = nn.MSELoss()
    optimizer = torch.optim.Adam(model.parameters(), lr=0.01)
    scheduler = torch.optim.lr_scheduler.StepLR(optimizer, step_size=2000, gamma=0.5)

    # Train
    print("\nTraining...")
    epochs = 10000
    for epoch in range(epochs):
        optimizer.zero_grad()
        pred = model(X)
        loss = criterion(pred, y)
        loss.backward()
        optimizer.step()
        scheduler.step()

        if epoch % 1000 == 0:
            print(f"  Epoch {epoch:5d}, Loss: {loss.item():.6f}, LR: {scheduler.get_last_lr()[0]:.6f}")

    print(f"  Epoch {epochs:5d}, Loss: {loss.item():.6f}")

    return model

def evaluate_model(model):
    print("\n" + "=" * 60)
    print("Evaluation")
    print("=" * 60)

    model.eval()
    with torch.no_grad():
        X_test = torch.linspace(0, np.pi, 100).reshape(-1, 1)
        y_test = torch.sin(X_test)
        pred = model(X_test)

        errors = torch.abs(pred - y_test)
        max_error = errors.max().item()
        mean_error = errors.mean().item()

        print(f"Max approximation error: {max_error:.6f}")
        print(f"Mean approximation error: {mean_error:.6f}")

        # Check specific points
        for x_val, name in [(0, "0"), (np.pi/2, "π/2"), (np.pi, "π")]:
            x_t = torch.tensor([[x_val]], dtype=torch.float32)
            pred_val = model(x_t).item()
            true_val = np.sin(x_val)
            print(f"  Network({name}) = {pred_val:.4f}, sin({name}) = {true_val:.4f}, error = {abs(pred_val - true_val):.4f}")

    return max_error

def float_to_rational(x, max_denom=10000):
    """Convert float to rational with bounded denominator."""
    frac = Fraction(float(x)).limit_denominator(max_denom)
    return (frac.numerator, frac.denominator)

def format_lean_rational(num, denom):
    """Format as Lean rational literal."""
    if denom == 1:
        return str(num)
    elif num < 0:
        return f"(({num}) : ℚ) / {denom}"
    else:
        return f"({num} : ℚ) / {denom}"

def export_to_lean(model, max_error):
    """Export model weights to Lean file."""

    # Extract weights
    w1 = model.layer1.weight.detach().numpy()  # (16, 1)
    b1 = model.layer1.bias.detach().numpy()    # (16,)
    w2 = model.layer2.weight.detach().numpy()  # (1, 16)
    b2 = model.layer2.bias.detach().numpy()    # (1,)

    lines = []
    lines.append("/-")
    lines.append("Copyright (c) 2025 LeanBound Contributors. All rights reserved.")
    lines.append("Released under AGPL-3.0 license as described in the file LICENSE.")
    lines.append("Authors: LeanBound Contributors")
    lines.append("-/")
    lines.append("import LeanBound.ML.Network")
    lines.append("")
    lines.append("set_option linter.unnecessarySeqFocus false")
    lines.append("")
    lines.append("/-!")
    lines.append("# Case Study: Verified Sine Approximator Neural Network")
    lines.append("")
    lines.append("This file demonstrates **end-to-end verified ML**:")
    lines.append("")
    lines.append("1. A neural network was trained in PyTorch to approximate sin(x)")
    lines.append("2. Weights were exported as exact rational numbers")
    lines.append("3. We formally verify output bounds using interval arithmetic")
    lines.append("")
    lines.append("## Network Architecture")
    lines.append("")
    lines.append("- **Input**: x ∈ [0, π]")
    lines.append("- **Hidden**: 16 neurons with ReLU activation")
    lines.append("- **Output**: approximation of sin(x)")
    lines.append("")
    lines.append(f"## Training Results")
    lines.append("")
    lines.append(f"- Max approximation error: {max_error:.4f}")
    lines.append(f"- The network learns to approximate sin(x) on [0, π]")
    lines.append("")
    lines.append("## Verified Property")
    lines.append("")
    lines.append("For ALL x ∈ [0, π], the network output is bounded within computed intervals.")
    lines.append("This is a mathematical proof, not empirical testing.")
    lines.append("-/")
    lines.append("")
    lines.append("namespace LeanBound.Examples.ML.SineApprox")
    lines.append("")
    lines.append("open LeanBound.Core")
    lines.append("open LeanBound.ML")
    lines.append("open IntervalVector")
    lines.append("")

    # Layer 1 weights
    lines.append(f"/-- Layer 1: 1 → 16 (trained weights) -/")
    lines.append(f"def layer1Weights : List (List ℚ) := [")
    for i, row in enumerate(w1):
        row_strs = [format_lean_rational(*float_to_rational(v)) for v in row]
        comma = "," if i < len(w1) - 1 else ""
        lines.append(f"  [{', '.join(row_strs)}]{comma}")
    lines.append("]")
    lines.append("")

    # Layer 1 bias
    bias_strs = [format_lean_rational(*float_to_rational(v)) for v in b1]
    lines.append(f"def layer1Bias : List ℚ := [{', '.join(bias_strs)}]")
    lines.append("")

    lines.append("def layer1 : Layer where")
    lines.append("  weights := layer1Weights")
    lines.append("  bias := layer1Bias")
    lines.append("")

    # Layer 2 weights
    lines.append(f"/-- Layer 2: 16 → 1 (trained weights) -/")
    lines.append(f"def layer2Weights : List (List ℚ) := [")
    for i, row in enumerate(w2):
        row_strs = [format_lean_rational(*float_to_rational(v)) for v in row]
        comma = "," if i < len(w2) - 1 else ""
        lines.append(f"  [{', '.join(row_strs)}]{comma}")
    lines.append("]")
    lines.append("")

    # Layer 2 bias
    bias_strs = [format_lean_rational(*float_to_rational(v)) for v in b2]
    lines.append(f"def layer2Bias : List ℚ := [{', '.join(bias_strs)}]")
    lines.append("")

    lines.append("def layer2 : Layer where")
    lines.append("  weights := layer2Weights")
    lines.append("  bias := layer2Bias")
    lines.append("")

    # Network definition
    lines.append("/-- The trained sine approximator network -/")
    lines.append("def sineNet : TwoLayerNet where")
    lines.append("  layer1 := layer1")
    lines.append("  layer2 := layer2")
    lines.append("")

    # Well-formedness proofs
    lines.append("/-! ## Well-formedness Proofs -/")
    lines.append("")
    lines.append("theorem layer1_wf : layer1.WellFormed := by")
    lines.append("  constructor")
    lines.append("  · intro row hrow")
    lines.append("    simp only [layer1, layer1Weights, Layer.inputDim] at *")
    lines.append("    fin_cases hrow <;> rfl")
    lines.append("  · rfl")
    lines.append("")
    lines.append("theorem layer2_wf : layer2.WellFormed := by")
    lines.append("  constructor")
    lines.append("  · intro row hrow")
    lines.append("    simp only [layer2, layer2Weights, Layer.inputDim] at *")
    lines.append("    fin_cases hrow <;> rfl")
    lines.append("  · rfl")
    lines.append("")
    lines.append("theorem sineNet_wf : sineNet.WellFormed := by")
    lines.append("  constructor")
    lines.append("  · exact layer1_wf")
    lines.append("  constructor")
    lines.append("  · exact layer2_wf")
    lines.append("  · simp [sineNet, layer1, layer2, layer1Weights, layer2Weights,")
    lines.append("         Layer.inputDim, Layer.outputDim, layer1Bias]")
    lines.append("")

    # Input domain and bounds
    lines.append("/-! ## Input Domain and Output Bounds -/")
    lines.append("")
    lines.append("/-- Helper to create dyadic interval -/")
    lines.append("def mkInterval (lo hi : ℚ) (h : lo ≤ hi := by norm_num) (prec : Int := -53) : IntervalDyadic :=")
    lines.append("  IntervalDyadic.ofIntervalRat ⟨lo, hi, h⟩ prec")
    lines.append("")
    lines.append("/-- Input domain: [0, π] where we use π ≈ 355/113 (more accurate than 22/7) -/")
    lines.append("def inputDomain : IntervalVector := [mkInterval 0 (355/113)]")
    lines.append("")
    lines.append("/-- Computed output bounds for the entire input domain -/")
    lines.append("def outputBounds : IntervalVector :=")
    lines.append("  TwoLayerNet.forwardInterval sineNet inputDomain (-53)")
    lines.append("")
    lines.append("-- Evaluate to see the concrete bounds")
    lines.append("#eval outputBounds.map (fun I => (I.lo.toRat, I.hi.toRat))")
    lines.append("")

    # Main theorem
    lines.append("/-! ## Main Verification Theorem -/")
    lines.append("")
    lines.append("/-- Membership in mkInterval -/")
    lines.append("theorem mem_mkInterval {x : ℝ} {lo hi : ℚ} (hle : lo ≤ hi)")
    lines.append("    (hx : (lo : ℝ) ≤ x ∧ x ≤ (hi : ℝ)) (prec : Int) (hprec : prec ≤ 0 := by norm_num) :")
    lines.append("    x ∈ mkInterval lo hi hle prec := by")
    lines.append("  unfold mkInterval")
    lines.append("  apply IntervalDyadic.mem_ofIntervalRat _ prec hprec")
    lines.append("  simp only [IntervalRat.mem_def]")
    lines.append("  exact hx")
    lines.append("")
    lines.append("/-- **Main Theorem**: For any x in [0, π], the network output is bounded.")
    lines.append("")
    lines.append("This is a formal verification certificate proving that the trained neural")
    lines.append("network's output lies within computed bounds for ALL inputs in the domain.")
    lines.append("")
    lines.append("Unlike testing (which checks finitely many points), this is a mathematical")
    lines.append("proof covering infinitely many inputs. -/")
    lines.append("theorem output_bounded {x : ℝ} (hx : 0 ≤ x ∧ x ≤ (355 : ℝ) / 113) :")
    lines.append("    ∀ i, (hi : i < min sineNet.layer2.outputDim sineNet.layer2.bias.length) →")
    lines.append("      (TwoLayerNet.forwardReal sineNet [x])[i]'(by")
    lines.append("        simp [TwoLayerNet.forwardReal, Layer.forwardReal_length]; omega) ∈")
    lines.append("      outputBounds[i]'(by")
    lines.append("        simp [outputBounds, TwoLayerNet.forwardInterval, Layer.forwardInterval_length]; omega) := by")
    lines.append("  have hwf := sineNet_wf")
    lines.append("  have hdim : sineNet.layer1.inputDim = inputDomain.length := by")
    lines.append("    simp [sineNet, layer1, layer1Weights, Layer.inputDim, inputDomain]")
    lines.append("  have hxlen : [x].length = inputDomain.length := by simp [inputDomain]")
    lines.append("  have hmem : ∀ i, (hi : i < inputDomain.length) →")
    lines.append("      [x][i]'(by omega) ∈ inputDomain[i]'hi := by")
    lines.append("    intro i hi")
    lines.append("    simp only [inputDomain, List.length_cons, List.length_nil] at hi")
    lines.append("    match i with")
    lines.append("    | 0 =>")
    lines.append("      simp only [inputDomain, List.getElem_cons_zero]")
    lines.append("      apply mem_mkInterval (by norm_num) _ (-53)")
    lines.append("      constructor")
    lines.append("      · simp only [Rat.cast_zero]; exact hx.1")
    lines.append("      · simp only [Rat.cast_div, Rat.cast_ofNat]; exact hx.2")
    lines.append("    | n + 1 => omega")
    lines.append("  intro i hi")
    lines.append("  have h := TwoLayerNet.mem_forwardInterval hwf hdim hxlen hmem (-53) (by norm_num) i hi")
    lines.append("  simp only [outputBounds]")
    lines.append("  exact h")
    lines.append("")

    # Interpretation
    lines.append("/-!")
    lines.append("## What This Proves")
    lines.append("")
    lines.append("The theorem `output_bounded` establishes:")
    lines.append("")
    lines.append("> **For every real number x with 0 ≤ x ≤ π:**")
    lines.append("> The neural network output is contained in the computed interval bounds.")
    lines.append("")
    lines.append("This is verified by Lean's proof checker - a mathematical certainty, not empirical testing.")
    lines.append("")
    lines.append("### Applications")
    lines.append("")
    lines.append("- **Safety certification**: Prove controller outputs stay in safe range")
    lines.append("- **Adversarial robustness**: Bound how much outputs can change")
    lines.append("- **Regulatory compliance**: Provide formal guarantees for ML systems")
    lines.append("-/")
    lines.append("")
    lines.append("end LeanBound.Examples.ML.SineApprox")

    return "\n".join(lines)

def main():
    # Train model
    model = train_model()

    # Evaluate
    max_error = evaluate_model(model)

    # Export to Lean
    print("\n" + "=" * 60)
    print("Exporting to Lean")
    print("=" * 60)

    lean_code = export_to_lean(model, max_error)
    output_path = "/Users/yales/workspace/leanbound/LeanBound/Examples/ML/SineApprox.lean"

    with open(output_path, "w") as f:
        f.write(lean_code)

    print(f"Verification file: {output_path}")

    # Print weight stats
    print("\n" + "=" * 60)
    print("Weight Statistics")
    print("=" * 60)
    for name, param in model.named_parameters():
        print(f"  {name}: shape={list(param.shape)}, range=[{param.min().item():.4f}, {param.max().item():.4f}]")

if __name__ == "__main__":
    main()
