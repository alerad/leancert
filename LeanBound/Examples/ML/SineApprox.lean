/-
Copyright (c) 2025 LeanBound Contributors. All rights reserved.
Released under AGPL-3.0 license as described in the file LICENSE.
Authors: LeanBound Contributors
-/
import LeanBound.ML.Network

set_option linter.unnecessarySeqFocus false

/-!
# Case Study: Verified Sine Approximator Neural Network

This file demonstrates **end-to-end verified ML**:

1. A neural network was trained in PyTorch to approximate sin(x)
2. Weights were exported as exact rational numbers
3. We formally verify output bounds using interval arithmetic

## Network Architecture

- **Input**: x ∈ [0, π]
- **Hidden**: 16 neurons with ReLU activation
- **Output**: approximation of sin(x)

## Training Results

- Max approximation error: 0.0317
- The network learns to approximate sin(x) on [0, π]

## Verified Property

For ALL x ∈ [0, π], the network output is bounded within computed intervals.
This is a mathematical proof, not empirical testing.
-/

namespace LeanBound.Examples.ML.SineApprox

open LeanBound.Core
open LeanBound.ML
open IntervalVector

/-- Layer 1: 1 → 16 (trained weights) -/
def layer1Weights : List (List ℚ) := [
  [(9061 : ℚ) / 9710],
  [(1552 : ℚ) / 993],
  [((-607) : ℚ) / 2591],
  [(8191 : ℚ) / 7266],
  [((-1007) : ℚ) / 4596],
  [(375 : ℚ) / 8438],
  [((-4463) : ℚ) / 9167],
  [(2893 : ℚ) / 5974],
  [(6716 : ℚ) / 6591],
  [((-4313) : ℚ) / 5879],
  [(11894 : ℚ) / 9737],
  [(309 : ℚ) / 1651],
  [(9132 : ℚ) / 9523],
  [(1115 : ℚ) / 8233],
  [(5841 : ℚ) / 9256],
  [((-1029) : ℚ) / 7288]
]

def layer1Bias : List ℚ := [(461 : ℚ) / 1126, ((-581) : ℚ) / 414, ((-4132) : ℚ) / 8851, (1 : ℚ) / 9810, ((-663) : ℚ) / 1439, ((-17) : ℚ) / 70, ((-277) : ℚ) / 682, (4488 : ℚ) / 6317, ((-16621) : ℚ) / 7287, ((-4499) : ℚ) / 9759, ((-17785) : ℚ) / 9287, ((-5765) : ℚ) / 9588, (2 : ℚ) / 9667, ((-7375) : ℚ) / 7467, (2463 : ℚ) / 4460, ((-3115) : ℚ) / 3667]

def layer1 : Layer where
  weights := layer1Weights
  bias := layer1Bias

/-- Layer 2: 16 → 1 (trained weights) -/
def layer2Weights : List (List ℚ) := [
  [(2351 : ℚ) / 9922, ((-373) : ℚ) / 1050, ((-577) : ℚ) / 7108, (942 : ℚ) / 3269, (305 : ℚ) / 7828, (356 : ℚ) / 6801, (139 : ℚ) / 5086, ((-605) : ℚ) / 9156, ((-5140) : ℚ) / 9361, ((-657) : ℚ) / 9691, ((-149) : ℚ) / 280, (227 : ℚ) / 1017, (2774 : ℚ) / 9337, ((-1022) : ℚ) / 9351, (697 : ℚ) / 5217, (45 : ℚ) / 1006]
]

def layer2Bias : List ℚ := [((-57) : ℚ) / 565]

def layer2 : Layer where
  weights := layer2Weights
  bias := layer2Bias

/-- The trained sine approximator network -/
def sineNet : TwoLayerNet where
  layer1 := layer1
  layer2 := layer2

/-! ## Well-formedness Proofs -/

theorem layer1_wf : layer1.WellFormed := by
  constructor
  · intro row hrow
    simp only [layer1, layer1Weights, Layer.inputDim] at *
    fin_cases hrow <;> rfl
  · rfl

theorem layer2_wf : layer2.WellFormed := by
  constructor
  · intro row hrow
    simp only [layer2, layer2Weights, Layer.inputDim] at *
    fin_cases hrow <;> rfl
  · rfl

theorem sineNet_wf : sineNet.WellFormed := by
  constructor
  · exact layer1_wf
  constructor
  · exact layer2_wf
  · simp [sineNet, layer1, layer2, layer1Weights, layer2Weights,
         Layer.inputDim, Layer.outputDim, layer1Bias]

/-! ## Input Domain and Output Bounds -/

/-- Helper to create dyadic interval -/
def mkInterval (lo hi : ℚ) (h : lo ≤ hi := by norm_num) (prec : Int := -53) : IntervalDyadic :=
  IntervalDyadic.ofIntervalRat ⟨lo, hi, h⟩ prec

/-- Input domain: [0, π] where we use π ≈ 355/113 (more accurate than 22/7) -/
def inputDomain : IntervalVector := [mkInterval 0 (355/113)]

/-- Computed output bounds for the entire input domain -/
def outputBounds : IntervalVector :=
  TwoLayerNet.forwardInterval sineNet inputDomain (-53)

-- Evaluate to see the concrete bounds
#eval outputBounds.map (fun I => (I.lo.toRat, I.hi.toRat))

/-! ## Main Verification Theorem -/

/-- Membership in mkInterval -/
theorem mem_mkInterval {x : ℝ} {lo hi : ℚ} (hle : lo ≤ hi)
    (hx : (lo : ℝ) ≤ x ∧ x ≤ (hi : ℝ)) (prec : Int) (hprec : prec ≤ 0 := by norm_num) :
    x ∈ mkInterval lo hi hle prec := by
  unfold mkInterval
  apply IntervalDyadic.mem_ofIntervalRat _ prec hprec
  simp only [IntervalRat.mem_def]
  exact hx

/-- **Main Theorem**: For any x in [0, π], the network output is bounded.

This is a formal verification certificate proving that the trained neural
network's output lies within computed bounds for ALL inputs in the domain.

Unlike testing (which checks finitely many points), this is a mathematical
proof covering infinitely many inputs. -/
theorem output_bounded {x : ℝ} (hx : 0 ≤ x ∧ x ≤ (355 : ℝ) / 113) :
    ∀ i, (hi : i < min sineNet.layer2.outputDim sineNet.layer2.bias.length) →
      (TwoLayerNet.forwardReal sineNet [x])[i]'(by
        simp [TwoLayerNet.forwardReal, Layer.forwardReal_length]; omega) ∈
      outputBounds[i]'(by
        simp [outputBounds, TwoLayerNet.forwardInterval, Layer.forwardInterval_length]; omega) := by
  have hwf := sineNet_wf
  have hdim : sineNet.layer1.inputDim = inputDomain.length := by
    simp [sineNet, layer1, layer1Weights, Layer.inputDim, inputDomain]
  have hxlen : [x].length = inputDomain.length := by simp [inputDomain]
  have hmem : ∀ i, (hi : i < inputDomain.length) →
      [x][i]'(by omega) ∈ inputDomain[i]'hi := by
    intro i hi
    simp only [inputDomain, List.length_cons, List.length_nil] at hi
    match i with
    | 0 =>
      simp only [inputDomain, List.getElem_cons_zero]
      apply mem_mkInterval (by norm_num) _ (-53)
      constructor
      · simp only [Rat.cast_zero]; exact hx.1
      · simp only [Rat.cast_div, Rat.cast_ofNat]; exact hx.2
    | n + 1 => omega
  intro i hi
  have h := TwoLayerNet.mem_forwardInterval hwf hdim hxlen hmem (-53) (by norm_num) i hi
  simp only [outputBounds]
  exact h

/-!
## What This Proves

The theorem `output_bounded` establishes:

> **For every real number x with 0 ≤ x ≤ π:**
> The neural network output is contained in the computed interval bounds.

This is verified by Lean's proof checker - a mathematical certainty, not empirical testing.

### Key Point: Formal Verification vs Testing

**Testing** can only check finitely many inputs (e.g., 1000 sample points).
An adversarial input between test points could still cause unexpected behavior.

**Formal verification** proves the property holds for ALL inputs simultaneously.
The theorem `output_bounded` covers **infinitely many** real numbers in [0, π].
There is no gap - every possible input is covered by the mathematical proof.

This is the power of formal verification for ML safety: not "we tested it thoroughly"
but "we proved it mathematically for all inputs."

### Applications

- **Safety certification**: Prove controller outputs stay in safe range
- **Adversarial robustness**: Bound how much outputs can change
- **Regulatory compliance**: Provide formal guarantees for ML systems
-/

end LeanBound.Examples.ML.SineApprox