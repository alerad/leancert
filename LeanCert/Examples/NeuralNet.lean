/-
Copyright (c) 2025 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.ML.Network

set_option linter.unnecessarySeqFocus false

/-!
# Neural Network Verification Example

This file demonstrates verified neural network robustness using LeanCert's
interval arithmetic infrastructure.

## Example: Verifying a 2→2→1 Network

We define a small neural network and prove that for inputs in a bounded region,
the output remains within specified bounds. This is the foundation for
certified adversarial robustness.

## Main results

* `exampleNet` - A simple 2→2→1 ReLU network
* `robustness_certificate` - Proof that output stays bounded for bounded inputs
-/

namespace LeanCert.Examples.NeuralNet

open LeanCert.Core
open LeanCert.ML
open IntervalVector

/-! ### Network Definition -/

/-- First layer: 2 inputs → 2 outputs
    W1 = [[1, -1], [1, 1]], b1 = [0, 0]
    This computes [x - y, x + y] -/
def layer1 : Layer where
  weights := [[1, -1], [1, 1]]
  bias := [0, 0]

/-- Second layer: 2 inputs → 1 output
    W2 = [[1, 1]], b2 = [0]
    This computes (x - y) + (x + y) = 2x after ReLU -/
def layer2 : Layer where
  weights := [[1, 1]]
  bias := [0]

/-- The example two-layer network -/
def exampleNet : TwoLayerNet where
  layer1 := layer1
  layer2 := layer2

/-! ### Well-formedness Proofs -/

theorem layer1_wf : layer1.WellFormed := by
  constructor
  · intro row hrow
    simp only [layer1, Layer.inputDim] at *
    fin_cases hrow <;> rfl
  · rfl

theorem layer2_wf : layer2.WellFormed := by
  constructor
  · intro row hrow
    simp only [layer2, Layer.inputDim] at *
    fin_cases hrow <;> rfl
  · rfl

theorem exampleNet_wf : exampleNet.WellFormed := by
  constructor
  · exact layer1_wf
  constructor
  · exact layer2_wf
  · simp only [exampleNet, layer1, layer2, Layer.inputDim, Layer.outputDim]
    rfl

/-! ### Input Region Definition -/

/-- Create an interval around a center point with radius ε -/
def intervalAround (center : ℚ) (eps : ℚ) (heps : 0 ≤ eps := by norm_num) (prec : Int := -53) : IntervalDyadic :=
  IntervalDyadic.ofIntervalRat ⟨center - eps, center + eps, by linarith⟩ prec

/-- Input region: x ∈ [0.4, 0.6], y ∈ [0.4, 0.6]
    This represents inputs near (0.5, 0.5) with perturbation ε = 0.1 -/
def inputRegion : IntervalVector :=
  [intervalAround (1/2) (1/10) (by norm_num), intervalAround (1/2) (1/10) (by norm_num)]

/-! ### Verification -/

/-- Compute the output interval for the example network -/
def outputInterval : IntervalVector :=
  TwoLayerNet.forwardInterval exampleNet inputRegion (-53)

/-! ### Robustness Certificate -/

/-- Helper: membership in intervalAround -/
theorem mem_intervalAround {x : ℝ} {center eps : ℚ} (heps : 0 < eps)
    (hx : |x - center| ≤ eps) (prec : Int) (hprec : prec ≤ 0 := by norm_num) :
    x ∈ intervalAround center eps (le_of_lt heps) prec := by
  unfold intervalAround
  apply IntervalDyadic.mem_ofIntervalRat _ prec hprec
  simp only [IntervalRat.mem_def]
  rw [abs_le] at hx
  constructor
  · -- x ≥ center - eps
    have h1 : -(eps : ℝ) ≤ x - (center : ℝ) := hx.1
    have h2 : (center : ℝ) - (eps : ℝ) ≤ x := by linarith
    simp only [Rat.cast_sub]
    exact h2
  · -- x ≤ center + eps
    have h1 : x - (center : ℝ) ≤ (eps : ℝ) := hx.2
    have h2 : x ≤ (center : ℝ) + (eps : ℝ) := by linarith
    simp only [Rat.cast_add]
    exact h2

/-- Main robustness theorem: For any real input (x, y) within ε=0.1 of (0.5, 0.5),
    the network output is contained in the computed output interval.

    This is a **verified robustness certificate**: it proves that small
    perturbations to the input cannot cause the output to leave the computed bounds. -/
theorem robustness_certificate {x y : ℝ}
    (hx : |x - (1/2 : ℚ)| ≤ (1/10 : ℚ)) (hy : |y - (1/2 : ℚ)| ≤ (1/10 : ℚ)) :
    ∀ i, (hi : i < min exampleNet.layer2.outputDim exampleNet.layer2.bias.length) →
      (TwoLayerNet.forwardReal exampleNet [x, y])[i]'(by
        simp [TwoLayerNet.forwardReal, Layer.forwardReal_length]; omega) ∈
      outputInterval[i]'(by
        simp [outputInterval, TwoLayerNet.forwardInterval, Layer.forwardInterval_length]; omega) := by
  -- Apply the soundness theorem
  have hwf := exampleNet_wf
  have hdim : exampleNet.layer1.inputDim = inputRegion.length := by
    simp [exampleNet, layer1, Layer.inputDim, inputRegion]
  have hxlen : [x, y].length = inputRegion.length := by simp [inputRegion]
  have hmem : ∀ i, (hi : i < inputRegion.length) →
      [x, y][i]'(by omega) ∈ inputRegion[i]'hi := by
    intro i hi
    simp only [inputRegion, List.length_cons, List.length_nil] at hi
    match i with
    | 0 =>
      simp only [inputRegion, List.getElem_cons_zero]
      exact mem_intervalAround (by norm_num : (0 : ℚ) < 1/10) hx (-53) (by norm_num)
    | 1 =>
      simp only [inputRegion, List.getElem_cons_succ, List.getElem_cons_zero]
      exact mem_intervalAround (by norm_num : (0 : ℚ) < 1/10) hy (-53) (by norm_num)
    | n + 2 => omega
  intro i hi
  have h := TwoLayerNet.mem_forwardInterval hwf hdim hxlen hmem (-53) (by norm_num) i hi
  simp only [outputInterval]
  exact h

/-! ### Interpretation

The theorem `robustness_certificate` proves that for ANY real values x, y
satisfying |x - 0.5| ≤ 0.1 and |y - 0.5| ≤ 0.1, the network output is
guaranteed to be within the computed bounds.

This is a **formal verification** of robustness - not just an empirical test,
but a mathematical proof that holds for ALL inputs in the region.

Applications:
- Certified defense against adversarial examples
- Safety verification for neural network controllers
- Proving bounds on neural network outputs for formal verification
-/

end LeanCert.Examples.NeuralNet
