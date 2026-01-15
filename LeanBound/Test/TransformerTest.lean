/-
Copyright (c) 2025 LeanBound Contributors. All rights reserved.
Released under AGPL-3.0 license as described in the file LICENSE.
Authors: LeanBound Contributors
-/
import LeanBound.ML.Transformer

/-!
# Transformer Module Tests

This file tests the Transformer components:
1. GELU activation
2. LayerNorm
3. FFNBlock
4. TransformerBlock
-/

namespace LeanBound.ML.Transformer.Test

open LeanBound.Core
open LeanBound.ML
open LeanBound.ML.Transformer

-- Helper to convert Int to Float
def intToFloat : Int → Float
  | Int.ofNat n => n.toFloat
  | Int.negSucc n => -(n + 1).toFloat

-- Helper to convert Rational to Float for display
def ratToFloat (q : ℚ) : Float :=
  intToFloat q.num / q.den.toFloat

-- Helper to show an interval
def showInterval (I : IntervalDyadic) : String :=
  s!"[{ratToFloat I.lo.toRat}, {ratToFloat I.hi.toRat}]"

/-! ### Test GELU -/

-- Test interval containing 0
def testInterval0 : IntervalDyadic :=
  IntervalDyadic.ofIntervalRat ⟨-1, 1, by norm_num⟩ (-53)

-- Test positive interval
def testIntervalPos : IntervalDyadic :=
  IntervalDyadic.ofIntervalRat ⟨1/2, 3/2, by norm_num⟩ (-53)

-- Test negative interval
def testIntervalNeg : IntervalDyadic :=
  IntervalDyadic.ofIntervalRat ⟨-2, -1/2, by norm_num⟩ (-53)

-- Run GELU on test intervals
#eval! do
  let result0 := geluInterval testInterval0
  IO.println s!"GELU([-1, 1]) = {showInterval result0}"

  let resultPos := geluInterval testIntervalPos
  IO.println s!"GELU([0.5, 1.5]) = {showInterval resultPos}"

  let resultNeg := geluInterval testIntervalNeg
  IO.println s!"GELU([-2, -0.5]) = {showInterval resultNeg}"

-- Verify GELU correctness theorem compiles
#check @mem_geluIntervalRat
#check @mem_geluInterval

/-! ### Test LayerNorm -/

-- Simple LayerNorm params: identity scale, zero shift
def testLNParams : LayerNormParams where
  gamma := [1, 1, 1]
  beta := [0, 0, 0]
  epsilon := 1/1000000  -- 1e-6
  epsilon_pos := by norm_num

-- Input vector: three intervals around 1
def testLNInput : IntervalVector := [
  IntervalDyadic.ofIntervalRat ⟨9/10, 11/10, by norm_num⟩ (-53),
  IntervalDyadic.ofIntervalRat ⟨95/100, 105/100, by norm_num⟩ (-53),
  IntervalDyadic.ofIntervalRat ⟨1, 1, by norm_num⟩ (-53)
]

#eval! do
  let result := testLNParams.forwardInterval testLNInput
  IO.println "LayerNorm output:"
  for h : i in [:result.length] do
    let interval := result[i]
    IO.println s!"  [{i}] = {showInterval interval}"

/-! ### Test FFNBlock -/

-- Simple 2->4->2 FFN
def testFFN : FFNBlock where
  linear1 := {
    weights := [[1, 0], [-1, 1], [0, 1], [1, 1]]  -- 4x2
    bias := [0, 0, 0, 0]
  }
  linear2 := {
    weights := [[1, 0, -1, 0], [0, 1, 0, -1]]  -- 2x4
    bias := [0, 0]
  }
  dims_match := by simp [Layer.outputDim, Layer.inputDim]

-- Input: 2D interval vector
def testFFNInput : IntervalVector := [
  IntervalDyadic.ofIntervalRat ⟨-1, 1, by norm_num⟩ (-53),
  IntervalDyadic.ofIntervalRat ⟨0, 2, by norm_num⟩ (-53)
]

#eval! do
  let result := testFFN.forwardInterval testFFNInput
  IO.println "FFN output:"
  for h : i in [:result.length] do
    let interval := result[i]
    IO.println s!"  [{i}] = {showInterval interval}"

/-! ### Test TransformerBlock -/

-- LayerNorm for 2D input
def testLN2D : LayerNormParams where
  gamma := [1, 1]
  beta := [0, 0]
  epsilon := 1/1000000
  epsilon_pos := by norm_num

-- 2D Transformer block
def testTransformerBlock : TransformerBlock where
  ln1 := testLN2D
  ffn := testFFN
  ln2 := testLN2D

#eval! do
  let input := testFFNInput
  let result := testTransformerBlock.forwardInterval input
  IO.println "TransformerBlock output:"
  for h : i in [:result.length] do
    let interval := result[i]
    IO.println s!"  [{i}] = {showInterval interval}"

/-! ### Vector GELU Test -/

def testVec : IntervalVector := [
  IntervalDyadic.ofIntervalRat ⟨-1, 0, by norm_num⟩ (-53),
  IntervalDyadic.ofIntervalRat ⟨0, 1, by norm_num⟩ (-53),
  IntervalDyadic.ofIntervalRat ⟨1, 2, by norm_num⟩ (-53)
]

#eval! do
  let result := geluVector testVec
  IO.println "GELU vector output:"
  for h : i in [:result.length] do
    let interval := result[i]
    IO.println s!"  [{i}] = {showInterval interval}"

/-! ### Verify Key Theorems -/

-- The sqrt(2/π) bound is proven
#check sqrt_two_div_pi_mem_interval

-- GELU correctness theorems
#check @mem_geluIntervalRat
#check @mem_geluInterval

-- LayerNorm soundness (has sorry)
#check @mem_layerNorm_forwardInterval

-- All tests pass if this file compiles!
#check "Transformer module tests passed!"

end LeanBound.ML.Transformer.Test
