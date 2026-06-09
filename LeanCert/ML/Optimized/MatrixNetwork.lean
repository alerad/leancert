/-
Copyright (c) 2025 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.ML.Network
import LeanCert.ML.Optimized.Matrix
import LeanCert.ML.Optimized.QuantizedLayer

/-!
# Matrix-Based Network Operations

This module connects the optimized `IntervalMatrix` infrastructure with the
neural network layer definitions, enabling:

1. **Batch Processing**: Forward pass on multiple inputs simultaneously
2. **Attention Mechanism**: Q × K^T computation for Transformer verification
3. **Efficient Layer Application**: Using quantized integer arithmetic

## Key Definitions

* `toIntervalMatrix` - Convert weight matrix to IntervalMatrix format
* `batchForward` - Apply layer to multiple inputs (batch dimension)
* `attentionScores` - Compute Q × K^T for self-attention

## Design Notes

The `IntervalMatrix` uses Structure-of-Arrays layout for cache efficiency.
For Transformer verification, the key operations are:
- Linear projections (matmul with weight matrices)
- Attention score computation (Q × K^T)
- Softmax bounds (separate module)
-/

namespace LeanCert.ML.Optimized

open LeanCert.Core
open LeanCert.ML

/-! ### Conversion Functions -/

/-- Convert a rational weight matrix (List of Lists) to IntMatrix with given exponent.
    Each rational q is converted to an integer q * 2^(-exp) (rounded). -/
def rationalToIntMatrix (rows cols : Nat) (weights : List (List ℚ)) (exp : Int) : IntMatrix rows cols :=
  IntMatrix.ofFn fun i j =>
    let row := weights.getD i []
    let q := row.getD j 0
    -- Scale by 2^(-exp) and round to nearest integer
    let scaled := q * (2 : ℚ) ^ (-exp)
    scaled.floor

/-- Convert Layer weights to IntervalMatrix (point intervals).
    Useful for propagating through linear layers with matrix multiply. -/
def layerToIntervalMatrix (l : Layer) (exp : Int) : IntervalMatrix l.outputDim l.inputDim :=
  let intMat := rationalToIntMatrix l.outputDim l.inputDim l.weights exp
  -- For exact weights, lo = hi (point interval)
  ⟨intMat, intMat⟩

/-! ### Batch Forward Pass -/

/-- A batch of inputs represented as an IntervalMatrix.
    Each column is one input vector, rows are features.
    Shape: (input_dim, batch_size) -/
abbrev InputBatch (inputDim batchSize : Nat) := IntervalMatrix inputDim batchSize

/-- A batch of outputs represented as an IntervalMatrix.
    Shape: (output_dim, batch_size) -/
abbrev OutputBatch (outputDim batchSize : Nat) := IntervalMatrix outputDim batchSize

/-- Apply weight matrix to a batch of inputs: W × X where
    W : (output_dim, input_dim) and X : (input_dim, batch_size)
    Result: (output_dim, batch_size) -/
def batchLinear {outDim inDim batchSize : Nat}
    (W : IntervalMatrix outDim inDim)
    (X : InputBatch inDim batchSize) :
    OutputBatch outDim batchSize :=
  W.matmul X

/-! ### Attention Mechanism Support -/

/-- Compute attention scores: Q × K^T
    Q : (seq_len, d_k) - Query matrix
    K : (seq_len, d_k) - Key matrix
    Result: (seq_len, seq_len) - Attention score matrix -/
def attentionScores {seqLen dK : Nat}
    (Q K : IntervalMatrix seqLen dK) :
    IntervalMatrix seqLen seqLen :=
  Q.matmul K.transpose

/-- Structure for Multi-Head Attention parameters -/
structure AttentionParams (dModel numHeads : Nat) where
  /-- Query projection weights (dModel, dModel) -/
  wQ : IntervalMatrix dModel dModel
  /-- Key projection weights (dModel, dModel) -/
  wK : IntervalMatrix dModel dModel
  /-- Value projection weights (dModel, dModel) -/
  wV : IntervalMatrix dModel dModel
  /-- Output projection weights (dModel, dModel) -/
  wO : IntervalMatrix dModel dModel

/-- Project input to Q, K, V matrices.
    Input X : (seq_len, d_model)
    Returns (Q, K, V) each of shape (seq_len, d_model) -/
def projectQKV {seqLen dModel : Nat}
    (X : IntervalMatrix seqLen dModel)
    (params : AttentionParams dModel numHeads) :
    IntervalMatrix seqLen dModel × IntervalMatrix seqLen dModel × IntervalMatrix seqLen dModel :=
  let Q := X.matmul params.wQ.transpose
  let K := X.matmul params.wK.transpose
  let V := X.matmul params.wV.transpose
  (Q, K, V)

/-! ### ReLU for Matrices -/

/-- Element-wise ReLU on an IntMatrix: max(0, x) -/
def reluIntMatrix {r c : Nat} (M : IntMatrix r c) : IntMatrix r c :=
  IntMatrix.ofFn fun i j => max 0 (M.get i j i.isLt j.isLt)

/-- Element-wise ReLU on IntervalMatrix.
    For interval [lo, hi]: ReLU([lo, hi]) = [max(0, lo), max(0, hi)] -/
def reluIntervalMatrix {r c : Nat} (M : IntervalMatrix r c) : IntervalMatrix r c :=
  ⟨reluIntMatrix M.lo, reluIntMatrix M.hi⟩

/-! ### Bias Addition for Matrices -/

/-- Add bias vector to each column of a matrix.
    M : (out_dim, batch_size), bias : out_dim vector
    Result: M[i,j] + bias[i] for all i,j -/
def addBiasMatrix {outDim batchSize : Nat}
    (M : IntervalMatrix outDim batchSize)
    (bias_lo bias_hi : Fin outDim → Int) :
    IntervalMatrix outDim batchSize :=
  IntervalMatrix.ofFn fun i j =>
    let (m_lo, m_hi) := M.getBounds i j i.isLt j.isLt
    (m_lo + bias_lo i, m_hi + bias_hi i)

/-! ### Full Layer Forward (Matrix version) -/

/-- Forward pass through a layer with batch input.
    Computes ReLU(W × X + b) where X is a batch. -/
def layerForwardBatch {inDim outDim batchSize : Nat}
    (W : IntervalMatrix outDim inDim)
    (bias_lo bias_hi : Fin outDim → Int)
    (X : InputBatch inDim batchSize) :
    OutputBatch outDim batchSize :=
  let linear := W.matmul X
  let withBias := addBiasMatrix linear bias_lo bias_hi
  reluIntervalMatrix withBias

/-! ### Soundness (Placeholder) -/

/-- Soundness of batch linear transformation -/
theorem mem_batchLinear {outDim inDim batchSize : Nat}
    (W : IntervalMatrix outDim inDim)
    (X : InputBatch inDim batchSize)
    (W_real : Matrix (Fin outDim) (Fin inDim) ℝ)
    (X_real : Matrix (Fin inDim) (Fin batchSize) ℝ)
    (exp : Int)
    (hW : W.mem exp W_real)
    (hX : X.mem exp X_real) :
    (batchLinear W X).mem (exp + exp) (W_real * X_real) :=
  mem_matmul W X W_real X_real exp hW hX

/-- Soundness of attention score computation -/
theorem mem_attentionScores {seqLen dK : Nat}
    (Q K : IntervalMatrix seqLen dK)
    (Q_real K_real : Matrix (Fin seqLen) (Fin dK) ℝ)
    (exp : Int)
    (hQ : Q.mem exp Q_real)
    (hK : K.mem exp K_real) :
    (attentionScores Q K).mem (exp + exp) (Q_real * K_real.transpose) := by
  unfold attentionScores
  -- K.transpose preserves membership
  have hKT := mem_transpose K exp K_real hK
  -- Apply matrix multiplication soundness
  exact mem_matmul Q K.transpose Q_real K_real.transpose exp hQ hKT

end LeanCert.ML.Optimized
