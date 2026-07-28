import LeanCert.Tactic
import LeanCert.ML.Distillation
import LeanCert.ML.Attention
import LeanCert.ML.LayerNormAffine
import LeanCert.ML.Optimized
import LeanCert.ML.Symbolic.ReLU
import LeanCert.ML.Symbolic.Sigmoid

/-!
# Documentation smoke tests

Copy-pasteable declarations used by the public documentation belong here (or
in another compiled example). Schematic snippets must be labelled as such.
-/

open LeanCert.Core
open LeanCert.ML
open LeanCert.ML.Distillation
open LeanCert.ML.Optimized

def docsNet : TwoLayerNet := {
  layer1 := { weights := [[1, -1], [0, 1]], bias := [0, 0] }
  layer2 := { weights := [[1, 1]], bias := [0] }
}

def docsInputBox : IntervalVector := [
  IntervalDyadic.ofIntervalRat ⟨-1, 1, by norm_num⟩ (-53),
  IntervalDyadic.ofIntervalRat ⟨0, 1, by norm_num⟩ (-53)
]

#check docsNet.forwardInterval docsInputBox

example : ∀ x ∈ Set.Icc (0 : ℝ) 1, Real.sin x ≤ 1 := by
  leancert

example : ∃ x ∈ Set.Icc (1 : ℝ) 2, x ^ 2 = 2 := by
  interval_roots

#check Layer.mem_forwardInterval
#check TwoLayerNet.mem_forwardInterval
#check IntervalVector.relu
#check IntervalVector.mem_relu
#check IntervalVector.sigmoid
#check IntervalVector.mem_sigmoid
#check LeanCert.ML.Symbolic.relu_relaxation_sound
#check LeanCert.ML.Symbolic.sigmoid_relaxation_sound
#check LeanCert.ML.Transformer.geluInterval
#check LeanCert.ML.Transformer.mem_geluInterval
#check LeanCert.ML.Attention.mem_scaledDotProductAttention
#check LeanCert.ML.Transformer.LayerNormParams.forwardAffine
#check LeanCert.ML.Transformer.mem_forwardAffine
#check LeanCert.ML.Transformer.TransformerBlock.forwardIntervalTight
#check QuantizedLayer.forwardQuantized
#check QuantizedLayer.forwardQuantized_sound
#check SequentialNet
#check checkEquivalence
#check verify_equivalence
