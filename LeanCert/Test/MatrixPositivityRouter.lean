import LeanCert.Tactic.LeanCert
import LeanCert.Tactic.MatrixPositivity
import LeanCert.Test.MatrixPositivity

open LeanCert.Engine
open LeanCert.Test.MatrixPositivity

example : (ratCastMatrix positiveDefiniteTwo).PosDef := by
  leancert

example : (ratCastMatrix rankOne).PosSemidef := by
  leancert

set_option leancert.trust "kernel" in
example : (ratCastMatrix positiveDefiniteTwo).PosDef := by
  leancert
