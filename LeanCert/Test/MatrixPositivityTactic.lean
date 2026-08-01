import LeanCert.Tactic.MatrixPositivity
import LeanCert.Test.MatrixPositivity

open LeanCert.Engine
open LeanCert.Test.MatrixPositivity

example : (ratCastMatrix positiveDefiniteTwo).PosDef := by
  matrix_posdef (trust := kernel) (maxDimension := 8)

example : (ratCastMatrix rankOne).PosSemidef := by
  matrix_psd

example : (ratCastMatrix positiveDefiniteTwo).PosDef := by
  matrix_posdef using positiveDefiniteTwoCertificate (trust := auto)

example : (ratCastMatrix rankOne).PosSemidef := by
  matrix_psd using (PSDCertificate.ldlt rankOneCertificate)

example : (ratCastMatrix rankOne).PosSemidef := by
  matrix_psd using (PSDCertificate.gram rectangularGram) (trust := kernel)

set_option leancert.trust "kernel" in
example : (ratCastMatrix positiveDefiniteTwo).PosDef := by
  matrix_posdef

set_option leancert.trust "native" in
example : (ratCastMatrix rankOne).PosSemidef := by
  matrix_psd

set_option leancert.trust "auto" in
example : (ratCastMatrix positiveDefiniteTwo).PosDef := by
  matrix_posdef

/- Unsupported goals restore the original target and messages. -/
example : True := by
  fail_if_success matrix_posdef
  guard_target = True
  trivial
