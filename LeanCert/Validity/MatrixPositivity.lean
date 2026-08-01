/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Engine.MatrixPositivity.Certificate

/-!
# Golden Theorems for exact matrix positivity certificates
-/

namespace LeanCert.Validity

open LeanCert.Engine

/-- A successful exact certificate check proves real positive semidefiniteness. -/
theorem verify_matrix_posSemidef {n : Nat} (matrix : Matrix (Fin n) (Fin n) ℚ)
    (certificate : PSDCertificate n) (h : matrixPSDCheck matrix certificate = true) :
    (ratCastMatrix matrix).PosSemidef :=
  matrixPSDCheck_sound matrix certificate h

/-- A successful exact LDLᵀ certificate check proves real positive definiteness. -/
theorem verify_matrix_posDef {n : Nat} (matrix : Matrix (Fin n) (Fin n) ℚ)
    (certificate : LDLTCertificate n) (h : matrixPosDefCheck matrix certificate = true) :
    (ratCastMatrix matrix).PosDef :=
  matrixPosDefCheck_sound matrix certificate h

end LeanCert.Validity
