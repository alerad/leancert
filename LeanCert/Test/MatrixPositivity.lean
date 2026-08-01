import LeanCert.Engine.MatrixPositivity
import LeanCert.Validity.MatrixPositivity
import LeanCert.LinearAlgebra.Gram

open LeanCert.Engine LeanCert.Validity

namespace LeanCert.Test.MatrixPositivity

def positiveDefiniteTwo : Matrix (Fin 2) (Fin 2) ℚ :=
  !![2, 1; 1, 2]

def positiveDefiniteTwoCertificate : LDLTCertificate 2 where
  lower := !![1, 0; 1 / 2, 1]
  diagonal := ![2, 3 / 2]

example : matrixPosDefCheck positiveDefiniteTwo positiveDefiniteTwoCertificate = true := by
  native_decide

example : (ratCastMatrix positiveDefiniteTwo).PosDef := by
  exact verify_matrix_posDef positiveDefiniteTwo positiveDefiniteTwoCertificate (by native_decide)

def rankOne : Matrix (Fin 2) (Fin 2) ℚ :=
  !![1, 1; 1, 1]

def rankOneCertificate : LDLTCertificate 2 where
  lower := !![1, 0; 1, 1]
  diagonal := ![1, 0]

example : matrixPSDCheck rankOne (.ldlt rankOneCertificate) = true := by
  native_decide

example : (ratCastMatrix rankOne).PosSemidef := by
  exact verify_matrix_posSemidef rankOne (.ldlt rankOneCertificate) (by native_decide)

def rectangularGram : GramCertificate 2 where
  rows := 1
  factor := !![1, 1]

example : matrixPSDCheck rankOne (.gram rectangularGram) = true := by
  native_decide

example : matrixPosDefCheck rankOne rankOneCertificate = false := by
  native_decide

def indefinite : Matrix (Fin 2) (Fin 2) ℚ :=
  !![1, 2; 2, 1]

def indefiniteCertificate : LDLTCertificate 2 where
  lower := !![1, 0; 2, 1]
  diagonal := ![1, -3]

example : matrixPSDCheck indefinite (.ldlt indefiniteCertificate) = false := by
  native_decide

def nonsymmetric : Matrix (Fin 2) (Fin 2) ℚ :=
  !![1, 0; 1, 1]

example : matrixPSDCheck nonsymmetric (.gram rectangularGram) = false := by
  native_decide

def obstructedZeroPivot : Matrix (Fin 2) (Fin 2) ℚ :=
  !![0, 1; 1, 0]

example : (discoverMatrixPositivity obstructedZeroPivot).report.failure =
    some (.zeroPivotObstruction 0 1) := by
  native_decide

example :
    (discoverMatrixPositivity positiveDefiniteTwo).report.diagonal = [2, 3 / 2] := by
  native_decide

example :
    (discoverMatrixPositivity rankOne).report.zeroPivots = 1 := by
  native_decide

example :
    (discoverMatrixPositivity indefinite).report.negativePivots = 1 := by
  native_decide

example :
    (discoverMatrixPositivity positiveDefiniteTwo { maxDimension := 1 }).certificate.isNone := by
  native_decide

noncomputable def featureTable : Matrix (Fin 2) (Fin 1) ℝ :=
  !![1; 2]

example : (LeanCert.gramMatrix featureTable).PosSemidef :=
  LeanCert.gramMatrix_posSemidef featureTable

example :
    (LeanCert.regularizedGramMatrix featureTable (fun _ => 1)).PosDef := by
  exact LeanCert.regularizedGramMatrix_posDef featureTable (fun _ => 1) (by
    intro i
    norm_num)

end LeanCert.Test.MatrixPositivity
