import LeanCert.API.MatrixPositivity

/-! # Narrow public matrix positivity API contract -/

open LeanCert.Engine LeanCert.Validity

#check @LDLTCertificate
#check @GramCertificate
#check @PSDCertificate
#check @matrixPSDCheck
#check @matrixPosDefCheck
#check @verify_matrix_posSemidef
#check @verify_matrix_posDef
#check @LeanCert.gramMatrix
#check @LeanCert.gramMatrix_posSemidef
#check @LeanCert.regularizedGramMatrix
#check @LeanCert.regularizedGramMatrix_posDef
