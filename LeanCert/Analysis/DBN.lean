import LeanCert.Analysis.DBN.HeatKernel
import LeanCert.Analysis.DBN.HeatFlow
import LeanCert.Analysis.DBN.HeatRegularity
import LeanCert.Analysis.DBN.Xi
import LeanCert.Analysis.DBN.ThetaDerivatives
import LeanCert.Analysis.DBN.ThetaIntegral
import LeanCert.Analysis.DBN.XiIdentity
import LeanCert.Analysis.DBN.StripShift
import LeanCert.Analysis.DBN.HeatShift
import LeanCert.Analysis.DBN.Hadamard
import LeanCert.Analysis.DBN.CanonicalProduct
import LeanCert.Analysis.DBN.RealZeros

/-! Analytic definitions, majorants, and the unconditional real-zero theorem
at time one half for the de Bruijn–Newman heat flow.
Numerical mollifier certificates and their approximation-error transfers are
separate from this analytic endpoint and are not supplied by this module. -/
