import LeanCert.Engine.ChebyshevPsi

open LeanCert.Engine.ChebyshevPsi

-- Quick test: incremental checker (O(N), fast)
example : allPsiBoundsHold 11723 20 = true := by native_decide

-- Eval the incremental checker result
#eval allPsiBoundsHold 11723 20
