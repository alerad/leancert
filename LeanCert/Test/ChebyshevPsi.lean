module

public import LeanCert.Engine.Chebyshev.Psi

public section

open LeanCert.Engine.Chebyshev.Psi

-- Quick test: incremental checker (O(N), fast)
example : checkAllPsiLeMulWith 11723 (111 / 100) 20 = true := by native_decide

-- Eval the incremental checker result
#eval checkAllPsiLeMulWith 11723 (111 / 100) 20
