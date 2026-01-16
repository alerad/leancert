import LeanCert

open LeanCert.Core
open LeanCert.Validity

-- e ≈ 2.7182818284590452...
-- This bound is below e; the checker should reject it even at high Taylor depth.
def I01 : IntervalRat := ⟨0, 1, by norm_num⟩
def exprExp : Expr := Expr.exp (Expr.var 0)

example :
    checkUpperBound exprExp I01 (679570457 / 250000000) { taylorDepth := 50 } = false := by
  native_decide
