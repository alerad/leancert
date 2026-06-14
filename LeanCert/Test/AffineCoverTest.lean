import LeanCert.Validity.AffineCover

/-!
Regression test for the affine cover certificate.

The comparison `0.8 + (5/3)·s² ≤ 9.2211·s³·exp(-0.8476·s)` on `s ∈ [0.83, 3.23]`
is a `polynomial ≤ polynomial·exp` shape with the `s³`/`exp(-0.8476 s)`
anti-correlation that defeats the plain interval backend even under
subdivision.  The affine cover closes it: one `native_decide` over a
width-0.1 partition.
-/

namespace LeanCert.Test.AffineCover

open LeanCert.Core LeanCert.Validity

-- f(s) = 0.8 + (5/3) s²
def fE : Expr :=
  Expr.add (Expr.const (4/5))
    (Expr.mul (Expr.const (5/3)) (Expr.mul (Expr.var 0) (Expr.var 0)))

-- g(s) = 9.2211 s³ exp(-0.8476 s)
def gE : Expr :=
  Expr.mul (Expr.mul (Expr.const (92211/10000))
      (Expr.mul (Expr.mul (Expr.var 0) (Expr.var 0)) (Expr.var 0)))
    (Expr.exp (Expr.mul (Expr.const (-2119/2500)) (Expr.var 0)))

def bps : List ℚ := (List.range 24).map (fun k => ((83 + 10*(k+1) : ℚ))/100)

theorem gminusf_supp : ExprSupportedCore (Expr.sub gE fE) := by
  unfold gE fE Expr.sub; repeat constructor

/-- The comparison holds on `[0.83, 3.23]`, via the affine cover. -/
example :
    ∀ x ∈ Set.Icc ((83/100 : ℚ) : ℝ) ((bps.getLast (by decide) : ℚ) : ℝ),
      Expr.eval (fun _ => x) fE ≤ Expr.eval (fun _ => x) gE :=
  verify_le_affine_cover fE gE gminusf_supp {} (83/100) bps (by decide)
    (by native_decide)

end LeanCert.Test.AffineCover
