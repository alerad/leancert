import LeanCert

open LeanCert.Core
open LeanCert.Engine
open LeanCert.Engine.Optimization
open LeanCert.Validity.GlobalOpt

-- Box domains for global optimization.
def I01 : IntervalRat := ⟨0, 1, by norm_num⟩
def B01_2D : Box := [I01, I01]
def B01_3D : Box := [I01, I01, I01]

-- Multivariate stress tests via global optimization theorems.
theorem stress_opt_2d_sum_sq :
    ∀ ρ, Box.envMem ρ B01_2D → (∀ i, i ≥ B01_2D.length → ρ i = 0) →
      Expr.eval ρ (Expr.add (Expr.mul (Expr.var 0) (Expr.var 0))
                           (Expr.mul (Expr.var 1) (Expr.var 1))) ≤ (2 : ℚ) :=
  verify_global_upper_bound
    (Expr.add (Expr.mul (Expr.var 0) (Expr.var 0)) (Expr.mul (Expr.var 1) (Expr.var 1)))
    (ADSupported.add
      (ADSupported.mul (ADSupported.var 0) (ADSupported.var 0))
      (ADSupported.mul (ADSupported.var 1) (ADSupported.var 1)))
    B01_2D 2 ⟨1500, 1/1000, false, 10⟩
    (by native_decide)

theorem stress_opt_2d_xy_nonneg :
    ∀ ρ, Box.envMem ρ B01_2D → (∀ i, i ≥ B01_2D.length → ρ i = 0) →
      (0 : ℚ) ≤ Expr.eval ρ (Expr.mul (Expr.var 0) (Expr.var 1)) :=
  verify_global_lower_bound
    (Expr.mul (Expr.var 0) (Expr.var 1))
    (ADSupported.mul (ADSupported.var 0) (ADSupported.var 1))
    B01_2D 0 ⟨1500, 1/1000, false, 10⟩
    (by native_decide)

theorem stress_opt_3d_sum_sq :
    ∀ ρ, Box.envMem ρ B01_3D → (∀ i, i ≥ B01_3D.length → ρ i = 0) →
      Expr.eval ρ
        (Expr.add (Expr.add (Expr.mul (Expr.var 0) (Expr.var 0))
                             (Expr.mul (Expr.var 1) (Expr.var 1)))
                  (Expr.mul (Expr.var 2) (Expr.var 2))) ≤ (3 : ℚ) :=
  verify_global_upper_bound
    (Expr.add (Expr.add (Expr.mul (Expr.var 0) (Expr.var 0)) (Expr.mul (Expr.var 1) (Expr.var 1)))
              (Expr.mul (Expr.var 2) (Expr.var 2)))
    (ADSupported.add
      (ADSupported.add
        (ADSupported.mul (ADSupported.var 0) (ADSupported.var 0))
        (ADSupported.mul (ADSupported.var 1) (ADSupported.var 1)))
      (ADSupported.mul (ADSupported.var 2) (ADSupported.var 2)))
    B01_3D 3 ⟨2000, 1/1000, false, 10⟩
    (by native_decide)
