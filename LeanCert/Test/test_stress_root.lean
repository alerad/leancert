module

public import LeanCert.Tactic.IntervalAuto

@[expose] public section

open LeanCert.Core

def I01 : IntervalRat := ⟨0, 1, by norm_num⟩
def I23 : IntervalRat := ⟨2, 3, by norm_num⟩

-- Root-finding stress tests (prove no roots in a box).
example : ∀ x ∈ I01, Expr.eval (fun _ => x) (Expr.exp (Expr.var 0)) ≠ (0 : ℝ) := by
  root_bound 15

example : ∀ x ∈ I23,
    Expr.eval (fun _ => x)
      (Expr.add (Expr.mul (Expr.var 0) (Expr.var 0)) (Expr.neg (Expr.const 2))) ≠ (0 : ℝ) := by
  root_bound
