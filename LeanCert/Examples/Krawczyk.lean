/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Validity.Krawczyk

/-!
# Nonlinear systems certified by Krawczyk's method

We certify the unique root of

* `x² + y - 2 = 0`
* `x + y² - 2 = 0`

inside `[9/10, 11/10]²`.  The untrusted certificate uses center `(1,1)` and
the exact inverse of the center Jacobian, `(1/3) [[2,-1],[-1,2]]`.
-/

namespace LeanCert.Examples.Krawczyk

open LeanCert.Core
open LeanCert.Engine
open LeanCert.Validity

def system : Fin 2 → Expr :=
  let x := Expr.var 0
  let y := Expr.var 1
  ![Expr.add (Expr.add (Expr.mul x x) y) (Expr.const (-2)),
    Expr.add (Expr.add x (Expr.mul y y)) (Expr.const (-2))]

def box : Fin 2 → IntervalRat :=
  ![⟨9 / 10, 11 / 10, by norm_num⟩, ⟨9 / 10, 11 / 10, by norm_num⟩]

def certificate : KrawczykCert 2 where
  center := ![1, 1]
  preconditioner := !![2 / 3, -1 / 3; -1 / 3, 2 / 3]

example : krawczykCheck system box certificate = true := by native_decide

/-- The coupled system has exactly one real root in the candidate box. -/
theorem unique_root : ∃! p, FinBoxMem p box ∧ SystemZero system p := by
  apply verify_unique_system_root system box certificate {}
  native_decide

/-! The same API handles transcendental expressions in the differentiable AD
fragment. Here it certifies the unique zero of `exp(x) - 1` near the origin. -/

def expSystem : Fin 1 → Expr :=
  ![Expr.add (Expr.exp (Expr.var 0)) (Expr.const (-1))]

def expBox : Fin 1 → IntervalRat :=
  ![⟨-1 / 10, 1 / 10, by norm_num⟩]

def expCertificate : KrawczykCert 1 where
  center := ![0]
  preconditioner := !![1]

example : krawczykCheck expSystem expBox expCertificate = true := by native_decide

/-- `exp(x) - 1` has exactly one real root in the candidate interval. -/
theorem exp_unique_root :
    ∃! p, FinBoxMem p expBox ∧ SystemZero expSystem p := by
  apply verify_unique_system_root expSystem expBox expCertificate {}
  native_decide

end LeanCert.Examples.Krawczyk
