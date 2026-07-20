import LeanCert.Examples.Krawczyk

namespace LeanCert.Test.Krawczyk

open LeanCert.Core
open LeanCert.Engine
open LeanCert.Validity
open LeanCert.Examples.Krawczyk

example : krawczykCheck system box certificate = true := by native_decide

def singularCertificate : KrawczykCert 2 where
  center := ![1, 1]
  preconditioner := 0

example : krawczykCheck system box singularCertificate = false := by native_decide

example : krawczykCheck expSystem expBox expCertificate = true := by native_decide

example : ∃ p, FinBoxMem p expBox ∧ SystemZero expSystem p := by
  apply verify_system_root_exists expSystem expBox expCertificate {}
  native_decide

example {p q : Fin 2 → ℝ}
    (hp : FinBoxMem p box ∧ SystemZero system p)
    (hq : FinBoxMem q box ∧ SystemZero system q) : p = q := by
  apply verify_system_root_unique system box certificate {} (by native_decide) hp hq

def unsupportedSystem : Fin 2 → Expr :=
  ![Expr.log (Expr.var 0), Expr.var 1]

example : krawczykCheck unsupportedSystem box certificate = false := by native_decide

def wideBox : Fin 2 → IntervalRat :=
  ![⟨0, 2, by norm_num⟩, ⟨0, 2, by norm_num⟩]

example : krawczykCheck system wideBox certificate = false := by native_decide

end LeanCert.Test.Krawczyk
