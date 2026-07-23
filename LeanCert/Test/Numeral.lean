/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Meta.ToExpr
import LeanCert.Tactic.IntervalAuto

/-!
# Numeric Extraction Regression Tests

Smoke tests for canonical rational extraction through reification.
-/

namespace LeanCert.Test.Numeral

def myRat : ℚ := 9 / 500

#leancert_reflect (fun _x : Real => ((9 / 500 : Rat) : Real))
#leancert_reflect (fun _x : Real => (myRat : Real))
#leancert_reflect (fun x : Real => x + (((-2 : Int) : Real) + 3))
#leancert_reflect (fun x : Real => x + 2.72)
#leancert_reflect (fun x : Real => x + ((1 : Nat) : Real))

theorem interval_bound_nat_cast :
    ∀ x ∈ Set.Icc (0 : Real) 1, x + ((1 : Nat) : Real) ≤ (2 : Rat) := by
  certify_bound

end LeanCert.Test.Numeral
