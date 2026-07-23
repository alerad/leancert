import LeanCert.Meta.ToExpr
import LeanCert.Tactic.IntervalAuto

-- Reflection smoke tests: these fail to compile if reification cannot parse the form.
#leancert_reflect (fun x : Real => x + 1)
#leancert_reflect (fun x : Real => x - 1)
#leancert_reflect (fun x : Real => x / 2)
#leancert_reflect (fun x : Real => abs x)
#leancert_reflect (fun x : Real => x ^ ((1 : Real) / 2))
#leancert_reflect (fun x : Real => x ^ ((2 : Real)⁻¹))
#leancert_reflect (fun x : Real => x ^ ((3 : Real) / 2))
#leancert_reflect (fun x : Real => x ^ (1.5 : Real))
#leancert_reflect (fun x : Real => x ^ ((5 : Real) / 2))
#leancert_reflect (fun x : Real => x ^ ((-1 : Real) / 2))
#leancert_reflect (fun x : Real => x ^ ((-3 : Real) / 2))
#leancert_reflect (fun x : Real => x ^ ((-2 : Real)))
#leancert_reflect (fun x : Real => x ^ ((1 : Real) / 3))
#leancert_reflect (fun x : Real => x ^ ((2 : Real) / 3))
#leancert_reflect (fun x : Real => x ^ ((1 : Real) / 5))
#leancert_reflect (fun x : Real => x ^ ((-2 : Real) / 3))
#leancert_reflect (fun x : Real => Real.sinh x + Real.cosh x + Real.tanh x)
#leancert_reflect (fun x : Real => max x (1 / 2 : Real))
#leancert_reflect (fun x : Real => min x (1 / 2 : Real))
#leancert_reflect (fun x : Real => x + Real.pi)
#leancert_reflect (fun x : Real => x + Real.eulerMascheroniConstant)
#leancert_reflect (fun x : Real => x + ((-2 : Int) : Real) + ((3 / 7 : Rat) : Real))

theorem reify_norm_sub_div :
    ∀ x ∈ Set.Icc (1 : Real) 2, x - x / 2 ≤ (2 : Rat) := by
  certify_bound

theorem reify_norm_casts :
    ∀ x ∈ Set.Icc (0 : Real) 1, x + ((1 : Nat) : Real) ≤ (2 : Rat) := by
  certify_bound

theorem reify_norm_max :
    ∀ x ∈ Set.Icc (0 : Real) 1, max x (1 / 2 : Real) ≤ (2 : Rat) := by
  certify_bound

theorem reify_norm_min :
    ∀ x ∈ Set.Icc (0 : Real) 1, (-1 : Rat) ≤ min x (1 / 2 : Real) := by
  certify_bound
theorem reify_rpow_thirds_bound :
    ∀ x ∈ Set.Icc (2 : Real) 3, x ^ ((1 : Real) / 3) ≤ (2 : Rat) := by
  certify_bound

theorem reify_rpow_neg_thirds_bound :
    ∀ x ∈ Set.Icc (2 : Real) 3, x ^ ((-2 : Real) / 3) ≤ (1 : Rat) := by
  certify_bound

theorem reify_named_const_pi_bound :
    ∀ x ∈ Set.Icc (0 : Real) 1, x + Real.pi ≤ (5 : Rat) := by
  certify_bound
