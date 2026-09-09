import LeanCert.Engine.DirichletGaussian
import Mathlib.Util.AssertNoSorry

open LeanCert.Analysis.DirichletGaussian
open LeanCert.Engine.DirichletGaussian
open Filter
open scoped Topology

-- Symbolic results: no numerical search and no assumption on a zero's location.
example {a : ℝ} (ha : 0 < a) (s : ℂ) : Summable (term a s) := summable_term ha s
example {a : ℝ} (ha : 0 < a) : Differentiable ℂ (series a) := entire_series ha
example {a : ℝ} (ha : 0 < a) (s : ℂ) :
    ‖series a s‖ ≤ Real.exp ((2+1/a)*(1+‖s‖)^2) := growth_bound ha s
example {t : ℝ} (ht : t < 0) : ∃ s : ℂ, series (-t/4) s = 0 :=
  negative_time_exists_zero ht
example : ∃ s : ℂ, series (1/4) s = 0 := exists_zero (by norm_num)
example {a : ℝ} (ha : 0 < a) :
    Tendsto (fun x : ℝ => series a (x : ℂ)) atTop (𝓝 1) := tendsto_series_real ha

-- Actual rational evaluation, kernel reduction (not native_decide).
example : checkTail 1 0 15 4 = true := by decide +kernel
example : checkTail 0 0 15 4 = false := by decide +kernel
example : checkTail (-1) 0 15 4 = false := by decide +kernel
example : checkTail 1 0 0 4 = false := by decide +kernel
example : checkTail 1 100 15 4 = false := by decide +kernel

example {s : ℂ} (hs : 0 ≤ s.re) :
    ‖series 1 s - partialSum 1 15 s‖ ≤ 1/8 := by
  have h := certified_tail (a := 1) (R := 0) (N := 15) (precision := 4)
    (by decide +kernel) (s := s) (by simpa using hs)
  norm_num at h ⊢
  exact h

-- An empty head and an arbitrary left boundary are also covered analytically.
example {s : ℂ} (hs : 2 ≤ s.re) : ‖series 1 s‖ ≤ 2 := by
  simpa [partialSum] using tail_bound (a := 1) (R := -2) (by norm_num) 0
    (by norm_num) (s := s) (by simpa using hs)

assert_no_sorry exists_zero
assert_no_sorry negative_time_exists_zero
assert_no_sorry certified_tail
assert_no_sorry certified_disk
