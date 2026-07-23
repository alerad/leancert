/-
  Test file for Discovery Mode features
  Testing the library as an end-user would for various applications
-/
import LeanCert.Tactic.IntervalAuto
import LeanCert.Tactic.Discovery
import LeanCert.Tactic.Refute
import LeanCert.Tactic.DyadicAuto

open LeanCert.Core
open Set

/-! ## Application 1: Basic Polynomial Bounds

Simple polynomial examples that should always work
-/

section BasicPolynomials

-- x² on [0, 1]
example : ∀ x ∈ Icc (0 : ℝ) 1, x * x ≤ 1 := by
  certify_bound

example : ∀ x ∈ Icc (0 : ℝ) 1, 0 ≤ x * x := by
  certify_bound

-- x² on [-1, 1]
example : ∀ x ∈ Icc (-1 : ℝ) 1, x * x ≤ 1 := by
  certify_bound

-- x³ on [0, 1]
example : ∀ x ∈ Icc (0 : ℝ) 1, x * x * x ≤ 1 := by
  certify_bound

-- Linear: 2x + 1 on [0, 1] → [1, 3]
example : ∀ x ∈ Icc (0 : ℝ) 1, 2 * x + 1 ≤ 3 := by
  certify_bound

example : ∀ x ∈ Icc (0 : ℝ) 1, 1 ≤ 2 * x + 1 := by
  certify_bound

-- Quadratic: x² - x on [0, 1] - min at x=0.5 is -0.25
example : ∀ x ∈ Icc (0 : ℝ) 1, x * x - x ≤ 1 := by
  certify_bound

example : ∀ x ∈ Icc (0 : ℝ) 1, -1 ≤ x * x - x := by
  certify_bound

end BasicPolynomials


/-! ## Application 2: Transcendental Function Bounds

sin, cos, exp on various intervals
-/

section Transcendentals

-- sin(x) ∈ [-1, 1] always
example : ∀ x ∈ Icc (0 : ℝ) 7, Real.sin x ≤ 1 := by
  certify_bound

example : ∀ x ∈ Icc (0 : ℝ) 7, -1 ≤ Real.sin x := by
  certify_bound

-- cos(x) ∈ [-1, 1] always
example : ∀ x ∈ Icc (0 : ℝ) 7, Real.cos x ≤ 1 := by
  certify_bound

example : ∀ x ∈ Icc (0 : ℝ) 7, -1 ≤ Real.cos x := by
  certify_bound

-- exp(x) on [0, 1] → [1, e] ⊂ [1, 3]
example : ∀ x ∈ Icc (0 : ℝ) 1, Real.exp x ≤ 3 := by
  certify_bound 15

example : ∀ x ∈ Icc (0 : ℝ) 1, 1 ≤ Real.exp x := by
  certify_bound

-- exp(x) on [0, 2] → [1, e²] ⊂ [1, 8]
example : ∀ x ∈ Icc (0 : ℝ) 2, Real.exp x ≤ 8 := by
  certify_bound 15

-- tanh(x) ∈ [-1, 1]
example : ∀ x ∈ Icc (-5 : ℝ) 5, Real.tanh x ≤ 1 := by
  certify_bound

example : ∀ x ∈ Icc (-5 : ℝ) 5, -1 ≤ Real.tanh x := by
  certify_bound

-- sinh on [0, 2]
example : ∀ x ∈ Icc (0 : ℝ) 2, Real.sinh x ≤ 4 := by
  certify_bound

example : ∀ x ∈ Icc (0 : ℝ) 2, 0 ≤ Real.sinh x := by
  certify_bound

-- cosh on [0, 2] - always ≥ 1
example : ∀ x ∈ Icc (0 : ℝ) 2, Real.cosh x ≤ 4 := by
  certify_bound

example : ∀ x ∈ Icc (0 : ℝ) 2, 1 ≤ Real.cosh x := by
  certify_bound

end Transcendentals


/-! ## Application 3: Point Inequalities with interval_decide

Prove specific numerical facts about transcendentals
-/

section PointInequalities

-- π bounds
example : Real.pi < 3.15 := by interval_decide
example : 3.14 < Real.pi := by interval_decide

-- sin/cos at specific points
example : Real.sin 1 < 0.85 := by interval_decide

example : Real.cos 1 < 0.55 := by interval_decide

-- Combined: sin(1) + cos(1) < 1.4
example : Real.sin 1 + Real.cos 1 < 1.4 := by interval_decide

-- sqrt bounds
example : Real.sqrt 2 < 1.42 := by interval_decide

end PointInequalities


/-! ## Application 4: Root Finding

Prove existence of roots using IVT with proper Expr.eval form
-/

section RootFinding

-- Define intervals
def I12 : IntervalRat := ⟨1, 2, by norm_num⟩
def I01 : IntervalRat := ⟨0, 1, by norm_num⟩

-- x² - 2 = 0 has root in [1, 2] (√2)
-- At x=1: 1 - 2 = -1 < 0
-- At x=2: 4 - 2 = 2 > 0
example : ∃ x ∈ I12, Expr.eval (fun _ => x)
    (Expr.add (Expr.mul (Expr.var 0) (Expr.var 0)) (Expr.neg (Expr.const 2))) = 0 := by
  interval_roots

-- x³ - x - 1 = 0 (plastic constant) has root in [1, 2]
-- At x=1: 1 - 1 - 1 = -1 < 0
-- At x=2: 8 - 2 - 1 = 5 > 0
example : ∃ x ∈ I12, Expr.eval (fun _ => x)
    (Expr.add (Expr.add (Expr.mul (Expr.var 0) (Expr.mul (Expr.var 0) (Expr.var 0)))
                        (Expr.neg (Expr.var 0)))
              (Expr.neg (Expr.const 1))) = 0 := by
  interval_roots

-- cos(x) - x = 0 has root in [0, 1] (Dottie number ≈ 0.739)
-- At x=0: cos(0) - 0 = 1 > 0
-- At x=1: cos(1) - 1 ≈ 0.54 - 1 = -0.46 < 0
example : ∃ x ∈ I01, Expr.eval (fun _ => x)
    (Expr.add (Expr.cos (Expr.var 0)) (Expr.neg (Expr.var 0))) = 0 := by
  interval_roots

-- sin(x) = 0 has root in [3, 4] (π is in this range)
def I34 : IntervalRat := ⟨3, 4, by norm_num⟩

example : ∃ x ∈ I34, Expr.eval (fun _ => x) (Expr.sin (Expr.var 0)) = 0 := by
  interval_roots

end RootFinding


/-! ## Application 5: Dyadic Backend - certify_kernel_fallback

For kernel-verified proofs (uses decide instead of native_decide when possible)
-/

section DyadicBackend

-- Basic polynomial
example : ∀ x ∈ Icc (0 : ℝ) 1, x * x + x ≤ 2 := by
  certify_kernel_fallback

-- With transcendentals
example : ∀ x ∈ Icc (0 : ℝ) 1, Real.sin x ≤ 1 := by
  certify_kernel_fallback

example : ∀ x ∈ Icc (0 : ℝ) 1, Real.cos x ≤ 1 := by
  certify_kernel_fallback

-- exp bounds
example : ∀ x ∈ Icc (0 : ℝ) 1, Real.exp x ≤ 3 := by
  certify_kernel_fallback 60

end DyadicBackend


/-! ## Application 6: Exploration Command

Interactive analysis (run in editor to see output)
-/

section Exploration

-- Explore sin on [0, 7] - should show range [-1, 1]
#explore (Expr.sin (Expr.var 0)) on [0, 7]

-- Explore x² on [0, 2] - min=0 at x=0, max=4 at x=2
#explore (Expr.mul (Expr.var 0) (Expr.var 0)) on [0, 2]

-- Explore cos(x) on [0, 4]
#explore (Expr.cos (Expr.var 0)) on [0, 4]

-- Explore e^x on [0, 2] - strictly increasing
#explore (Expr.exp (Expr.var 0)) on [0, 2]

-- Explore x³ - x on [-2, 2]
#explore (Expr.add (Expr.mul (Expr.var 0) (Expr.mul (Expr.var 0) (Expr.var 0)))
                   (Expr.neg (Expr.var 0))) on [-2, 2]

-- Explore sin(x²) - nested composition
#explore (Expr.sin (Expr.mul (Expr.var 0) (Expr.var 0))) on [0, 3]

-- Explore tanh(x)
#explore (Expr.tanh (Expr.var 0)) on [-3, 3]

end Exploration


/-! ## Application 7: Machine Learning - Activation Function Bounds

Bounding common activation functions
-/

section MLActivations

-- tanh ∈ [-1, 1]
example : ∀ x ∈ Icc (-5 : ℝ) 5, Real.tanh x ≤ 1 := by
  certify_bound

example : ∀ x ∈ Icc (-5 : ℝ) 5, -1 ≤ Real.tanh x := by
  certify_bound

-- sinh grows, but bounded on finite interval
example : ∀ x ∈ Icc (-2 : ℝ) 2, Real.sinh x ≤ 4 := by
  certify_bound

example : ∀ x ∈ Icc (-2 : ℝ) 2, -4 ≤ Real.sinh x := by
  certify_bound

-- cosh ≥ 1 always
example : ∀ x ∈ Icc (-2 : ℝ) 2, 1 ≤ Real.cosh x := by
  certify_bound

end MLActivations


/-! ## Application 8: Using Expr.eval directly with Set.Icc

Complex compositions work well with inline expressions
-/

section ExprEvalWithSetIcc

-- sin(x) + x² on [0, 1]
example : ∀ x ∈ Icc (0 : ℝ) 1, Expr.eval (fun _ => x)
    (Expr.add (Expr.sin (Expr.var 0)) (Expr.mul (Expr.var 0) (Expr.var 0))) ≤ (2 : ℚ) := by
  certify_bound

-- cos(x²) on [0, 2]
example : ∀ x ∈ Icc (0 : ℝ) 2, Expr.eval (fun _ => x)
    (Expr.cos (Expr.mul (Expr.var 0) (Expr.var 0))) ≤ (1 : ℚ) := by
  certify_bound

example : ∀ x ∈ Icc (0 : ℝ) 2, (-1 : ℚ) ≤ Expr.eval (fun _ => x)
    (Expr.cos (Expr.mul (Expr.var 0) (Expr.var 0))) := by
  certify_bound

-- exp(sin(x)) on [0, 3]
example : ∀ x ∈ Icc (0 : ℝ) 3, Expr.eval (fun _ => x)
    (Expr.exp (Expr.sin (Expr.var 0))) ≤ (3 : ℚ) := by
  certify_bound 15

-- sinh(cos(x)) - nested hyperbolic and trig
example : ∀ x ∈ Icc (0 : ℝ) 4, Expr.eval (fun _ => x)
    (Expr.sinh (Expr.cos (Expr.var 0))) ≤ (2 : ℚ) := by
  certify_bound

end ExprEvalWithSetIcc


/-! ## Application 9: Signal Processing - Trig Products

Bounding products and sums of trig functions
-/

section SignalProcessing

-- sin(x) * cos(x) = sin(2x)/2 ∈ [-1/2, 1/2]
example : ∀ x ∈ Icc (0 : ℝ) 7, Real.sin x * Real.cos x ≤ 1 := by
  certify_bound

example : ∀ x ∈ Icc (0 : ℝ) 7, -1 ≤ Real.sin x * Real.cos x := by
  certify_bound

-- sin(x) + cos(x) = √2 * sin(x + π/4) ∈ [-√2, √2]
example : ∀ x ∈ Icc (0 : ℝ) 7, Real.sin x + Real.cos x ≤ 2 := by
  certify_bound

example : ∀ x ∈ Icc (0 : ℝ) 7, -2 ≤ Real.sin x + Real.cos x := by
  certify_bound

-- sin²(x) ∈ [0, 1] - upper bound
example : ∀ x ∈ Icc (0 : ℝ) 7, Real.sin x * Real.sin x ≤ 1 := by
  certify_bound

end SignalProcessing


/-! ## Application 10: Strict Inequalities

Testing strict inequality support
-/

section StrictInequalities

-- Strict upper bound
example : ∀ x ∈ Icc (0 : ℝ) 1, x * x < 2 := by
  certify_bound

-- Strict lower bound
example : ∀ x ∈ Icc (0 : ℝ) 1, -1 < x * x := by
  certify_bound

-- With transcendentals
example : ∀ x ∈ Icc (0 : ℝ) 1, Real.sin x < 2 := by
  certify_bound

example : ∀ x ∈ Icc (0 : ℝ) 1, Real.exp x < 4 := by
  certify_bound 15

end StrictInequalities


/-! ## Application 11: Control Systems - Bounded Control

Bounding control inputs and outputs
-/

section ControlSystems

-- Bounded control: |sin(x)| ≤ 1 means control effort bounded
example : ∀ x ∈ Icc (-10 : ℝ) 10, Real.sin x ≤ 1 := by
  certify_bound

example : ∀ x ∈ Icc (-10 : ℝ) 10, -1 ≤ Real.sin x := by
  certify_bound

-- Saturated tanh control: |tanh(x)| ≤ 1
example : ∀ x ∈ Icc (-10 : ℝ) 10, Real.tanh x ≤ 1 := by
  certify_bound

example : ∀ x ∈ Icc (-10 : ℝ) 10, -1 ≤ Real.tanh x := by
  certify_bound

-- Quadratic on positive domain: x² ≥ 0 works fine
example : ∀ x ∈ Icc (0 : ℝ) 5, 0 ≤ x * x := by
  certify_bound

end ControlSystems
