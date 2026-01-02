/-
Copyright (c) 2024 LeanBound Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanBound Contributors
-/
import LeanBound.Numerics.Optimization.Global

/-!
# Global Optimization Examples

This file demonstrates the branch-and-bound global optimization algorithm
on multivariate expressions over n-dimensional boxes.

## Examples

### Univariate

- Minimize x² over [-1, 1] → global min at x = 0
- Minimize (x - 1/2)² over [0, 1] → global min at x = 1/2

### Multivariate

- Minimize x² + y² over [-1, 1]² → global min at (0, 0)
- Rosenbrock function: (1 - x)² + 100(y - x²)² over [-2, 2]²
- Beale function on a box
-/

namespace LeanBound.Examples.GlobalOptimization

open LeanBound.Core
open LeanBound.Numerics
open LeanBound.Numerics.Optimization

/-! ### Expression builders -/

/-- The expression x² (variable 0 squared) -/
def exprXSq : Expr := Expr.mul (Expr.var 0) (Expr.var 0)

/-- The expression y² (variable 1 squared) -/
def exprYSq : Expr := Expr.mul (Expr.var 1) (Expr.var 1)

/-- The expression x² + y² -/
def exprSumSq : Expr := Expr.add exprXSq exprYSq

/-- The expression (x - c)² for a constant c -/
def exprShiftedSq (c : ℚ) : Expr :=
  let xMinusC := Expr.add (Expr.var 0) (Expr.neg (Expr.const c))
  Expr.mul xMinusC xMinusC

/-- The expression (1 - x)² -/
def exprOneMinusXSq : Expr :=
  let oneMinusX := Expr.add (Expr.const 1) (Expr.neg (Expr.var 0))
  Expr.mul oneMinusX oneMinusX

/-- The expression (y - x²)² -/
def exprYMinusXSqSq : Expr :=
  let yMinusXSq := Expr.add (Expr.var 1) (Expr.neg exprXSq)
  Expr.mul yMinusXSq yMinusXSq

/-- Rosenbrock function: (1 - x)² + 100(y - x²)² -/
def exprRosenbrock : Expr :=
  Expr.add exprOneMinusXSq (Expr.mul (Expr.const 100) exprYMinusXSqSq)

/-! ### Box construction -/

/-- Unit box [0, 1]² -/
def boxUnit2D : Box := Box.unit 2

/-- Symmetric box [-1, 1]² -/
def boxSym2D : Box := Box.symmetric 2

/-- A larger box [-2, 2]² for Rosenbrock -/
def boxLarge2D : Box :=
  [⟨-2, 2, by norm_num⟩, ⟨-2, 2, by norm_num⟩]

/-! ### Example evaluations -/

-- Minimize x² over [-1, 1]
#eval
  let B : Box := [⟨-1, 1, by norm_num⟩]
  let result := globalMinimizeCore exprXSq B { maxIterations := 100, tolerance := 1/100 }
  s!"Min x^2 on [-1,1]: lo={result.bound.lo}, hi={result.bound.hi}, iters={result.bound.iterations}"

-- Minimize (x - 1/2)² over [0, 1]
#eval
  let B : Box := [⟨0, 1, by norm_num⟩]
  let e := exprShiftedSq (1/2)
  let result := globalMinimizeCore e B { maxIterations := 100, tolerance := 1/100 }
  s!"Min (x-1/2)^2 on [0,1]: lo={result.bound.lo}, hi={result.bound.hi}, iters={result.bound.iterations}"

-- Minimize x² + y² over [-1, 1]²
#eval
  let result := globalMinimizeCore exprSumSq boxSym2D { maxIterations := 500, tolerance := 1/10 }
  s!"Min x^2+y^2 on [-1,1]^2: lo={result.bound.lo}, hi={result.bound.hi}, iters={result.bound.iterations}"

-- Minimize x² + y² over [0, 1]²
#eval
  let result := globalMinimizeCore exprSumSq boxUnit2D { maxIterations := 500, tolerance := 1/10 }
  s!"Min x^2+y^2 on [0,1]^2: lo={result.bound.lo}, hi={result.bound.hi}, iters={result.bound.iterations}"

-- Maximize x² over [-1, 1] (should give 1 at x = ±1)
#eval
  let B : Box := [⟨-1, 1, by norm_num⟩]
  let result := globalMaximizeCore exprXSq B { maxIterations := 100, tolerance := 1/100 }
  s!"Max x^2 on [-1,1]: lo={result.bound.lo}, hi={result.bound.hi}, iters={result.bound.iterations}"

-- Rosenbrock function (harder test)
#eval
  let result := globalMinimizeCore exprRosenbrock boxLarge2D
    { maxIterations := 1000, tolerance := 1/4 }
  s!"Min Rosenbrock on [-2,2]^2: lo={result.bound.lo}, hi={result.bound.hi}, iters={result.bound.iterations}"

/-! ### Box operations demo -/

#eval
  let B := boxSym2D
  s!"Dimension: {B.dim}, Volume: {Box.volume B}, MaxWidth: {Box.maxWidth B}"

#eval
  let B := boxSym2D
  let (B1, B2) := Box.splitWidest B
  s!"After split: B1 maxWidth={Box.maxWidth B1}, B2 maxWidth={Box.maxWidth B2}"

#eval
  let B := Box.unit 3
  s!"Unit box [0,1]^3: dim={B.dim}, maxWidth={Box.maxWidth B}"

end LeanBound.Examples.GlobalOptimization
