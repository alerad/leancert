/-
Copyright (c) 2024 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Tactic.NormNum

/-!
# vec_simp & dite_simp: Simplification for vectors and dependent if-then-else

## Problems

### 1. Vector indexing with Fin.mk

Mathlib's `cons_val` simproc uses `ei.int?` to extract indices, which only
matches numeric literals like `0`, `1`, `2`. It does not match explicit
`Fin.mk` applications like `⟨0, by omega⟩`.

This causes expressions like:
```lean
(![a, b, c] : Fin 3 → α) ⟨1, by omega⟩
```
to not simplify automatically.

### 2. Dependent if with ℕ literal conditions

`dite` expressions with natural number comparison conditions require verbose
manual proofs:
```lean
simp only [show (1 : ℕ) ≤ 2 from by omega, show (2 : ℕ) ≤ 2 from by omega, dite_true]
```

## Solutions

### vec_simp

A tactic using a custom `dsimproc` that extracts the natural number from
`Fin.mk n proof` applications and reduces vector indexing accordingly.

### vec_simp!

Aggressive variant of `vec_simp` that also handles `dite` conditions and
absolute values of positive literals. Use this when vector indexing appears
inside dependent if expressions (common with bounds checking).

### dite_simp

Standalone tactic that uses `simp` with `config := { decide := true }` to
automatically evaluate decidable conditions involving ℕ literals, then
applies `dite_true`/`dite_false`. Use this when you only need dite
simplification without vector indexing.

## Design Notes for dite_simp

### Failed approach: Custom simproc

We initially attempted a custom `simproc` to match on `dite` applications:
```lean
simproc diteNatLit (dite _ _ _) := fun e => do
  -- Check if condition is ℕ comparison, reduce via whnf
  ...
```

**Why it failed:** The pattern `dite _ _ _` doesn't match correctly because
`dite` has implicit type arguments and an auto-bound `Decidable` instance.
The simproc pattern syntax couldn't reliably match the actual `dite` applications.

### Working approach: simp with decide config

The solution uses Lean's built-in `decide` configuration for `simp`:
```lean
simp (config := { decide := true }) only [dite_true, dite_false]
```

**Why it works:**
1. `config := { decide := true }` tells simp to use `Decidable` instances
   to evaluate propositions to `True` or `False`
2. For ℕ literal comparisons like `(1 : ℕ) ≤ 2`, the `Decidable` instance computes
3. Once reduced to `True`/`False`, `dite_true`/`dite_false` eliminate the `dite`

### Limitations

- Only works for conditions with computable `Decidable` instances
- Both sides of comparisons must be concrete literals (not variables)
- Very large literals may be slow to compute

## Main definitions

* `VecSimp.vecConsFinMk` - dsimproc for reducing `vecCons` with `Fin.mk` indices
* `vec_simp` - basic tactic for vector indexing with `Fin.mk` indices
* `vec_simp!` - **all-in-one tactic** for vectors, matrices, dite, abs, and norm_num
  - Use `vec_simp!` for simple cases
  - Use `vec_simp! [M]` for matrices with definition M
* `dite_simp` - standalone tactic for simplifying dite with decidable literal conditions
-/

namespace VecSimp

open Lean Meta Elab Tactic

/-- Extract natural number from a Fin.mk application.
    Returns `some n` if `e` is `Fin.mk n proof`, otherwise `none`. -/
def getFinMkVal? (e : Expr) : MetaM (Option Nat) := do
  -- Try to match Fin.mk _ val _
  let e ← whnfR e
  let args := e.getAppArgs
  -- Fin.mk has 3 args: n (bound), val, proof
  if e.getAppFn.constName? == some ``Fin.mk && args.size == 3 then
    let val ← whnfR args[1]!
    match val.nat? with
    | some n => return some n
    | none => return none
  else
    return none

/-- Recursively traverse a vecCons chain to extract the element at index `idx`.
    Returns `some elem` if successful, `none` otherwise. -/
partial def getVecElem (idx : Nat) (e : Expr) : MetaM (Option Expr) := do
  let e ← whnfR e
  let args := e.getAppArgs
  -- Matrix.vecCons has 4 args when not applied to an index: α, n, head, tail
  if e.getAppFn.constName? == some ``Matrix.vecCons && args.size >= 4 then
    let head := args[2]!
    let tail := args[3]!
    if idx == 0 then
      return some head
    else
      getVecElem (idx - 1) tail
  else
    return none

/-- Simproc: Reduce `![a, b, c, ...] ⟨n, proof⟩` to the n-th element.

    This handles the case where the index is an explicit `Fin.mk` application
    rather than a numeric literal (which Mathlib's `cons_val` handles).

    The expression structure is: `App (Matrix.vecCons α n head tail) idx`
    which gives 5 args total to the vecCons function. -/
dsimproc vecConsFinMk (Matrix.vecCons _ _ _) := fun e => do
  let e ← whnfR e
  let args := e.getAppArgs
  -- When vecCons is applied to an index, we have 5 args: α, n, head, tail, idx
  if e.getAppFn.constName? != some ``Matrix.vecCons || args.size != 5 then
    return .continue
  let x := args[2]!   -- head
  let xs := args[3]!  -- tail
  let ei := args[4]!  -- index
  -- First check if it's a standard numeric literal - let Mathlib handle those
  let ei ← whnfR ei
  if ei.int?.isSome then
    return .continue
  -- Try to extract index from Fin.mk
  let some i ← getFinMkVal? ei | return .continue
  -- Get the element at index i
  if i == 0 then
    return .done x
  else
    let some result ← getVecElem (i - 1) xs | return .continue
    return .done result

end VecSimp

/-- Tactic that simplifies vector indexing with explicit Fin constructors.

    Use this when `![a, b, c] ⟨n, proof⟩` doesn't reduce automatically.

    For a more aggressive variant that also handles `dite` conditions, use `vec_simp!`.

    Example:
    ```lean
    example : (![1, 2, 3] : Fin 3 → ℕ) ⟨1, by omega⟩ = 2 := by vec_simp
    ```
-/
macro "vec_simp" : tactic =>
  `(tactic| simp only [VecSimp.vecConsFinMk, Matrix.cons_val_zero, Matrix.cons_val_zero',
                       Matrix.cons_val_one, Matrix.head_cons])

/-- Aggressive variant of `vec_simp` for simple vector/dite expressions.

    Simplifies vector indexing with `Fin.mk` indices, evaluates decidable `dite`
    conditions, handles absolute values, and tries `norm_num` to close numeric goals.

    For matrices with named definitions, use `vec_simp! [M]` instead.

    Example:
    ```lean
    example (f : (1 : ℕ) ≤ 2 → ℕ) :
        (if h : (1 : ℕ) ≤ 2 then (![1, 2, 3] : Fin 3 → ℕ) ⟨1, by omega⟩ else 0)
        = 2 := by
      vec_simp!
    ```
-/
macro "vec_simp!" : tactic =>
  `(tactic| (
    simp (config := { decide := true }) only [
      VecSimp.vecConsFinMk, Matrix.cons_val_zero, Matrix.cons_val_zero',
      Matrix.cons_val_one, Matrix.head_cons, dite_true, dite_false,
      abs_of_pos, abs_of_nonneg
    ]
    try norm_num
  ))

/-- Version of `vec_simp!` for matrices with named definitions.

    Disables Mathlib simprocs (to avoid PANIC with `fin_cases`), unfolds the
    given definitions, then applies vector simplification, dite evaluation,
    abs simplification, and `norm_num`.

    Example:
    ```lean
    def M : Fin 3 → Fin 3 → ℝ := ![![1, 2, 3], ![4, 5, 6], ![7, 8, 9]]
    example : ∀ i j : Fin 3, |M i j| ≤ 9 := by
      intro i j
      fin_cases i <;> fin_cases j
      all_goals vec_simp! [M]
    ```
-/
macro "vec_simp!" "[" defs:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| (
    set_option simprocs false in simp [$defs,*]
    try simp only [VecSimp.vecConsFinMk]
    try simp (config := { decide := true }) only [dite_true, dite_false]
    try simp only [abs_of_pos, abs_of_nonneg]
    try norm_num
  ))

/-- Tactic that simplifies `dite` expressions with decidable literal conditions.

    Replaces manual patterns like:
    ```lean
    simp only [show (1 : ℕ) ≤ 2 from by omega, show (2 : ℕ) ≤ 2 from by omega, dite_true]
    ```

    With just:
    ```lean
    dite_simp
    ```

    ## How it works

    Uses `simp (config := { decide := true })` to evaluate decidable conditions,
    then applies `dite_true`/`dite_false` to eliminate the `dite`.

    ## Supported conditions

    Any condition with a computable `Decidable` instance where both operands
    are literals:
    - `(1 : ℕ) ≤ 2`, `(3 : ℕ) < 5`, `(2 : ℕ) = 2`
    - Works with `ℕ`, `ℤ`, `Fin n`, and other types with decidable ordering

    ## Limitations

    - **Variables don't work**: `n ≤ 2` where `n` is a variable won't simplify
    - **Large literals**: Very large numbers may be slow to compute
    - **Non-decidable conditions**: Conditions without `Decidable` instances fail

    ## Example

    ```lean
    example (f : (1 : ℕ) ≤ 2 → ℕ) (g : ¬(1 : ℕ) ≤ 2 → ℕ) :
        (if h : (1 : ℕ) ≤ 2 then f h else g h) = f (by omega) := by
      dite_simp

    -- Multiple nested dite:
    example (f : (1 : ℕ) ≤ 2 → (2 : ℕ) ≤ 2 → ℕ) :
        (if h₁ : (1 : ℕ) ≤ 2 then if h₂ : (2 : ℕ) ≤ 2 then f h₁ h₂ else 0 else 0)
        = f (by omega) (by omega) := by
      dite_simp
    ```
-/
macro "dite_simp" : tactic =>
  `(tactic| simp (config := { decide := true }) only [dite_true, dite_false])

-- Note: matrix_simp and matrix_simp! are deprecated; use vec_simp! [defs] instead
