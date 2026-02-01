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

Mathlib's `cons_val` simproc uses `ei.int?` to extract indices, which matches
numeric literals like `0`, `1`, `2` but does not match explicit `Fin.mk`
applications like `⟨0, by omega⟩`.

This causes expressions like:
```lean
(![a, b, c] : Fin 3 → α) ⟨1, by omega⟩
```
to not simplify automatically with default simp.

### 2. Dependent if with ℕ literal conditions

`dite` expressions with natural number comparison conditions require verbose
manual proofs:
```lean
simp only [show (1 : ℕ) ≤ 2 from by omega, show (2 : ℕ) ≤ 2 from by omega, dite_true]
```

## Solutions

### vec_simp

A tactic using a custom `dsimproc` that handles:
- Numeric literal indices: `![a, b, c] 2` → `c` (via `int?`)
- Explicit `Fin.mk` applications: `![a, b, c] ⟨1, proof⟩` → `b` (via `Fin.val` reduction)
- Lambda tails from matrix column extraction: `vecCons a (fun i => vecCons b ...) 1` → `b`
  (applies lambda to synthesized Fin index and reduces)

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
- Complex expressions (e.g., `Finset.sup'` with nested sums) may hit max recursion;
  use `vec_simp!` after `fin_cases` breaks down the goal into simple cases

## Main definitions

* `VecSimp.vecConsFinMk` - dsimproc for reducing `vecCons` with any Fin indices
  (both numeric literals and explicit `Fin.mk` applications)
* `vec_simp` - basic tactic for vector indexing
* `vec_simp!` - **all-in-one tactic** for vectors, matrices, dite, abs, and norm_num
  - Use `vec_simp!` for simple cases
  - Use `vec_simp! [M]` for matrices with definition M
* `dite_simp` - standalone tactic for simplifying dite with decidable literal conditions
-/

namespace VecSimp

open Lean Meta Elab Tactic

initialize registerTraceClass `VecSimp.debug

/-- Extract natural number from a Fin expression.
    Handles both `Fin.mk n proof` and numeric literals like `(2 : Fin 3)`.
    Returns `some n` if successful, otherwise `none`. -/
def getFinVal? (e : Expr) : MetaM (Option Nat) := do
  -- First try whnfR and check for Fin.mk directly (handles ⟨n, proof⟩)
  let e' ← whnfR e
  if e'.getAppFn.constName? == some ``Fin.mk then
    let args := e'.getAppArgs
    if args.size == 3 then
      let val ← whnfR args[1]!
      if let some n := val.nat? then
        return some n
  -- For numeric literals like (2 : Fin 3), extract via Fin.val and reduce
  try
    let finVal ← mkAppM ``Fin.val #[e]
    let finValReduced ← reduce finVal
    return finValReduced.nat?
  catch _ =>
    return none

/-- Recursively traverse a vecCons chain to extract the element at index `idx`.
    Returns `some elem` if successful, `none` otherwise.

    Handles:
    - Explicit vecCons chains: `vecCons a (vecCons b ...) idx`
    - Lambda tails from matrix column extraction: `fun i => vecCons ... i`
    - Nested vecCons after lambda reduction: when applying a lambda returns
      another `vecCons` application that needs further element extraction

    ## Implementation notes

    **inferType vs bindingDomain!**: For lambda tails, we use `inferType` to get
    the domain type rather than `bindingDomain!`, because lambdas without explicit
    binder annotations (e.g., `fun i => ...` vs `fun (i : Fin 2) => ...`) may not
    have the Fin type directly accessible in the binder.

    **instantiateMVars + reduce before nat?**: When extracting the dimension `n` from
    `Fin n`, we must first `instantiateMVars` on the type (to substitute assigned
    metavariables), then `reduce nExpr` before calling `nat?`. Without explicit type
    annotations, `nExpr` may be `Nat.succ ?m` (a metavariable wrapped in Nat.succ)
    rather than a raw literal like `2`. The `nat?` function only matches raw nat
    literals, so instantiating then reducing converts `Nat.succ ?m` → `2`.

    **Recursive extraction**: After reducing a lambda application, the result may
    still be a `vecCons` applied to an index (e.g., `vecCons a tail (Fin.mk k proof)`).
    We recursively extract from this to handle arbitrary nesting depth. -/
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
  -- Handle lambda tails from matrix column extraction
  -- e.g., (fun i => Matrix.vecCons ... i) needs to be applied to idx
  else if e.isLambda then
    trace[VecSimp.debug] "getVecElem: handling lambda tail for idx={idx}"
    -- Get the Fin type from the lambda's inferred type (more robust than bindingDomain!)
    let lamType ← inferType e
    trace[VecSimp.debug] "  inferType result: {lamType}"
    let lamType' ← whnfR lamType
    trace[VecSimp.debug] "  after whnfR: {lamType'}"
    -- Instantiate metavariables that may have been assigned during elaboration
    let lamType'' ← instantiateMVars lamType'
    trace[VecSimp.debug] "  after instantiateMVars: {lamType''}"
    if !lamType''.isForall then
      trace[VecSimp.debug] "  NOT a forall, returning none"
      return none
    let domain := lamType''.bindingDomain!
    trace[VecSimp.debug] "  domain: {domain}"
    let finType ← whnfR domain
    trace[VecSimp.debug] "  finType after whnfR: {finType}"
    if finType.isAppOf ``Fin then
      let finArgs := finType.getAppArgs
      trace[VecSimp.debug] "  Fin args: {finArgs.toList}"
      if finArgs.size >= 1 then
        let nExpr := finArgs[0]!
        let nExprReduced ← reduce nExpr
        trace[VecSimp.debug] "  nExpr: {nExpr}, reduced: {nExprReduced}, nat?: {nExprReduced.nat?}"
        let some _ := nExprReduced.nat? | do
          trace[VecSimp.debug] "  FAILED: nExprReduced.nat? returned none"
          return none
        -- Create Fin.mk idx (proof : idx < n)
        let idxExpr := mkNatLit idx
        let proof ← mkDecideProof (← mkAppM ``LT.lt #[idxExpr, nExprReduced])
        let finIdx ← mkAppM ``Fin.mk #[idxExpr, proof]
        -- Apply lambda to the index and reduce
        let applied := Expr.app e finIdx
        let reduced ← reduce applied
        -- Recursively process - handles nested vecCons after lambda application
        let reduced' ← whnfR reduced
        if reduced'.getAppFn.constName? == some ``Matrix.vecCons && reduced'.getAppArgs.size == 5 then
          -- Result is vecCons applied to an index - extract via recursive getVecElem
          let rargs := reduced'.getAppArgs
          let ridxExpr := rargs[4]!
          let some remainingIdx ← getFinVal? ridxExpr | return some reduced
          return ← getVecElem remainingIdx reduced'
        else
          return some reduced
    return none
  else
    return none

/-- Simproc: Reduce `![a, b, c, ...] i` to the i-th element.

    Handles:
    - Numeric literal indices: `![a, b, c] 2` → `c` (via `int?`)
    - Explicit `Fin.mk` applications: `![a, b, c] ⟨1, proof⟩` → `b` (via `Fin.val` reduction)
    - Lambda tails from matrix column extraction: when the tail is
      `fun i => Matrix.vecCons ...`, applies the lambda to a synthesized Fin index

    First tries `int?` to extract raw integer literals (like Mathlib's cons_val),
    then falls back to reducing `Fin.val` for explicit `Fin.mk` expressions.

    The expression structure is: `App (Matrix.vecCons α n head tail) idx`
    which gives 5 args total to the vecCons function. -/
dsimproc vecConsFinMk (Matrix.vecCons _ _ _) := fun e => do
  trace[VecSimp.debug] "vecConsFinMk called with: {e}"
  let e ← whnfR e
  trace[VecSimp.debug] "after whnfR: {e}"
  let args := e.getAppArgs
  trace[VecSimp.debug] "args.size = {args.size}, fn = {e.getAppFn.constName?}"
  -- When vecCons is applied to an index, we have 5 args: α, n, head, tail, idx
  if e.getAppFn.constName? != some ``Matrix.vecCons || args.size != 5 then
    trace[VecSimp.debug] "  returning .continue (pattern mismatch)"
    return .continue
  let x := args[2]!   -- head
  let xs := args[3]!  -- tail
  let ei := args[4]!  -- index
  trace[VecSimp.debug] "  head={x}, tail={xs}, idx={ei}"
  -- Try to get the index value:
  -- 1. First try int? for raw integer literals (like Mathlib's cons_val)
  -- 2. Fall back to getFinVal? for Fin.mk expressions
  let ei' ← whnfR ei
  let i : Nat ← match ei'.int? with
    | some n => pure n.toNat
    | none =>
      let some n ← getFinVal? ei | return .continue
      pure n
  -- Get the element at index i
  if i == 0 then
    return .done x
  else
    let some result ← getVecElem (i - 1) xs | return .continue
    return .done result

end VecSimp

/-- Tactic that simplifies vector indexing with Fin indices.

    Handles both explicit `Fin.mk` constructors and numeric literal indices:
    - `![a, b, c] ⟨1, proof⟩` → `b`
    - `![a, b, c] 2` → `c`

    For a more aggressive variant that also handles `dite` conditions, use `vec_simp!`.

    Example:
    ```lean
    example : (![1, 2, 3] : Fin 3 → ℕ) ⟨1, by omega⟩ = 2 := by vec_simp
    example : (![1, 2, 3] : Fin 3 → ℕ) 2 = 3 := by vec_simp
    ```
-/
macro "vec_simp" : tactic =>
  `(tactic| simp only [VecSimp.vecConsFinMk, Matrix.cons_val_zero, Matrix.cons_val_zero',
                       Matrix.cons_val_one, Matrix.head_cons])

/-- Aggressive variant of `vec_simp` for simple vector/dite expressions.

    Simplifies:
    - Vector indexing with `Fin.mk` indices: `![a, b, c] ⟨1, proof⟩` → `b`
    - `Matrix.of` applications: `(Matrix.of f) i j` → `f i j`
    - Decidable `dite` conditions: `if h : 1 ≤ 2 then x else y` → `x`
    - Absolute values of positive/nonnegative values
    - Numeric goals via `norm_num`

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
    -- Matrix.of_apply: unwraps !![...] notation: (Matrix.of f) i j → f i j
    try simp only [Matrix.of_apply]
    -- Nested indexing (![![...]] i j) is handled by simp's repeated application:
    --   ![![1,2],[3,4]] 0 → ![1,2], then ![1,2] 0 → 1
    try simp (config := { decide := true }) only [
      VecSimp.vecConsFinMk, Matrix.cons_val_zero, Matrix.cons_val_zero',
      Matrix.cons_val_one, Matrix.head_cons, dite_true, dite_false,
      abs_of_pos, abs_of_nonneg
    ]
    try norm_num
  ))

/-- Version of `vec_simp!` for matrices with named definitions.

    Unfolds the given definitions, then applies `vec_simp!`.

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
  `(tactic| (simp only [$defs,*]; vec_simp!))

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
