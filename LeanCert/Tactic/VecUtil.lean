/-
Copyright (c) 2024 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FailIfNoProgress
import Mathlib.Algebra.Order.Group.Abs

/-!
# VecUtil: Shared vector/matrix simplification utilities

Helpers for `Matrix.vecCons` expressions, used by `VecSimp` and `FinSumExpand`.

## Metaprogramming utilities (in `VecUtil` namespace)

* `getFinVal?` - extract Nat from Fin expression
* `getVecElem` - extract element from vecCons chain
* `vecConsFinMk` - dsimproc reducing `vecCons` indexing

## Shared tactics (outside namespace, for use by other tactics)

* `dite_simp` - simplify `if h : 1 ≤ 2 then x else y` → `x`
* `abs_simp` - simplify `|3| → 3`, `|-2| → 2`
* `vec_index_simp_core` - vector indexing with Matrix.of_apply fixed-point iteration
* `vec_index_simp_with_dite` - adds dite/abs support to `vec_index_simp_core`

Debug: `set_option trace.VecUtil.debug true`
-/

namespace VecUtil

open Lean Meta

initialize registerTraceClass `VecUtil.debug

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
    trace[VecUtil.debug] "getVecElem: handling lambda tail for idx={idx}"
    -- Get the Fin type from the lambda's inferred type (more robust than bindingDomain!)
    let lamType ← inferType e
    trace[VecUtil.debug] "  inferType result: {lamType}"
    let lamType' ← whnfR lamType
    trace[VecUtil.debug] "  after whnfR: {lamType'}"
    -- Instantiate metavariables that may have been assigned during elaboration
    let lamType'' ← instantiateMVars lamType'
    trace[VecUtil.debug] "  after instantiateMVars: {lamType''}"
    if !lamType''.isForall then
      trace[VecUtil.debug] "  NOT a forall, returning none"
      return none
    let domain := lamType''.bindingDomain!
    trace[VecUtil.debug] "  domain: {domain}"
    let finType ← whnfR domain
    trace[VecUtil.debug] "  finType after whnfR: {finType}"
    if finType.isAppOf ``Fin then
      let finArgs := finType.getAppArgs
      trace[VecUtil.debug] "  Fin args: {finArgs.toList}"
      if finArgs.size >= 1 then
        let nExpr := finArgs[0]!
        let nExprReduced ← reduce nExpr
        trace[VecUtil.debug] "  nExpr: {nExpr}, reduced: {nExprReduced}, nat?: {nExprReduced.nat?}"
        let some _ := nExprReduced.nat? | do
          trace[VecUtil.debug] "  FAILED: nExprReduced.nat? returned none"
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
  trace[VecUtil.debug] "vecConsFinMk called with: {e}"
  let e ← whnfR e
  trace[VecUtil.debug] "after whnfR: {e}"
  let args := e.getAppArgs
  trace[VecUtil.debug] "args.size = {args.size}, fn = {e.getAppFn.constName?}"
  -- When vecCons is applied to an index, we have 5 args: α, n, head, tail, idx
  if e.getAppFn.constName? != some ``Matrix.vecCons || args.size != 5 then
    trace[VecUtil.debug] "  returning .continue (pattern mismatch)"
    return .continue
  let x := args[2]!   -- head
  let xs := args[3]!  -- tail
  let ei := args[4]!  -- index
  trace[VecUtil.debug] "  head={x}, tail={xs}, idx={ei}"
  -- Try to get the index value:
  -- 1. First try int? for raw integer literals (like Mathlib's cons_val)
  -- 2. Fall back to getFinVal? for Fin.mk expressions
  let ei' ← whnfR ei
  let i : Nat ← match ei'.int? with
    | some n =>
      -- Guard against negative values: int?.toNat silently gives 0 for negatives
      if n < 0 then
        let some nat_n ← getFinVal? ei | return .continue
        pure nat_n
      else
        pure n.toNat
    | none =>
      let some n ← getFinVal? ei | return .continue
      pure n
  -- Get the element at index i
  if i == 0 then
    return .done x
  else
    let some result ← getVecElem (i - 1) xs | return .continue
    return .done result

end VecUtil

/-! ## Shared tactics for vector/matrix simplification -/

/-- Simplify dite with decidable literal conditions: `if h : 1 ≤ 2 then x else y` → `x`.
    Uses `simp (config := { decide := true })`. Requires literal operands (not variables). -/
macro "dite_simp" : tactic =>
  `(tactic| simp (config := { decide := true }) only [dite_true, dite_false])

/-- Simplify absolute values of positive/nonnegative literals: `|3| → 3`, `|-2| → 2`. -/
macro "abs_simp" : tactic =>
  `(tactic| simp only [abs_of_pos, abs_of_nonneg, abs_of_neg, abs_neg])

/-- Core vector indexing simplification with fixed-point iteration.

    Reduces `![a,b,c] i` → element and handles nested `Matrix.of` wrappers.
    Uses `fail_if_no_progress` to iterate until `Matrix.of_apply` makes no progress.

    This is the base tactic used by `finsum_expand!`. For dite/abs support, use
    `vec_index_simp_with_dite` or `vec_simp!`. -/
macro "vec_index_simp_core" : tactic =>
  `(tactic| (
    -- First pass of vector indexing simp
    try simp only [VecUtil.vecConsFinMk,
                   Matrix.cons_val_zero, Matrix.cons_val_zero',
                   Matrix.cons_val_one, Matrix.head_cons]
    -- Fixed-point iteration: of_apply -> main simp, repeat while of_apply makes progress
    repeat (
      fail_if_no_progress simp only [Matrix.of_apply]
      try simp only [VecUtil.vecConsFinMk,
                     Matrix.cons_val_zero, Matrix.cons_val_zero',
                     Matrix.cons_val_one, Matrix.head_cons]
    )
  ))

/-- Vector indexing with dite conditions and absolute values.

    Like `vec_index_simp_core` but also simplifies:
    - `if h : 1 ≤ 2 then x else y` → `x` (decidable dite conditions)
    - `|positive_literal|` → `positive_literal`

    Used by `vec_simp!`. -/
macro "vec_index_simp_with_dite" : tactic =>
  `(tactic| (
    -- First pass with dite/abs
    try simp (config := { decide := true }) only [
      VecUtil.vecConsFinMk, Matrix.cons_val_zero, Matrix.cons_val_zero',
      Matrix.cons_val_one, Matrix.head_cons, dite_true, dite_false,
      abs_of_pos, abs_of_nonneg
    ]
    -- Fixed-point iteration: of_apply -> main simp, repeat while of_apply makes progress
    repeat (
      fail_if_no_progress simp only [Matrix.of_apply]
      try simp (config := { decide := true }) only [
        VecUtil.vecConsFinMk, Matrix.cons_val_zero, Matrix.cons_val_zero',
        Matrix.cons_val_one, Matrix.head_cons, dite_true, dite_false,
        abs_of_pos, abs_of_nonneg
      ]
    )
  ))
