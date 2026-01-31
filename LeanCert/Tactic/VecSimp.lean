/-
Copyright (c) 2024 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import Mathlib.Data.Fin.VecNotation

/-!
# vec_simp: Vector indexing with explicit Fin constructors

## Problem

Mathlib's `cons_val` simproc uses `ei.int?` to extract indices, which only
matches numeric literals like `0`, `1`, `2`. It does not match explicit
`Fin.mk` applications like `⟨0, by omega⟩`.

This causes expressions like:
```lean
(![a, b, c] : Fin 3 → α) ⟨1, by omega⟩
```
to not simplify automatically.

## Solution

This file provides a `dsimproc` that extracts the natural number from
`Fin.mk n proof` applications and reduces vector indexing accordingly.

## Main definitions

* `VecSimp.vecConsFinMk` - dsimproc for reducing `vecCons` with `Fin.mk` indices
* `vec_simp` - tactic macro combining the simproc with standard vector lemmas
-/

namespace VecSimp

open Lean Meta Elab Tactic

/-- Extract natural number from a Fin.mk application.
    Returns `some n` if `e` is `Fin.mk n proof`, otherwise `none`. -/
def getFinMkVal? (e : Expr) : MetaM (Option Nat) := do
  -- Try to match Fin.mk _ val _
  let e ← whnfR e
  match e.getAppFnArgs with
  | (``Fin.mk, #[_, val, _]) =>
    -- val should be a natural number literal
    let val ← whnfR val
    match val.nat? with
    | some n => return some n
    | none => return none
  | _ => return none

/-- Recursively traverse a vecCons chain to extract the element at index `idx`.
    Returns `some elem` if successful, `none` otherwise. -/
partial def getVecElem (idx : Nat) (e : Expr) : MetaM (Option Expr) := do
  let e ← whnfR e
  match e.getAppFnArgs with
  | (``Matrix.vecCons, #[_, _, head, tail]) =>
    if idx == 0 then
      return some head
    else
      getVecElem (idx - 1) tail
  | _ => return none

/-- Simproc: Reduce `![a, b, c, ...] ⟨n, proof⟩` to the n-th element.

    This handles the case where the index is an explicit `Fin.mk` application
    rather than a numeric literal (which Mathlib's `cons_val` handles). -/
dsimproc vecConsFinMk (Matrix.vecCons _ _ _) := fun e => do
  let e ← whnfR e
  match e.getAppFnArgs with
  | (``Matrix.vecCons, #[_α, _en, x, xs, ei]) =>
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
  | _ => return .continue

end VecSimp

/-- Tactic that simplifies vector indexing with explicit Fin constructors.

    Use this when `![a, b, c] ⟨n, proof⟩` doesn't reduce automatically.

    Example:
    ```lean
    example : (![1, 2, 3] : Fin 3 → ℕ) ⟨1, by omega⟩ = 2 := by vec_simp
    ```
-/
macro "vec_simp" : tactic =>
  `(tactic| simp only [VecSimp.vecConsFinMk, Matrix.cons_val_zero, Matrix.cons_val_zero',
                       Matrix.cons_val_one, Matrix.head_cons])
