Design Notes (not part of documentation)
========================================

## dite_simp: Failed approach with custom simproc

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

## finsum_expand: Design notes

### Interval sums: simproc + repeat pattern
For interval finsets, we use Mathlib's existing simprocs to convert intervals
to explicit sets, then repeatedly apply `Finset.sum_insert`.

### Fin sums: Mathlib's `Fin.sum_univ_ofNat` simproc
For `∑ i : Fin n, f i`, we use Mathlib's `Fin.sum_univ_ofNat` simproc from
`Mathlib.Data.Fin.Tuple.Reflection`. This simproc:
1. Pattern-matches on `∑ _ : Fin n, _`
2. Extracts `n` as a literal using `n.nat?`
3. Builds the expanded form `f 0 + f 1 + ... + f (n-1)` via `mkSumEqQ`
4. Returns the proof using `FinVec.sum_eq`

Works for any concrete literal n.

### Fallback for non-literal Fin dimensions
When n is not a syntactic literal (e.g., `Fin (2 + 1)` instead of `Fin 3`),
`n.nat?` returns `none` and the simproc doesn't fire. We fall back to
repeatedly applying `Fin.sum_univ_succ` to expand element by element.

### Computed interval bounds
Mathlib's interval simprocs (e.g., `Finset.Icc_ofNat_ofNat`) pattern-match on
syntactic `OfNat` literals. When bounds are computed expressions like `2 * 2`,
the simprocs don't fire because `2 * 2` is syntactically `HMul.hMul 2 2`, not `4`.

The `finsum_expand!` variant handles this by first applying `simp only` with
`Nat.reduceAdd`, `Nat.reduceMul`, `Nat.reduceSub` to normalize arithmetic
expressions in interval bounds to literals before the expansion.

## vec_simp!: Fixed-point iteration with fail_if_no_progress

### The problem: Matrix.of_apply and vecConsFinMk interaction

`Matrix.of_apply` (unwraps `!![...]` notation) and `vecConsFinMk` (reduces vector
indexing) cannot be in the same `simp` call - including both breaks the dsimproc.
But after `vecConsFinMk` reduces one level, `Matrix.of_apply` may be needed again.

**Failed approaches:**
1. `simp only [Matrix.of_apply, VecUtil.vecConsFinMk, ...]` - breaks vecConsFinMk
2. `repeat try simp only [Matrix.of_apply]` - infinite loop (`try` always succeeds)

### Working approach: fail_if_no_progress

Use `fail_if_no_progress` from `Mathlib.Tactic.FailIfNoProgress` to detect when
a tactic makes no progress:

```lean
-- First pass of main simp
try simp (config := { decide := true }) only [VecUtil.vecConsFinMk, ...]
-- Loop: of_apply -> main simp, repeat while of_apply makes progress
repeat (
  fail_if_no_progress simp only [Matrix.of_apply]
  try simp (config := { decide := true }) only [VecUtil.vecConsFinMk, ...]
)
```

**Why it works:**
1. First pass handles cases where Matrix.of_apply isn't needed
2. `fail_if_no_progress` fails when simp doesn't change the goal
3. `repeat` stops when `fail_if_no_progress` fails
4. Inner `try simp` runs unconditionally after each successful `Matrix.of_apply`

This achieves fixed-point iteration: alternate between the two simplifications
until `Matrix.of_apply` can't unwrap any more `Matrix.of` expressions.

### Example: nested Matrix.of wrapping

```lean
def wrappedOf (M : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of fun i j => M i j + 1

example : wrappedOf ![![1, 2], ![3, 4]] 0 0 = 2 := by vec_simp! [wrappedOf]
```

After unfolding `wrappedOf`, we have `(Matrix.of fun i j => ![![1,2],[3,4]] i j + 1) 0 0`.
1. `Matrix.of_apply` → `![![1,2],[3,4]] 0 0 + 1`
2. `vecConsFinMk` (first pass) → `![1,2] 0 + 1`
3. `vecConsFinMk` (second pass) → `1 + 1`
4. `norm_num` → `2`

### Shared module: VecUtil

Reusable tactic macros extracted into `VecUtil` (outside namespace):

| Macro | Description |
|-------|-------------|
| `dite_simp` | `if h : 1 ≤ 2 then x else y` → `x` |
| `abs_simp` | `\|3\|` → `3`, `\|-2\|` → `2` |
| `vec_index_simp_core` | Vector indexing + Matrix.of_apply iteration |
| `vec_index_simp_with_dite` | `vec_index_simp_core` + dite/abs + norm_num |

Usage:
- `vec_simp!` = `vec_index_simp_with_dite` + `norm_num`
- `finsum_expand!` = `finsum_expand` + Fin processing + `vec_index_simp_with_dite`

## Bug fix: |vecCons ... idx| inside matrix column norms (Feb 2026)

### The problem

When computing matrix column norms like `∑ i, |A i j| * ν^i`, the expression
`|A i j|` unfolds to `|vecCons ... idx|` where the vecCons is INSIDE the abs.

**Failing case (Example_7_7.colNorm_le):**
```lean
-- After finsum_expand!, the goal contained unreduced expressions like:
⊢ |Matrix.vecCons (1/2) (fun i => Matrix.vecCons (-1/4) (fun _ => 3/8) i) 2| * ν^2 ≤ bound
```

The vecCons at index 2 should reduce to `3/8`, then `|3/8|` should reduce to `3/8`.

### Root cause analysis

**Issue 1: abs lemmas outside the iteration**

The original `vec_index_simp_with_dite` had abs lemmas in a SEPARATE phase:
```lean
-- Phase 1: iteration
repeat (first | simp [vecConsFinMk, ...] | simp [Matrix.of_apply])
-- Phase 2: abs (AFTER iteration ended)
try simp [abs_of_pos, ...]
```

When we have `|vecCons ...|`:
1. Phase 1 can't reduce vecCons because it's inside abs (simp can't "see through")
2. Phase 1 iteration terminates (neither simp makes progress)
3. Phase 2 tries `abs_of_*` but the argument is still `vecCons ...`, not a literal
4. FAILURE: vecCons unreduced

**Issue 2: decide can't prove positivity for ℝ**

Even with abs lemmas in the iteration, `abs_of_pos` requires proving the argument
is positive. For `ℚ`, `config := { decide := true }` works. For `ℝ`, the order
isn't decidable by `decide` even for literals like `3/8 : ℝ`.

### The fix (two parts)

**Part 1: abs lemmas IN the iteration**
```lean
repeat (
  first
  | fail_if_no_progress simp (config := { decide := true }) only [
      VecUtil.vecConsFinMk, ..., abs_of_pos, abs_of_nonneg, abs_of_neg, abs_neg
    ]
  | fail_if_no_progress simp only [Matrix.of_apply]
)
```

Now simp can:
1. Descend into `|vecCons ...|`
2. Apply `vecConsFinMk` to reduce `vecCons ... idx` → literal
3. Apply `abs_of_*` in the SAME pass once we have a literal (works for ℚ)

**Part 2: norm_num for ℝ**
```lean
-- After iteration, handle ℝ literals where decide doesn't work
try norm_num [abs_of_pos, abs_of_nonneg, abs_of_neg, abs_neg]
```

`norm_num` can prove `(3/8 : ℝ) > 0` and apply `abs_of_pos`.

### Test cases for this bug

The key pattern is: `|vecCons h (fun i => vecCons ... i) idx|` where:
- The vecCons is INSIDE abs
- The tail is a lambda (from matrix column extraction)
- The index is the LAST element (triggers deepest recursion)

```lean
-- Lambda tail inside abs, index 2 (last element)
example : |(![1/2, -1/4, 3/8] : Fin 3 → ℝ) 2| = 3/8 := by vec_simp!

-- Explicit vecCons structure (how it appears after unfolding)
example : |Matrix.vecCons (1/2 : ℝ)
    (fun i => Matrix.vecCons (-1/4) (fun _ => 3/8) i) 2| = 3/8 := by vec_simp!

-- In an inequality context (like the actual colNorm_le proof)
example : 1/2 + (-1/4 * ν + |Matrix.vecCons ... 2| * ν^2) ≤ bound := by
  finsum_expand!; vec_simp!
```

### Lessons learned

1. **abs blocks reduction**: Simp can descend into `|...|` but only if the relevant
   lemmas (like `vecConsFinMk`) are in the same simp call as `abs_of_*`.

2. **Separate phases fail**: If the iteration and abs reduction are separate,
   the iteration terminates before abs is ready (argument not yet a literal).

3. **ℝ vs ℚ**: `decide := true` works for `ℚ` positivity but not `ℝ`. Always
   include `norm_num` as a fallback for real number goals.

4. **Test the last index**: Lambda tail patterns are most likely to fail on the
   last index because it requires the deepest recursion through the tail.

## finsum_bound: O(1) Proof-Size Finite Sum Bounds (Feb 2026)

### Motivation

`finsum_expand` expands `∑ k ∈ Icc a b, f k` into `f a + f(a+1) + ... + f b`,
creating an O(N) expression tree. For N > ~100, this blows up: Lean's kernel
chokes on the giant proof term.

`ReflectiveSum` (in Engine/ReflectiveSum.lean) solved this for BKLNW's specific
function `x^(1/k - 1/3)` using an accumulator loop + `native_decide` for O(1)
proofs. But it's hardcoded — 20+ nearly-identical theorems in BKLNW_a2_reflective.lean
for different parameter values.

`finsum_bound` generalizes this: any function expressible as a `Core.Expr` gets
O(1) proofs automatically.

### Architecture (3 layers)

```
Layer 1: Engine (FinSumDyadic.lean)
  evalSumTermDyadic : per-term interval evaluation via evalIntervalDyadic
  finSumAux : accumulator loop (current → limit, acc += term)
  checkFinSumUpperBound/LowerBound : Bool certificate checkers
  verify_finsum_upper/lower : bridge theorems (checker = true → sum ≤ target)

Layer 2: Tactic (FinSumBound.lean)
  parseFinSumGoal : detect ∑ k ∈ Finset.Icc a b, f k ≤ target
  reifyFinSumBody : convert ℕ→ℝ lambda to Core.Expr (handles Nat.cast)
  mkDomainValidProof : structural recursion on AST for domain validity
  finSumBoundCore : orchestrate reify → support → config → check → bridge

Layer 3: Tests (FinSumBound.lean)
  Constants, index sums, transcendentals, lower bounds, large N
```

### Key reuse from existing infrastructure

- `evalIntervalDyadic` + `evalIntervalDyadic_correct` (IntervalEvalDyadic.lean):
  Per-term interval arithmetic with correctness proof. This is the workhorse.
- `Core.Expr` AST (Core/Expr.lean): 20+ constructors for arithmetic/transcendentals.
  The sum body is reified into this AST.
- `reify` (Meta/ToExpr.lean): Translates Lean expressions to Core.Expr.
  We wrap it with Nat.cast handling for the ℕ → ℝ sum body.
- `mkSupportedCoreProof` (Meta/ProveSupported.lean): Generates ExprSupportedCore
  proofs by structural recursion.
- `IntervalDyadic.upperBoundedBy/lowerBoundedBy` (Core/IntervalDyadic.lean):
  Bool-valued bound checks used in certificate checkers.
- Bridge theorem pattern from DyadicAuto.lean: the same
  "checker = true → semantic property" structure.

### The Nat.cast challenge

Sum bodies have type `ℕ → ℝ`. The lambda variable `k : ℕ` appears in the body
as `↑k : ℝ` (via Nat.cast). But `reify` expects `fun (x : ℝ) => ...`.

Solution: `reifyFinSumBody` uses `replaceNatCast` to find all `Nat.cast k` and
`NatCast.natCast k` subexpressions (by checking the last argument of known cast
functions) and replaces them with a fresh `ℝ` variable before reifying.

### The definitional equality challenge

The bridge theorem produces:
  `∑ k ∈ Icc a b, Expr.eval (sumBodyRealEnv k) body ≤ ↑target`

But the user's goal is:
  `∑ k ∈ Icc a b, f k ≤ literal`

Two issues:
1. `Expr.eval (sumBodyRealEnv k) body` vs `f k`: noncomputable `Expr.eval` must
   unfold to match the user's concrete function.
2. `↑(target : ℚ)` vs `(literal : ℝ)`: Rat.cast of extracted rational vs original
   real literal.

Solution: Try direct `isDefEq` first (works sometimes). If it fails, use a
suffices + converter pattern:
  1. Build a converter metavar: `proofTy → goalType`
  2. Close it with `simp [Expr.eval, sumBodyRealEnv] + norm_num`
  3. This unfolds Expr.eval structurally and normalizes casts

### Domain validity

`evalDomainValidDyadic` checks positivity for log, non-zero for inv, etc.
It's a `Prop` with no `Decidable` instance, and the environment contains
the free variable `k` (summation index), so `mkDecideProof` fails.

Solution: `mkDomainValidProof` builds the proof by structural recursion on
the AST at the meta level:
- const/var/pi → `True.intro`
- add/mul → `And.intro h₁ h₂`
- neg/exp/sin/cos/... → recurse into subexpression
- log/inv/atanh → error (not yet supported; would need per-k checking)

The proof is wrapped in a metavar with the expected type to ensure Lean
accepts the definitional equality between `True` and `evalDomainValidDyadic ...`.

### Relationship to ReflectiveSum

`finsum_bound` generalizes `ReflectiveSum`:
- ReflectiveSum: hardcoded `bklnwTermEval` + `bklnwSumAux`
- finsum_bound: generic `evalSumTermDyadic` + `finSumAux` via Core.Expr

ReflectiveSum's `bklnwTermEval` (which handles rpow) could be wrapped as a
witness in the future Tier 2 API. The accumulator loop, certificate checkers,
and bridge theorem structure are identical.

### Future: Witness API (Tier 2)

For functions NOT in Core.Expr (e.g., rpow, user-defined):

```lean
structure SumTermWitness where
  eval : Nat → DyadicConfig → IntervalDyadic
  correct : ∀ k, f k ∈ eval k cfg
```

The user provides `eval` (computable) and `correct` (bridge). The tactic
plugs this into the same accumulator loop. ReflectiveSum becomes one instance.

### Key failures during development

1. **Argument order in induction hypothesis** (FinSumDyadic.lean):
   Swapped `hdom'` and `hnewAcc` in the `ih` call.

2. **Missing helper theorems** (FinSumDyadic.lean):
   `IntervalDyadic.le_hi_of_mem`, `upperBoundedBy_spec` etc. are defined in
   ReflectiveSum.lean, not in IntervalDyadic. Inlined with `.2` / `.1` and
   `simp + exact_mod_cast`.

3. **No Decidable instance for evalDomainValidDyadic** (FinSumBound.lean):
   Can't use `mkDecideProof` when the environment contains free variable `k`.
   Fixed with meta-level structural recursion.

4. **Eq argument order** (FinSumBound.lean):
   `mkAppM ``Eq #[boolTy, checkExpr, true]` — Bool is the type parameter,
   not a term. Fixed: `mkAppM ``Eq #[checkExpr, true]`.

5. **True.intro has type True, not evalDomainValidDyadic**:
   Though definitionally equal, Lean's `mkAppM` rejects the type mismatch.
   Fixed by wrapping in `mkFreshExprMVar (some expectedTy)` + `assign`.

## finsum_bound Tier 2: Domain Validity for inv/log/atanh (Feb 2026)

### Problem

Tier 1 built domain validity proofs statically via `mkDomainValidProof`, which
recursed on the AST and returned `True.intro` for trivially-valid nodes. This
fails for `inv` (nonzero check), `log` (positive check), and `atanh` (bounds
check) because these conditions depend on `evalIntervalDyadic ... (sumBodyEnvSimple k prec)`,
which varies per summation index `k`.

### Solution: Combined domain+bound checker

Instead of building a domain proof at the tactic level, we integrate domain
checking into the certificate checker. One `native_decide` verifies both
domain validity (for all k ∈ [a,b]) and the bound.

**Engine additions (FinSumDyadic.lean):**

```
checkDomainValidAllAux : loop over k ∈ [current, limit], AND together
  checkDomainValidDyadic body (sumBodyEnvSimple k prec) cfg
  for each k.

checkDomainValidAll_correct : bridge theorem, by strong induction on
  limit + 1 - current (mirrors mem_finSumAux).

checkFinSumUpperBoundFull := checkDomainValidAll && checkFinSumUpperBound

verify_finsum_upper_full : splits the && via Bool.and_eq_true, applies
  checkDomainValidAll_correct for domain + verify_finsum_upper for bound.
```

**Key insight**: `checkDomainValidDyadic` (Bool) already exists in
IntervalEvalDyadic.lean with bridge theorem `checkDomainValidDyadic_correct`.
We just loop it over all k.

### ExprSupportedWithInv support

`ExprSupportedCore` excludes `inv`, `atan`, `arsinh`, `atanh`. For sums like
`∑ 1/(k*k)`, we need `ExprSupportedWithInv` which includes all operations.

The WithInv correctness chain duplicates the Core chain using
`evalIntervalDyadic_correct_withInv` instead of `evalIntervalDyadic_correct`:

```
mem_evalSumTermDyadic_withInv → mem_finSumAux_withInv → mem_finSumDyadic_withInv
  → verify_finsum_upper_withInv → verify_finsum_upper_full_withInv
```

Proofs are identical — only the support predicate and correctness lemma differ.

### Tactic changes (FinSumBound.lean)

1. Removed `mkDomainValidProof` and `buildDomainProof` (no longer needed)
2. Added `detectSupportLevel`: try `mkSupportedCoreProof`, fallback to
   `mkSupportedWithInvProof`
3. Bridge theorem selected by (support level × direction):
   - Core + upper → `verify_finsum_upper_full`
   - WithInv + upper → `verify_finsum_upper_full_withInv`
   etc.
4. Bridge theorem arguments simplified: no domain proof needed (it's inside
   the combined checker).

### What this enables

- `∑ k ∈ Icc 1 100, 1/(k*k) ≤ 2` — inv with auto domain check
- `∑ k ∈ Icc 1 10, log(k) ≤ 16` — log with auto positivity check (k ≥ 1)
- `∑ k ∈ Icc 1 10, exp(1/k) ≤ 20` — nested inv inside exp
- `∑ k ∈ Icc 1 500, 1/(k*k) ≤ 2` — O(1) proof, 500 terms with inv

## finsum_witness: Witness API for Custom Functions (Tier 3, Feb 2026)

### Problem

`finsum_bound` (Tiers 1-2) auto-reifies sum bodies to `Core.Expr`. Functions NOT
in `Core.Expr` (like `rpow` in BKLNW's `x^(1/k - 1/3)`) can't be handled. The
existing `ReflectiveSum.lean` solves this for one hardcoded function, producing
22 near-identical theorems in `BKLNW_a2_reflective.lean` for different parameters.

### Solution: Generic Witness API

The user provides:
1. `evalTerm : Nat → DyadicConfig → IntervalDyadic` — computable per-term evaluator
2. `hmem` — proof that `∀ k, a ≤ k → k ≤ b → f k ∈ evalTerm k cfg`

The engine provides:
- `witnessSumAux` — generic accumulator loop (same pattern as `finSumAux`)
- `witnessSumDyadic` — entry point
- `checkWitnessSumUpperBound/LowerBound` — Bool certificate checkers
- `verify_witness_sum_upper/lower` — bridge theorems
- `mem_witnessSumAux/Dyadic` — correctness chain (strong induction)

### Key difference from Expr-based approach

- **No ExprSupportedCore/WithInv** — user handles semantics
- **No evalDomainValidDyadic** — user's `hmem` proof covers domain
- **No reification** — evaluator is a plain Lean function
- **Same accumulator pattern** — reuses `finSumZero`, `mem_finSumZero`,
  `Finset.sum_Icc_eq_add_sum_Ioc'`, `Finset.Ioc_eq_Icc_succ'`

### Tactic: `finsum_witness`

Syntax: `finsum_witness evalTerm using hmem [prec]`

The `using` keyword separates the evaluator from the proof (needed because
Lean's `term` parser greedily consumes `evalTerm (fun ...)` as one application).

Flow:
1. Parse goal (same `parseWitnessGoal` as `finsum_bound`)
2. Extract target rational via `extractRatFromReal`
3. Elaborate `evalTerm` against `Nat → DyadicConfig → IntervalDyadic`
4. Build expected `hmem` type: `∀ k, a ≤ k → k ≤ b → f k ∈ evalTerm k cfg`
   (requires `.headBeta` on `bodyLambda k` for type inference)
5. Elaborate user's `hmem` against expected type
6. Build bridge theorem + `native_decide`
7. Suffices fallback for defEq mismatches

### Membership.mem argument order gotcha

In Lean 4, `Membership.mem` takes `(container, element)` order:
  `mem : γ → α → Prop`  (with `class Membership (α : outParam ...) (γ : ...)`)
  `x ∈ S = Membership.mem S x`  (notation swaps)

So `mkAppM ``Membership.mem #[interval, value]` — container first!

### Relationship to ReflectiveSum

ReflectiveSum's `bklnwTermDyadic` is one instance of the witness evaluator:
```
bklnwTermDyadic x k cfg  →  evalTerm k cfg  (with x captured in closure)
mem_bklnwTermDyadic       →  user provides hmem
```

The 22 theorems in `BKLNW_a2_reflective.lean` could be unified as instances
of `verify_witness_sum_upper`. This is a follow-up task.

### Files

- `Engine/WitnessSum.lean` — accumulator, checkers, correctness, bridge theorems
- `Tactic/FinSumWitness.lean` — `finsum_witness` tactic
- `Test/WitnessSum.lean` — tests with constant witness + direct bridge use

## finsum_bound Tier 4: Arbitrary Finite Sets (Feb 2026)

### Problem

Tiers 1-3 only handled `∑ k ∈ Finset.Icc a b, f k`. Users also need:
- `Finset.range n`, `Finset.Ico a b`, `Finset.Ioc a b`, `Finset.Ioo a b`
- Explicit finite sets like `{1, 3, 5, 7}`

Key constraint: keep O(1) proof size (no `finsum_expand`-style expansion).

### Core idea: List-based accumulator

A random finite set is not inductively enumerable like `[a, b]`. Solution:
iterate over a `List Nat` of elements, then bridge to `Finset.sum` via
Mathlib's `List.sum_toFinset`:

```lean
theorem List.sum_toFinset (f : ι → M) (hl : l.Nodup) :
    l.toFinset.sum f = (l.map f).sum
```

The List accumulator uses structural induction (simpler than `Nat.strongRecOn`
for Icc). A single `native_decide` verifies:
  `decide (S = indices.toFinset) && indices.Nodup && domain && bound`

### Engine: List chain (FinSumDyadic.lean)

```
finSumAuxList : iterate List Nat, accumulate intervals
finSumDyadicList : entry point (zero-initialized accumulator)
checkFinSumUpperBoundListFull : combined Bool checker
  = decide (S = indices.toFinset) && Nodup && domainAll && upperBound
verify_finsum_upper_list_full : bridge theorem
```

Correctness proof by List structural induction:
```lean
induction indices generalizing acc partialSum with
| nil => simp; exact hacc
| cons k rest ih =>
    -- reassociate: (ps + f(k)) + rest.map.sum
    -- show ps + f(k) ∈ newAcc via mem_add + roundOut_contains
    -- apply ih with (fun j hj => hdom j (.tail k hj))
```

**List.Mem constructors**: `.head rest` for `k ∈ k :: rest`, `.tail k hj` for
`j ∈ k :: rest` given `hj : j ∈ rest`. Don't use `List.mem_cons_self k rest`
(all-implicit args — gives "Function expected" error in this Lean version).

Both ExprSupportedCore and ExprSupportedWithInv variants provided.

### Engine: Witness list chain (WitnessSum.lean)

Same pattern but parameterized by `evalTerm : Nat → DyadicConfig → IntervalDyadic`:

```
witnessSumAuxList / witnessSumDyadicList
checkWitnessSumUpperBoundListFull : S = toFinset ∧ Nodup ∧ bound
verify_witness_sum_upper_list_full
  (hmem : ∀ k, k ∈ S → f k ∈ evalTerm k cfg) : ∑ k ∈ S, f k ≤ target
```

The combined bridge converts `hmem` from Finset membership to List membership
using `heq ▸ List.mem_toFinset.mpr hk`.

### Tactic: Finset extraction (FinSumBound.lean)

The tactic extracts elements from any recognized Finset expression:

| Finset form | Extraction |
|---|---|
| `Finset.Icc a b` | `List.range' a (b+1-a)` |
| `Finset.Ico a b` | `List.range' a (b-a)` |
| `Finset.Ioc a b` | `List.range' (a+1) (b-a)` |
| `Finset.Ioo a b` | `List.range' (a+1) (b-a-1)` |
| `Finset.range n` | `List.range n` |
| `{1, 3, 5, 7}` | recursive Insert.insert/Singleton.singleton |

**Lean 4 Finset expression representation**: `{1, 3, 5}` desugars to
`Insert.insert 1 (Insert.insert 3 (Singleton.singleton 5))`. The actual
constants are `Insert.insert` (5 args: [α, γ, inst, elem, rest]) and
`Singleton.singleton` (4 args: [α, γ, inst, elem]). NOT `Finset.insert` /
`Finset.singleton` (these don't exist as constants — they're instances).

### Tactic: Dispatch logic

```
finSumBoundCore:
  1. Try Icc path first (faster, no Nodup overhead)
  2. Fall back to list path for other Finsets
```

The list path builds `checkFinSumUpperBoundListFull body S indices target cfg`
and closes it with one `native_decide`.

### Tactic: Witness list dispatch (FinSumWitness.lean)

For `finsum_bound using evalTerm hmem` with non-Icc goals:

- Icc path: `hmem : ∀ k, a ≤ k → k ≤ b → f k ∈ evalTerm k cfg` (3 arg lambda)
- List path: `hmem : ∀ k, k ∈ S → f k ∈ evalTerm k cfg` (2 arg lambda)

The user writes `fun k _ => myProof k _` for list goals (vs `fun k _ _ => ...`
for Icc). Existing Icc tests are unaffected since they take the Icc path.

### Converter fix: div_eq_mul_inv

The suffices fallback converter failed for inv bodies on the list path:
```
Proof type: ∑ k ∈ {1,2,4,8}, Expr.eval (sumBodyRealEnv k) (const(1).mul (var 0).inv) ≤ ↑(2/1)
Goal type:  ∑ k ∈ {1,2,4,8}, 1 / ↑k ≤ 2
```

After `simp [Expr.eval, sumBodyRealEnv]`, the proof has `↑(1/1) * (↑k)⁻¹` but
the goal has `1 / ↑k`. Since `a / b = a * b⁻¹` by definition, these should match
after normalizing the goal's division.

**Fix**: Add `div_eq_mul_inv` to the simp set:
```lean
simp only [Core.Expr.eval, Engine.sumBodyRealEnv, div_eq_mul_inv] at h ⊢
norm_num at h ⊢
exact h
```

This normalizes `1 / ↑k` → `1 * (↑k)⁻¹` in the goal, then `norm_num` simplifies
`↑(Rat.divInt 1 1)` → `1` in the proof hypothesis. Both sides match.

### Finset parsing: shared vs duplicated helpers

`FinSumBound.lean` imports `FinSumWitness.lean`. The Finset extraction functions
(`extractFinsetSum`, `extractNatLit`, `tryExtractExplicitFinset`, `extractFinsetElements`)
are needed in both files. Since FinSumWitness can't import FinSumBound (circular),
the helpers are duplicated (with `'` suffix in FinSumWitness). This is acceptable
for ~80 lines of simple parsing code. A shared module could be factored out later
if more tactics need this functionality.

### What this enables

```lean
-- Finset.range
example : ∑ _k ∈ Finset.range 10, (1 : ℝ) ≤ 11 := by finsum_bound

-- Finset.Ico with inv
example : ∑ k ∈ Finset.Ico (1 : ℕ) 11, (1 : ℝ) / ↑k ≤ 4 := by finsum_bound

-- Explicit finset
example : ∑ k ∈ ({1, 3, 5, 7} : Finset ℕ), (↑k : ℝ) ≤ 17 := by finsum_bound

-- Explicit finset with inv
example : ∑ k ∈ ({1, 2, 4, 8} : Finset ℕ), (1 : ℝ) / ↑k ≤ 2 := by finsum_bound

-- Sparse set with transcendentals
example : ∑ k ∈ ({1, 10, 100} : Finset ℕ), Real.exp (-(↑k : ℝ)) ≤ 1 := by finsum_bound
```

### Files modified

- `Engine/FinSumDyadic.lean` — list-based accumulator + combined checkers + bridge theorems (~220 lines)
- `Engine/WitnessSum.lean` — list-based witness accumulator + combined checkers (~100 lines)
- `Tactic/FinSumBound.lean` — Finset extraction, list path dispatch, div_eq_mul_inv converter fix
- `Tactic/FinSumWitness.lean` — Finset extraction (duplicated), list path dispatch
- `Test/FinSumBound.lean` — Tier 4 tests (range, Ico, Ioc, explicit sets, inv, exp, lower bounds)

## Fin n sum support: unified `finsum_bound` (Feb 2026)

### Problem

`∑ i : Fin n, f i` elaborates to `Finset.sum Finset.univ (fun i : Fin n => f i)`.
The original approach used a separate `fin_sum_bound` wrapper that did
`simp only [Fin.sum_univ_eq_sum_range]; finsum_bound`. Two issues:

1. **Two tactic names** — users had to know when to use `fin_sum_bound` vs `finsum_bound`
2. **`simp only` fails for complex bodies** — `Fin.sum_univ_eq_sum_range` has type
   `∀ f : ℕ → M, ∑ i : Fin n, f ↑i = ∑ i ∈ range n, f i`. `simp` needs to infer
   `f` by higher-order matching, which fails when the body is e.g.
   `fun i : Fin 5 => exp (↑↑i)` (double coercion `Fin.val` then `Nat.cast`)

### Solution: meta-level `tryRewriteFinSum`

Instead of `simp`, `finsum_bound` detects `Finset.sum Finset.univ body` where
`univ` is over `Fin n`, then:

1. Extracts `body : Fin n → β` from the goal
2. Uses `lambdaTelescope` to open the body and replace `Fin.val i` / `Fin.toNat i`
   with a fresh `k : ℕ` variable
3. Builds `f : ℕ → β` via `mkLambdaFVars`
4. Rewrites with `Fin.sum_univ_eq_sum_range f` via `MVarId.rewrite` + `replaceTargetEq`

This handles arbitrary bodies because `f` is constructed explicitly, not inferred
by simp's pattern matcher.

### Nat.cast + Fin.val handling in reifier

`replaceNatCast` (used by `reifyFinSumBody`) was extended with `isFVarOrFinVal`
to also match `Nat.cast (Fin.val k)` — the double coercion that appears in
Fin-indexed sum bodies after the rewrite.

### Witness mode

Both auto-mode and witness-mode elab rules call `tryRewriteFinSum` before
dispatch. After rewriting, a Fin sum becomes `∑ k ∈ Finset.range n, ...`
which the existing range/list path handles. For witness mode, the hmem proof
uses the list path signature `∀ k, k ∈ S → ...` (2 args, not 3).

### Removed

`FinSumBoundFin.lean` and the `fin_sum_bound` syntax are deleted. All Fin sum
handling is now internal to `finsum_bound`.

## Auto-hmem witness mode: `finsum_bound auto` (Feb 2026)

### Problem

In witness mode (`finsum_bound using eval hmem`), the user must manually write
`hmem : ∀ k, ... → f k ∈ eval k cfg`. When the evaluator returns singletons
(exact ℚ values wrapped in `IntervalDyadic.singleton`), this proof is tedious —
membership reduces to `d.toRat ≤ x ∧ x ≤ d.toRat` which is just reflexivity
after reducing `Dyadic.toRat`.

### Solution: `finsum_bound auto eval`

New syntax: `finsum_bound auto evalTerm [prec]`. The tactic builds the hmem type,
creates a fresh metavar, and tries to close it automatically using:

**Strategy 1** (constant evaluators): `simp [mem_def, singleton]` then
`refine ⟨?_, ?_⟩ <;> exact_mod_cast (by native_decide)`. This pushes the ℝ
comparison down to ℚ via `exact_mod_cast`, then `native_decide` handles the ℚ
comparison computationally.

**Strategy 2** (k-dependent evaluators, Icc path): `interval_cases k` to enumerate
all concrete k values, then Strategy 1 per case. O(N) but works when bounds are
concrete literals.

**Strategy 3** (k-dependent evaluators, list path): `fin_cases hk` to enumerate
list membership, then Strategy 1 per case.

### Key insight: `exact_mod_cast (by native_decide)`

`x ∈ IntervalDyadic` is `(lo.toRat : ℝ) ≤ x ∧ x ≤ (hi.toRat : ℝ)` — not
decidable over ℝ. But `exact_mod_cast` pushes the cast down, producing a ℚ goal
`lo.toRat ≤ q ∧ q ≤ hi.toRat` which IS decidable and `native_decide` closes it.

### Limitation

`native_decide` can't handle free variables. When the evaluator depends on `k`
and the range is large, `interval_cases` / `fin_cases` enumerates all values
(O(N) proof). For large N with k-dependent evaluators, the user should use the
explicit `finsum_bound using eval hmem` syntax instead.

### TODO: Bool checker approach

For O(1) proof size on k-dependent evaluators, a future improvement would add a
combined Bool checker: `checkWitnessAutoFull evalTerm bodyQ S indices target cfg`
that verifies membership AND bound in one `native_decide`. Requires new engine
theorems and a `bodyQ : ℕ → ℚ` parameter.

## Cast support and reification order fix (Feb 2026)

### Cast patterns in `toRat?`

Added `Rat.cast`, `RatCast.ratCast`, `Nat.cast`, `NatCast.natCast`, `Int.cast`,
and `IntCast.intCast` patterns to `tryMatchNumeric` in `Meta/ToExpr.lean`.
Each extracts the inner value and recursively calls `toRat?`.

This lets `↑(q : ℚ)`, `↑(n : ℕ)`, and `↑(z : ℤ)` appearing in sum bodies be
recognized as constants during reification.

### Reification order: `tryMatchExpr` before `toRat?`

Previously, `toLeanCertExpr` called `toRat?` (step 2) before `tryMatchExpr`
(step 3). This caused `toRat?` to eagerly constant-fold compound expressions
like `↑(-2 : ℤ) + 3` into `const(1)`, because `toRat?` handles `HAdd` of
constants recursively. The bridge converter then couldn't match `Expr.eval ...
(const 1)` against the goal's `↑(-2) + 3` — the structure was lost.

**Fix**: Swap steps 2 and 3. `tryMatchExpr` now runs first, matching `HAdd` and
recursively reifying each operand. This produces `add(const(-2), const(3))`,
which `simp [Expr.eval]` unfolds to `↑(-2 : ℚ) + ↑(3 : ℚ)`, matching the
goal after `push_cast`. Leaf values (pure literals without operators) still
fall through to `toRat?`.

**Trade-off**: Expressions like `1/3 : ℝ` are now reified as `mul(const(1),
inv(const(3)))` instead of `const(1/3)`. This is slightly less compact but
semantically identical, and the bridge handles it correctly.

## Absolute value support (Feb 2026)

### ToExpr: |x| → sqrt(x * x)

`Meta/ToExpr.lean` pattern-matches on `abs _ _ _ x` (Lean 4's `abs` function
takes 3 implicit args: type, Lattice instance, AddGroup instance) and produces
`Expr.sqrt (Expr.mul ex ex)`.

**Why not `Expr.abs`?** `Expr.abs` is a `def` (not a constructor):
  `def abs (e : Expr) : Expr := sqrt (mul e e)`

Using `mkAppM ``Expr.abs` produces a head constant of `Expr.abs`, which the
support checker (`mkSupportedCoreProof`) doesn't recognize — it matches on
head constants like `Expr.sqrt`, `Expr.mul`, etc. By directly producing
`sqrt(mul e e)`, the existing support checker handles it with no changes.

### Proof bridge: `← sqrt_mul_self_eq_abs`

After `simp [Expr.eval, ...]` unfolds the proof, we get `Real.sqrt (f k * f k)`.
The goal still has `|f k|`. The bridge lemma `← Expr.sqrt_mul_self_eq_abs`
(aliased from `Real.sqrt_mul_self_eq_abs`) rewrites `|f k|` in the goal to
`√(f k * f k)`, making both sides match.

Added to simp sets in:
- `FinSumBound.lean` — both Icc and list path converters
- `IntervalAuto/PointIneq.lean` — pointwise inequality prover
- `IntervalAuto/Bound.lean` — interval bound prover

### Aliased lemma

`Core.Expr.sqrt_mul_self_eq_abs` in `Core/Expr.lean`:
```lean
theorem sqrt_mul_self_eq_abs (x : ℝ) : Real.sqrt (x * x) = |x| :=
  Real.sqrt_mul_self_eq_abs x
```

All tactic bridges reference this alias instead of the Mathlib original,
keeping lemma names within the `LeanCert` namespace.

## ↑(q : ℚ) bound target fix (Mar 2026)

### Problem

`finsum_bound` could handle `↑(q : ℚ)` in sum **bodies** (via `Rat.cast` pattern in
`toRat?`) but failed when `↑(q : ℚ)` appeared as the **bound target**:

```lean
-- Failed: "could not extract rational from bound `↑(9 / 500)`"
example : ∑ _k ∈ Icc 1 3, 1/1000 ≤ ↑(9/500 : ℚ) := by finsum_bound
```

### Root cause

`extractRatFromReal` in `IntervalAuto/Extract.lean` delegates to `extractRatFromRat`
for `Rat.cast` arguments. But `extractRatFromRat` only handles `Rat.ofInt`, `OfNat`,
`Nat.cast`, `Int.cast`, and `Rat.mk'` — not `HDiv.hDiv`. When `(9/500 : ℚ)` elaborates
to `HDiv.hDiv (OfNat 9) (OfNat 500)` in ℚ, `extractRatFromRat` fails.

### Fix

One-line change: in the `Rat.cast` branch of `extractRatFromReal`, replace
`extractRatFromRat args.back!` with `LeanCert.Meta.toRat? args.back!`. The `toRat?`
function (in `Meta/ToExpr.lean`) already handles all arithmetic patterns (`HDiv`,
`HAdd`, `HMul`, `HSub`, `Neg`, `OfScientific`, etc.), so it correctly parses
`HDiv.hDiv (OfNat 9) (OfNat 500)` as `9/500 : ℚ`.

## BridgeNative: shared bridge+native_decide infrastructure (Mar 2026)

### Problem

The "try defEq → suffices + converter → native_decide" pattern was duplicated
**6 times** across `finSumBound{Icc,List}Core` and `finSumWitness{Icc,List,AutoIcc,AutoList}Core`
(~35 lines each, ~210 total). Adding `finmatrix_bound` would create a 7th copy.

### Solution: `closeBridgeWithNativeDecide`

Extracted into `Tactic/BridgeNative.lean`:

```lean
def closeBridgeWithNativeDecide
    (goal : MVarId) (goalType : Lean.Expr)
    (proof checkMVar : Lean.Expr)
    (tacticName : String)
    (converterSteps : Array (TacticM Unit))
    : TacticM Unit
```

Logic:
1. `inferType proof` → `proofTy`
2. If `isDefEq proofTy goalType`: direct assign + `native_decide` on checkMVar
3. Else: suffMVar + converterMVar pattern, try converterSteps in sequence

Each caller provides its own converter steps inline:
- `finsum_bound`: `simp [Expr.eval, sumBodyRealEnv, ...] + norm_num`, then `push_cast + linarith`
- `finsum_witness` / `finmatrix_bound`: `intro h; exact h`, then `push_cast + linarith`

### Refactored files

- `FinSumBound.lean` — 2 blocks → 2 calls to `closeBridgeWithNativeDecide`
- `FinSumWitness.lean` — 4 blocks → 4 calls to `closeBridgeWithNativeDecide`
- Net: ~210 lines of duplication → ~40-line shared helper

## finmatrix_bound: matrix norm tactic (Mar 2026)

### Problem

Proving `finWeightedMatrixNorm ν M ≤ C` requires manually writing:
```lean
exact l1Weighted.finWeightedMatrixNorm_le_of_Q_le _ cols ν_q hcols hν (by native_decide)
```

For block-level `finiteBlockMatrixNorm ν A ≤ C`, users must decompose with
`fin_cases l <;> fin_cases j` producing L×L `native_decide` calls (9 for L=3).

### Design: generic bridge applier

`finmatrix_bound` is a generic "apply bridge term + native_decide" tactic.
Lives in RadiiPolynomial (not leancert) since its bridge lemmas and test data
are there. Imports `BridgeNative` from leancert for the shared helper:

```lean
syntax "finmatrix_bound" term : tactic
```

The user provides the bridge lemma fully applied except for the final `hle` argument:
```lean
finmatrix_bound (l1Weighted.finWeightedMatrixNorm_le_of_Q_le _ cols ν_q hcols hν)
```

The tactic:
1. Elaborates the bridge term
2. Infers its type — should be `(hle : X ≤ C) → goalType`
3. Creates mvar for `hle`, applies `bridgeExpr checkMVar`
4. Calls `closeBridgeWithNativeDecide` to close with `native_decide`

### Block extension (RadiiPolynomial — separate project)

`finiteBlockMatrixNormQ` computes the entire block norm in ℚ:
```lean
def finiteBlockMatrixNormQ (L N : ℕ) [NeZero L]
    (blockCols : Fin L → Fin L → Fin (N+1) → Array ℚ) (ν : ℚ) : ℚ :=
  Finset.univ.sup' Finset.univ_nonempty fun l =>
    ∑ j : Fin L, finWeightedMatrixNormQ (blockCols l j) ν N
```

Block bridge lemma `finiteBlockMatrixNorm_le_of_Q_le` reduces the entire block norm
to a single `native_decide`, eliminating the `fin_cases l <;> fin_cases j` decomposition.

Usage:
```lean
-- 1 native_decide instead of 9:
finmatrix_bound (finiteBlockMatrixNorm_le_of_Q_le _ blockCols ν_q hcols hν)
```

### Key insight

Matrix norm = max of sums — same computable structure as `finsum_bound` with an
extra `max` layer. Both `max` (via `Finset.sup'`) and `∑` are decidable over ℚ,
so `native_decide` handles the whole thing in one shot.
