/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Engine.FinSumDyadic
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Certified Euler–Mascheroni Constant Bounds

Fully machine-checked bounds for `Real.eulerMascheroniConstant`:

  0.5772151 ≤ γ ≤ 0.5772162      (width 1.1e-6; true value γ = 0.5772156649...)

**Sorry-free.** The verification runs inline via `native_decide` (~25 s build),
so unlike the li(2) development there is no lightweight-interface /
heavy-verification split: downstream projects import this file directly. The
`native_decide` dependency (`Lean.ofReduceBool`) is pinned by an axiom guard in
`Tests/AxiomAudit.lean`, the same trust shape as `PNT_PsiBounds` and the BKLNW
bounds already consumed by PNT+.

## Proof

Mathlib's strict sandwich at `N = 2^20`:

  eulerMascheroniSeq N < γ < eulerMascheroniSeq' N

where `eulerMascheroniSeq N = harmonic N - log (N+1)` and
`eulerMascheroniSeq' N = harmonic N - log N`. The sandwich gap is
`log (1 + 1/N) ≈ 9.5e-7`, which dictates the achievable width. Ingredients:

1. **Harmonic number.** `harmonic (2^20)` is enclosed to width `1e-10` by the
   reflective dyadic sum evaluator (`LeanCert.Engine.FinSumDyadic`) with the
   summand `1/k` expressed as `Expr.inv (Expr.var 0)`, at precision `-80`
   (accumulated outward-rounding error ≤ `2^20 · 2^(-79)` ≈ `2e-18`, far below
   the `4e-11` checker margins):

     14.4401597529 ≤ harmonic (2^20) ≤ 14.4401597530

2. **Logarithm.** `N = 2^20` makes `log N = 20 * log 2`, discharged by
   Mathlib's `Real.log_two_gt_d9` / `Real.log_two_lt_d9`. For the lower bound,
   `log (N + 1) ≤ log N + 1/N` via `Real.log_le_sub_one_of_pos`.

Tightening beyond ~1e-6 is structural, not incremental: the sandwich gap is
`1/N`, so each extra digit costs 10× the `native_decide` work (or an
Euler–Maclaurin midpoint refinement, which needs new analysis).
-/

namespace EulerMascheroni

open Real LeanCert.Core LeanCert.Engine

/-! ### Internal setup: summand expression, config, truncation index -/

/-- The harmonic summand `1/k` as a LeanCert expression (`var 0` = summation
index). -/
def body : Expr := Expr.inv (Expr.var 0)

theorem body_supported : ExprSupportedWithInv body :=
  ExprSupportedWithInv.inv (ExprSupportedWithInv.var 0)

/-- 80-bit dyadic precision. The summand is rational, so `taylorDepth` is
inert. -/
def cfg : DyadicConfig := { precision := -80 }

/-- Truncation index `N = 2^20`, chosen so that `log N = 20 * log 2` reduces
to Mathlib's decimal `log 2` bounds. -/
def N : ℕ := 2 ^ 20

/-! ### Bridge: Mathlib's `harmonic` as a `FinSumDyadic` sum -/

/-- `harmonic n` is the semantic sum that `finSumDyadic body 1 n` encloses. -/
theorem harmonic_eq_finsum (n : ℕ) :
    (harmonic n : ℝ) = ∑ k ∈ Finset.Icc 1 n, Expr.eval (sumBodyRealEnv k) body := by
  simp only [body, Expr.eval, sumBodyRealEnv]
  induction n with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_Icc_succ_top (Nat.one_le_iff_ne_zero.mpr (Nat.succ_ne_zero m)),
      harmonic_succ, ← ih]
    push_cast
    ring

/-! ### Verified harmonic number enclosure (native_decide) -/

/-- Lower bound `14.4401597529 ≤ harmonic (2^20)`
(true value `14.44015975293752...`; margin `3.7e-11`). -/
theorem harmonic_N_ge :
    (((144401597529 / 10 ^ 10 : ℚ)) : ℝ) ≤ (harmonic N : ℝ) := by
  rw [harmonic_eq_finsum]
  exact verify_finsum_lower_full_withInv body body_supported 1 N
    (144401597529 / 10 ^ 10) cfg (by norm_num [cfg]) (by native_decide)

/-- Upper bound `harmonic (2^20) ≤ 14.4401597530` (margin `6.2e-11`). -/
theorem harmonic_N_le :
    (harmonic N : ℝ) ≤ (((144401597530 / 10 ^ 10 : ℚ)) : ℝ) := by
  rw [harmonic_eq_finsum]
  exact verify_finsum_upper_full_withInv body body_supported 1 N
    (144401597530 / 10 ^ 10) cfg (by norm_num [cfg]) (by native_decide)

/-! ### Logarithm bounds at `N = 2^20` -/

theorem log_N_eq : Real.log (N : ℝ) = 20 * Real.log 2 := by
  have h : (N : ℝ) = (2 : ℝ) ^ (20 : ℕ) := by norm_num [N]
  rw [h, Real.log_pow]
  norm_num

/-- `log (N + 1) ≤ 20 * log 2 + 1/N` via `log x ≤ x - 1`. -/
theorem log_N_succ_le :
    Real.log ((N : ℝ) + 1) ≤ 20 * Real.log 2 + 1 / (N : ℝ) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by norm_num [N]
  have hsplit : Real.log ((N : ℝ) + 1)
      = Real.log (N : ℝ) + Real.log (((N : ℝ) + 1) / (N : ℝ)) := by
    rw [← Real.log_mul (by positivity) (by positivity)]
    congr 1
    field_simp
  have hlog1p : Real.log (((N : ℝ) + 1) / (N : ℝ)) ≤ ((N : ℝ) + 1) / (N : ℝ) - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  have hfrac : ((N : ℝ) + 1) / (N : ℝ) - 1 = 1 / (N : ℝ) := by
    field_simp
    ring
  rw [hsplit, log_N_eq]
  linarith [hfrac ▸ hlog1p]

/-! ### The certified γ bounds (public interface) -/

/-- Certified lower bound: γ ≥ 0.5772151.

From `eulerMascheroniSeq N < γ`:
`γ > harmonic N - log (N+1) ≥ 14.4401597529 - 20·0.6931471808 - 2^(-20)
   = 0.57721518322... ≥ 0.5772151`. -/
theorem gamma_lower : (0.5772151 : ℝ) ≤ Real.eulerMascheroniConstant := by
  have h := Real.eulerMascheroniSeq_lt_eulerMascheroniConstant N
  rw [Real.eulerMascheroniSeq] at h
  -- h : (harmonic N : ℝ) - log ((N : ℝ) + 1) < γ
  have hlog : Real.log ((N : ℝ) + 1) ≤ 20 * Real.log 2 + 1 / (N : ℝ) :=
    log_N_succ_le
  have hlog2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hH := harmonic_N_ge
  have hNval : (1 : ℝ) / (N : ℝ) = 1 / 1048576 := by norm_num [N]
  have hq : (((144401597529 / 10 ^ 10 : ℚ)) : ℝ) = 144401597529 / 10 ^ 10 := by
    push_cast
    norm_num
  rw [hq] at hH
  rw [hNval] at hlog
  nlinarith [h, hlog, hH]

/-- Certified upper bound: γ ≤ 0.5772162.

From `γ < eulerMascheroniSeq' N`:
`γ < harmonic N - log N ≤ 14.4401597530 - 20·0.6931471803
   = 0.5772161470 ≤ 0.5772162`. -/
theorem gamma_upper : Real.eulerMascheroniConstant ≤ (0.5772162 : ℝ) := by
  have h := Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' N
  have hN0 : N ≠ 0 := by norm_num [N]
  rw [Real.eulerMascheroniSeq', if_neg hN0] at h
  -- h : γ < (harmonic N : ℝ) - log (N : ℝ)
  have hlog : (13.862943606 : ℝ) < Real.log (N : ℝ) := by
    rw [log_N_eq]
    linarith [Real.log_two_gt_d9]
  have hH := harmonic_N_le
  have hq : (((144401597530 / 10 ^ 10 : ℚ)) : ℝ) = 144401597530 / 10 ^ 10 := by
    push_cast
    norm_num
  rw [hq] at hH
  nlinarith [h, hlog, hH]

/-- Combined bounds: γ ∈ [0.5772151, 0.5772162] (width 1.1e-6). -/
theorem gamma_bounds :
    Real.eulerMascheroniConstant ∈ Set.Icc (0.5772151 : ℝ) 0.5772162 :=
  Set.mem_Icc.mpr ⟨gamma_lower, gamma_upper⟩

/-- γ is approximately 0.57721565, to within 5.5e-7. -/
theorem gamma_approx :
    |Real.eulerMascheroniConstant - 0.57721565| ≤ 0.00000055 := by
  have h := gamma_bounds
  rw [Set.mem_Icc] at h
  rw [abs_le]
  constructor <;> [linarith [h.1]; linarith [h.2]]

end EulerMascheroni
