/-
Copyright (c) 2025 LeanCert Contributors. All rights reserved.
Released under AGPL-3.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.ML.Optimized.IntervalArray
import LeanCert.ML.Optimized.QuantizedLayer
import Mathlib.Data.Matrix.Basic

/-!
# Quantized Matrix Operations

This module provides the foundation for Transformer verification:
Matrix-Matrix multiplication for Intervals.

## Key Definitions

* `IntMatrix` - Flattened array of integers (row-major)
* `IntervalMatrix` - Structure-of-Arrays interval matrix
* `matmul` - Verified interval matrix multiplication
-/

namespace LeanCert.ML.Optimized

open LeanCert.Core

/-! ### Integer Matrix (Data Layer) -/

/-- A dense integer matrix stored in row-major format. -/
structure IntMatrix (rows cols : Nat) where
  data : Array Int
  size_eq : data.size = rows * cols
  deriving Repr

namespace IntMatrix

/-- Helper lemma for row-major index bounds -/
private theorem row_major_lt_of_lt_mul_of_lt {r c i j : Nat}
    (hi : i < r) (hj : j < c) : i * c + j < r * c := by
  calc i * c + j < i * c + c := Nat.add_lt_add_left hj _
    _ = (i + 1) * c := by ring
    _ ≤ r * c := Nat.mul_le_mul_right c (Nat.succ_le_of_lt hi)

/-- Get element at (r, c) -/
@[inline] def get (M : IntMatrix r c) (i j : Nat) (hi : i < r) (hj : j < c) : Int :=
  -- Row-major index: i * c + j
  let idx := i * c + j
  M.data[idx]'(by rw [M.size_eq]; exact row_major_lt_of_lt_mul_of_lt hi hj)

/-- Helper: convert k < r * c to k < c * r -/
private theorem lt_mul_comm {k r c : Nat} (h : k < r * c) : k < c * r := by
  rwa [Nat.mul_comm]

/-- Helper function to compute element at flat index -/
private def flatToElem {r c : Nat} (f : Fin r → Fin c → Int) (hc : c ≠ 0)
    (k : Fin (r * c)) : Int :=
  let i := k / c
  let j := k % c
  have hi : i < r := Nat.div_lt_of_lt_mul (lt_mul_comm k.isLt)
  have hj : j < c := Nat.mod_lt _ (Nat.pos_of_ne_zero hc)
  f ⟨i, hi⟩ ⟨j, hj⟩

/-- Create a matrix from a function -/
def ofFn {r c : Nat} (f : Fin r → Fin c → Int) : IntMatrix r c :=
  if hc : c = 0 then
    ⟨#[], by simp [hc]⟩
  else
    { data := Array.ofFn (flatToElem f hc)
      size_eq := Array.size_ofFn }

/-- Get an element from an ofFn matrix -/
@[simp] theorem ofFn_get {r c : Nat} (f : Fin r → Fin c → Int) (i : Fin r) (j : Fin c) :
    (ofFn f).get i j i.isLt j.isLt = f i j := by
  simp only [ofFn, get]
  split_ifs with hc
  · -- c = 0 case: impossible since j : Fin c requires c > 0
    exact absurd (Nat.eq_zero_of_not_pos (by simp [hc] : ¬ 0 < c)) (Nat.ne_zero_of_lt j.isLt)
  · -- c ≠ 0 case: need to show the array lookup equals f i j
    simp only [Array.getElem_ofFn, flatToElem]
    have hc_pos := Nat.pos_of_ne_zero hc
    -- i * c + j with j < c: div gives i, mod gives j
    have h_div : (↑i * c + ↑j) / c = ↑i := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hc_pos]
      rw [Nat.div_eq_of_lt j.isLt, Nat.zero_add]
    have h_mod : (↑i * c + ↑j) % c = ↑j := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right]
      exact Nat.mod_eq_of_lt j.isLt
    simp only [h_div, h_mod]

/-- Matrix Transpose -/
def transpose {r c : Nat} (M : IntMatrix r c) : IntMatrix c r :=
  ofFn fun i j => M.get j i j.isLt i.isLt

/-- Zero matrix -/
def zero (r c : Nat) : IntMatrix r c :=
  ofFn fun _ _ => 0

end IntMatrix

/-! ### Interval Matrix (Verification Layer) -/

/-- Interval Matrix in SoA layout (separate lo/hi matrices) -/
structure IntervalMatrix (rows cols : Nat) where
  lo : IntMatrix rows cols
  hi : IntMatrix rows cols

namespace IntervalMatrix

/-- Get the interval bounds at (i, j) as a pair -/
def getBounds (M : IntervalMatrix r c) (i j : Nat) (hi : i < r) (hj : j < c) : Int × Int :=
  let l := M.lo.get i j hi hj
  let h := M.hi.get i j hi hj
  (l, h)

/--
  **Interval Arithmetic Product**

  Computes [l1, h1] * [l2, h2].
  Result lo = min(l1*l2, l1*h2, h1*l2, h1*h2)
  Result hi = max(l1*l2, l1*h2, h1*l2, h1*h2)
-/
@[inline] def intervalMul (l1 h1 l2 h2 : Int) : Int × Int :=
  let p1 := l1 * l2
  let p2 := l1 * h2
  let p3 := h1 * l2
  let p4 := h1 * h2
  let lo := min (min p1 p2) (min p3 p4)
  let hi := max (max p1 p2) (max p3 p4)
  (lo, hi)

/-- Interval addition of two pairs -/
@[inline] def intervalAdd (l1 h1 l2 h2 : Int) : Int × Int :=
  (l1 + l2, h1 + h2)

/--
  **Matrix-Matrix Multiplication**

  C = A × B where A is (n × m) and B is (m × p).

  This implements the standard O(N³) loop but lifting operations to intervals.
  Unlike vector-matrix mul, we cannot easily decompose into Pos/Neg weights
  because both inputs are variable intervals.
-/
def matmul {n m p : Nat}
    (A : IntervalMatrix n m) (B : IntervalMatrix m p) : IntervalMatrix n p :=
  let C_lo := IntMatrix.ofFn fun i k =>
    (List.finRange m).foldl (fun sum (j : Fin m) =>
      -- Get Interval A[i,j]
      let a_lo := A.lo.get i j i.isLt j.isLt
      let a_hi := A.hi.get i j i.isLt j.isLt

      -- Get Interval B[j,k]
      let b_lo := B.lo.get j k j.isLt k.isLt
      let b_hi := B.hi.get j k j.isLt k.isLt

      -- Multiply Intervals
      let (prod_lo, _) := intervalMul a_lo a_hi b_lo b_hi
      sum + prod_lo
    ) 0

  let C_hi := IntMatrix.ofFn fun i k =>
    (List.finRange m).foldl (fun sum (j : Fin m) =>
      let a_lo := A.lo.get i j i.isLt j.isLt
      let a_hi := A.hi.get i j i.isLt j.isLt
      let b_lo := B.lo.get j k j.isLt k.isLt
      let b_hi := B.hi.get j k j.isLt k.isLt

      let (_, prod_hi) := intervalMul a_lo a_hi b_lo b_hi
      sum + prod_hi
    ) 0

  ⟨C_lo, C_hi⟩

/-- Transpose an interval matrix -/
def transpose {r c : Nat} (M : IntervalMatrix r c) : IntervalMatrix c r :=
  ⟨M.lo.transpose, M.hi.transpose⟩

/-- Zero interval matrix (all zeros) -/
def zero (r c : Nat) : IntervalMatrix r c :=
  ⟨IntMatrix.zero r c, IntMatrix.zero r c⟩

/-- Create from function -/
def ofFn {r c : Nat} (f : Fin r → Fin c → Int × Int) : IntervalMatrix r c :=
  ⟨IntMatrix.ofFn fun i j => (f i j).1, IntMatrix.ofFn fun i j => (f i j).2⟩

end IntervalMatrix

/-! ### Semantics and Correctness -/

/-- Value of integer as real given an exponent (2^exp scaling) -/
noncomputable def intVal (x : Int) (exp : Int) : ℝ := x * (2 : ℝ) ^ exp

/-- Multiplication of scaled values: intVal x e * intVal y e = intVal (x*y) (e+e) -/
theorem intVal_mul (x y : Int) (e : Int) :
    intVal x e * intVal y e = intVal (x * y) (e + e) := by
  unfold intVal
  simp only [Int.cast_mul]
  calc (x : ℝ) * (2 : ℝ) ^ e * (↑y * (2 : ℝ) ^ e)
      = (x : ℝ) * y * ((2 : ℝ) ^ e * (2 : ℝ) ^ e) := by ring
    _ = (x : ℝ) * y * (2 : ℝ) ^ (e + e) := by rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]

/-- intVal distributes over addition -/
theorem intVal_add (x y : Int) (e : Int) :
    intVal x e + intVal y e = intVal (x + y) e := by
  simp only [intVal, Int.cast_add]
  ring

/-- Value of integer matrix entry given an exponent -/
noncomputable def IntMatrix.valAt (M : IntMatrix r c) (exp : Int) (i : Fin r) (j : Fin c) : ℝ :=
  intVal (M.get i j i.isLt j.isLt) exp

/-- Membership in IntervalMatrix -/
def IntervalMatrix.mem {r c : Nat} (M : IntervalMatrix r c) (exp : Int)
    (A_real : Matrix (Fin r) (Fin c) ℝ) : Prop :=
  ∀ (i : Fin r) (j : Fin c),
    M.lo.valAt exp i j ≤ A_real i j ∧
    A_real i j ≤ M.hi.valAt exp i j

/-! ### Foldl to Finset.sum conversion -/

/-- Generalized: foldl with function application equals init + sum of mapped list -/
private theorem foldl_add_f_eq_foldl_map {α β : Type*} [AddCommMonoid α]
    (f : β → α) (l : List β) (init : α) :
    l.foldl (fun acc b => acc + f b) init = init + (l.map f).sum := by
  induction l generalizing init with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, List.map_cons, List.sum_cons]
    rw [ih]
    abel

/-- Key lemma: foldl with addition over List.finRange equals Finset.univ.sum.
    This converts the computational foldl in matmul to the mathematical Finset.sum. -/
theorem finRange_foldl_add_eq_sum {α : Type*} [AddCommMonoid α] {m : Nat} (f : Fin m → α) :
    (List.finRange m).foldl (fun acc j => acc + f j) 0 = Finset.univ.sum f := by
  rw [foldl_add_f_eq_foldl_map, zero_add, Fin.sum_univ_def]

/-! ### Int to Real cast lemmas for foldl -/

/-- Int.cast distributes over foldl with addition (generalized) -/
private theorem Int_cast_foldl_add_gen {β : Type*} (l : List β) (f : β → Int) (init : Int) :
    ((l.foldl (fun acc b => acc + f b) init : Int) : ℝ) =
    l.foldl (fun acc b => acc + (f b : ℝ)) (init : ℝ) := by
  induction l generalizing init with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons]
    rw [ih (init + f x)]
    simp only [Int.cast_add]

/-- Int.cast distributes over foldl with addition -/
theorem Int_cast_foldl_add {β : Type*} (l : List β) (f : β → Int) :
    ((l.foldl (fun acc b => acc + f b) 0 : Int) : ℝ) =
    l.foldl (fun acc b => acc + (f b : ℝ)) (0 : ℝ) := by
  have h := Int_cast_foldl_add_gen l f 0
  simp only [Int.cast_zero] at h
  exact h

/-! ### Helper for sum inequalities -/

/-- Sum inequality for intervals: if each term is bounded, sum is bounded -/
private theorem sum_interval_le {m : Nat}
    (f_lo f f_hi : Fin m → ℝ)
    (h : ∀ j, f_lo j ≤ f j ∧ f j ≤ f_hi j) :
    Finset.univ.sum f_lo ≤ Finset.univ.sum f ∧
    Finset.univ.sum f ≤ Finset.univ.sum f_hi := by
  constructor
  · exact Finset.sum_le_sum (fun j _ => (h j).1)
  · exact Finset.sum_le_sum (fun j _ => (h j).2)

/-! ### Interval Multiplication Soundness -/

/-- Helper: for x ∈ [a₁, a₂], x*y lies between endpoint products. -/
private theorem mul_mem_endpoints_left {x a₁ a₂ y : ℝ}
    (ha : a₁ ≤ x ∧ x ≤ a₂) :
    min (a₁ * y) (a₂ * y) ≤ x * y ∧ x * y ≤ max (a₁ * y) (a₂ * y) := by
  by_cases! hy : 0 ≤ y
  · have h1 : a₁ * y ≤ x * y := mul_le_mul_of_nonneg_right ha.1 hy
    have h2 : x * y ≤ a₂ * y := mul_le_mul_of_nonneg_right ha.2 hy
    exact ⟨le_trans (min_le_left _ _) h1, le_trans h2 (le_max_right _ _)⟩
  · have hy' := le_of_lt hy
    have h1 : a₂ * y ≤ x * y := mul_le_mul_of_nonpos_right ha.2 hy'
    have h2 : x * y ≤ a₁ * y := mul_le_mul_of_nonpos_right ha.1 hy'
    exact ⟨le_trans (min_le_right _ _) h1, le_trans h2 (le_max_left _ _)⟩

/-- Helper: for y ∈ [b₁, b₂], x*y lies between endpoint products. -/
private theorem mul_mem_endpoints_right {y b₁ b₂ x : ℝ}
    (hb : b₁ ≤ y ∧ y ≤ b₂) :
    min (x * b₁) (x * b₂) ≤ x * y ∧ x * y ≤ max (x * b₁) (x * b₂) := by
  by_cases! hx : 0 ≤ x
  · have h1 : x * b₁ ≤ x * y := mul_le_mul_of_nonneg_left hb.1 hx
    have h2 : x * y ≤ x * b₂ := mul_le_mul_of_nonneg_left hb.2 hx
    exact ⟨le_trans (min_le_left _ _) h1, le_trans h2 (le_max_right _ _)⟩
  · have hx' := le_of_lt hx
    have h1 : x * b₂ ≤ x * y := mul_le_mul_of_nonpos_left hb.2 hx'
    have h2 : x * y ≤ x * b₁ := mul_le_mul_of_nonpos_left hb.1 hx'
    exact ⟨le_trans (min_le_right _ _) h1, le_trans h2 (le_max_left _ _)⟩

/-- Lower bound: xy ≥ min of corner products -/
private theorem mul_lower_bound {x y a₁ a₂ b₁ b₂ : ℝ}
    (ha : a₁ ≤ x ∧ x ≤ a₂) (hb : b₁ ≤ y ∧ y ≤ b₂) :
    min (min (a₁ * b₁) (a₁ * b₂)) (min (a₂ * b₁) (a₂ * b₂)) ≤ x * y := by
  have h1 := (mul_mem_endpoints_left (y := y) ha).1
  by_cases! hcmp : a₁ * y ≤ a₂ * y
  · rw [min_eq_left hcmp] at h1
    have h2 := (mul_mem_endpoints_right hb (x := a₁)).1
    calc min (min (a₁ * b₁) (a₁ * b₂)) (min (a₂ * b₁) (a₂ * b₂))
        ≤ min (a₁ * b₁) (a₁ * b₂) := min_le_left _ _
      _ ≤ a₁ * y := h2
      _ ≤ x * y := h1
  · rw [min_eq_right (le_of_lt hcmp)] at h1
    have h2 := (mul_mem_endpoints_right hb (x := a₂)).1
    calc min (min (a₁ * b₁) (a₁ * b₂)) (min (a₂ * b₁) (a₂ * b₂))
        ≤ min (a₂ * b₁) (a₂ * b₂) := min_le_right _ _
      _ ≤ a₂ * y := h2
      _ ≤ x * y := h1

/-- Upper bound: xy ≤ max of corner products -/
private theorem mul_upper_bound {x y a₁ a₂ b₁ b₂ : ℝ}
    (ha : a₁ ≤ x ∧ x ≤ a₂) (hb : b₁ ≤ y ∧ y ≤ b₂) :
    x * y ≤ max (max (a₁ * b₁) (a₁ * b₂)) (max (a₂ * b₁) (a₂ * b₂)) := by
  have h1 := (mul_mem_endpoints_left (y := y) ha).2
  by_cases! hcmp : a₁ * y ≤ a₂ * y
  · rw [max_eq_right hcmp] at h1
    have h2 := (mul_mem_endpoints_right hb (x := a₂)).2
    calc x * y
        ≤ a₂ * y := h1
      _ ≤ max (a₂ * b₁) (a₂ * b₂) := h2
      _ ≤ max (max (a₁ * b₁) (a₁ * b₂)) (max (a₂ * b₁) (a₂ * b₂)) := le_max_right _ _
  · rw [max_eq_left (le_of_lt hcmp)] at h1
    have h2 := (mul_mem_endpoints_right hb (x := a₁)).2
    calc x * y
        ≤ a₁ * y := h1
      _ ≤ max (a₁ * b₁) (a₁ * b₂) := h2
      _ ≤ max (max (a₁ * b₁) (a₁ * b₂)) (max (a₂ * b₁) (a₂ * b₂)) := le_max_left _ _

/-- Key lemma: product lies in convex hull of corner products -/
private theorem mul_mem_corners {x y a₁ a₂ b₁ b₂ : ℝ}
    (ha : a₁ ≤ x ∧ x ≤ a₂) (hb : b₁ ≤ y ∧ y ≤ b₂) :
    min (min (a₁ * b₁) (a₁ * b₂)) (min (a₂ * b₁) (a₂ * b₂)) ≤ x * y ∧
    x * y ≤ max (max (a₁ * b₁) (a₁ * b₂)) (max (a₂ * b₁) (a₂ * b₂)) :=
  ⟨mul_lower_bound ha hb, mul_upper_bound ha hb⟩

/-- The interval multiplication is sound: if x ∈ [l1, h1] and y ∈ [l2, h2],
    then x * y ∈ [intervalMul.lo, intervalMul.hi] -/
theorem intervalMul_sound (l1 h1 l2 h2 : Int) (x y : ℝ)
    (hx_lo : (l1 : ℝ) ≤ x) (hx_hi : x ≤ h1)
    (hy_lo : (l2 : ℝ) ≤ y) (hy_hi : y ≤ h2) :
    let (lo, hi) := IntervalMatrix.intervalMul l1 h1 l2 h2
    (lo : ℝ) ≤ x * y ∧ x * y ≤ hi := by
  simp only [IntervalMatrix.intervalMul]
  -- Apply mul_mem_corners with Int→ℝ casts
  have hcorners := mul_mem_corners ⟨hx_lo, hx_hi⟩ ⟨hy_lo, hy_hi⟩
  -- Convert the integer products to real
  have p1_eq : ((l1 * l2 : Int) : ℝ) = (l1 : ℝ) * l2 := Int.cast_mul l1 l2
  have p2_eq : ((l1 * h2 : Int) : ℝ) = (l1 : ℝ) * h2 := Int.cast_mul l1 h2
  have p3_eq : ((h1 * l2 : Int) : ℝ) = (h1 : ℝ) * l2 := Int.cast_mul h1 l2
  have p4_eq : ((h1 * h2 : Int) : ℝ) = (h1 : ℝ) * h2 := Int.cast_mul h1 h2
  -- min/max of integers cast to real = min/max of casted integers
  simp only [Int.cast_min, Int.cast_max, p1_eq, p2_eq, p3_eq, p4_eq]
  exact hcorners

/-- Scaled version of intervalMul_sound using intVal with exponents.
    If x ∈ [intVal l1 exp, intVal h1 exp] and y ∈ [intVal l2 exp, intVal h2 exp],
    then x * y ∈ [intVal lo (exp+exp), intVal hi (exp+exp)] where (lo, hi) = intervalMul l1 h1 l2 h2. -/
theorem intervalMul_sound_scaled (l1 h1 l2 h2 : Int) (x y : ℝ) (exp : Int)
    (hx_lo : intVal l1 exp ≤ x) (hx_hi : x ≤ intVal h1 exp)
    (hy_lo : intVal l2 exp ≤ y) (hy_hi : y ≤ intVal h2 exp) :
    let (lo, hi) := IntervalMatrix.intervalMul l1 h1 l2 h2
    intVal lo (exp + exp) ≤ x * y ∧ x * y ≤ intVal hi (exp + exp) := by
  -- Unfold intVal in hypotheses
  unfold intVal at hx_lo hx_hi hy_lo hy_hi

  -- Key: scale factor 2^exp is positive
  have hpow_pos : (0 : ℝ) < (2 : ℝ) ^ exp := zpow_pos (by norm_num : (0 : ℝ) < 2) exp
  have hpow_ne : (2 : ℝ) ^ exp ≠ 0 := ne_of_gt hpow_pos

  -- Define scaled versions: x' = x / 2^exp, y' = y / 2^exp
  set scale := (2 : ℝ) ^ exp
  set x' := x / scale
  set y' := y / scale

  -- Bounds on x' and y' (unscaled)
  -- le_div_iff₀: a ≤ b / c ↔ a * c ≤ b
  -- div_le_iff₀: a / b ≤ c ↔ a ≤ c * b
  have hx'_lo : (l1 : ℝ) ≤ x' := by
    rw [le_div_iff₀ hpow_pos]
    exact hx_lo
  have hx'_hi : x' ≤ h1 := by
    rw [div_le_iff₀ hpow_pos]
    exact hx_hi
  have hy'_lo : (l2 : ℝ) ≤ y' := by
    rw [le_div_iff₀ hpow_pos]
    exact hy_lo
  have hy'_hi : y' ≤ h2 := by
    rw [div_le_iff₀ hpow_pos]
    exact hy_hi

  -- Apply unscaled soundness to x', y'
  have hsound := intervalMul_sound l1 h1 l2 h2 x' y' hx'_lo hx'_hi hy'_lo hy'_hi

  -- Scale back: x * y = x' * y' * (2^exp)^2 = x' * y' * 2^(exp+exp)
  have heq : x * y = x' * y' * (scale * scale) := by
    have h1 : x' * scale = x := div_mul_cancel₀ x hpow_ne
    have h2 : y' * scale = y := div_mul_cancel₀ y hpow_ne
    calc x * y = (x' * scale) * (y' * scale) := by rw [h1, h2]
      _ = x' * y' * (scale * scale) := by ring
  have hscale_sq : scale * scale = (2 : ℝ) ^ (exp + exp) := by
    rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]

  -- Get lo and hi from intervalMul
  set result := IntervalMatrix.intervalMul l1 h1 l2 h2
  have hlo : (result.1 : ℝ) ≤ x' * y' := hsound.1
  have hhi : x' * y' ≤ result.2 := hsound.2

  constructor
  · -- Lower bound
    rw [intVal, heq, hscale_sq]
    exact mul_le_mul_of_nonneg_right hlo (zpow_nonneg (by norm_num) _)
  · -- Upper bound
    rw [intVal, heq, hscale_sq]
    exact mul_le_mul_of_nonneg_right hhi (zpow_nonneg (by norm_num) _)

/-- **Soundness of Matrix Transpose**

  If A_real ∈ A_interval, then A_realᵀ ∈ A_intervalᵀ.
  The exponent is preserved. -/
theorem mem_transpose {r c : Nat}
    (M : IntervalMatrix r c) (exp : Int)
    (A_real : Matrix (Fin r) (Fin c) ℝ)
    (hM : M.mem exp A_real) :
    M.transpose.mem exp A_real.transpose := by
  intro j i
  -- M.transpose.lo[j,i] = M.lo[i,j] and similarly for hi
  simp only [IntervalMatrix.transpose, IntMatrix.valAt, IntMatrix.transpose,
             IntMatrix.ofFn_get, Matrix.transpose_apply]
  exact hM i j

/--
  **Main Theorem: Soundness of Matrix Multiplication**

  If A_real ∈ A_interval and B_real ∈ B_interval, then
  (A_real * B_real) ∈ (A_interval * B_interval).

  Note: Exponents add. If A has exp `e` and B has exp `e`, result has `2e`.
-/
theorem mem_matmul {n m p : Nat}
    (A : IntervalMatrix n m) (B : IntervalMatrix m p)
    (Ar : Matrix (Fin n) (Fin m) ℝ) (Br : Matrix (Fin m) (Fin p) ℝ)
    (exp : Int)
    (hA : A.mem exp Ar) (hB : B.mem exp Br) :
    (A.matmul B).mem (exp + exp) (Ar * Br) := by
  intro i k
  simp only [Matrix.mul_apply]

  -- Define helper functions for the products
  let prod_lo (j : Fin m) : Int :=
    (IntervalMatrix.intervalMul
      (A.lo.get i j i.isLt j.isLt) (A.hi.get i j i.isLt j.isLt)
      (B.lo.get j k j.isLt k.isLt) (B.hi.get j k j.isLt k.isLt)).1
  let prod_hi (j : Fin m) : Int :=
    (IntervalMatrix.intervalMul
      (A.lo.get i j i.isLt j.isLt) (A.hi.get i j i.isLt j.isLt)
      (B.lo.get j k j.isLt k.isLt) (B.hi.get j k j.isLt k.isLt)).2

  -- Step 1: For each j, Ar[i,j] * Br[j,k] is bounded by intVal prod_lo/hi (exp+exp)
  have h_term : ∀ j : Fin m,
      intVal (prod_lo j) (exp + exp) ≤ Ar i j * Br j k ∧
      Ar i j * Br j k ≤ intVal (prod_hi j) (exp + exp) := fun j => by
    have hAj := hA i j
    have hBj := hB j k
    exact intervalMul_sound_scaled
      (A.lo.get i j i.isLt j.isLt) (A.hi.get i j i.isLt j.isLt)
      (B.lo.get j k j.isLt k.isLt) (B.hi.get j k j.isLt k.isLt)
      (Ar i j) (Br j k) exp
      hAj.1 hAj.2 hBj.1 hBj.2

  -- Step 2: Sum inequality - sum of bounds bounds the sum
  have h_sum := sum_interval_le
    (fun j => intVal (prod_lo j) (exp + exp))
    (fun j => Ar i j * Br j k)
    (fun j => intVal (prod_hi j) (exp + exp))
    h_term

  -- Step 3: Relate the foldl computation to intVal of sum
  -- C_lo[i,k] = foldl (fun sum j => sum + prod_lo j) 0
  -- We need: intVal (C_lo[i,k]) (exp+exp) = ∑ j, intVal (prod_lo j) (exp+exp)

  -- First, show the foldl equals sum of integers
  have h_lo_foldl : (A.matmul B).lo.get i k i.isLt k.isLt =
      (List.finRange m).foldl (fun sum j => sum + prod_lo j) 0 := by
    simp only [IntervalMatrix.matmul, IntMatrix.ofFn_get]
    rfl
  have h_hi_foldl : (A.matmul B).hi.get i k i.isLt k.isLt =
      (List.finRange m).foldl (fun sum j => sum + prod_hi j) 0 := by
    simp only [IntervalMatrix.matmul, IntMatrix.ofFn_get]
    rfl

  -- Convert foldl to Finset.sum
  have h_lo_sum : (List.finRange m).foldl (fun sum j => sum + prod_lo j) 0 =
      Finset.univ.sum prod_lo := finRange_foldl_add_eq_sum prod_lo
  have h_hi_sum : (List.finRange m).foldl (fun sum j => sum + prod_hi j) 0 =
      Finset.univ.sum prod_hi := finRange_foldl_add_eq_sum prod_hi

  -- intVal distributes over sum: intVal (∑ x) e = ∑ (intVal x e)
  have h_intVal_sum_lo : intVal (Finset.univ.sum prod_lo) (exp + exp) =
      Finset.univ.sum (fun j => intVal (prod_lo j) (exp + exp)) := by
    simp only [intVal, Int.cast_sum, Finset.sum_mul]
  have h_intVal_sum_hi : intVal (Finset.univ.sum prod_hi) (exp + exp) =
      Finset.univ.sum (fun j => intVal (prod_hi j) (exp + exp)) := by
    simp only [intVal, Int.cast_sum, Finset.sum_mul]

  -- Combine everything
  simp only [IntMatrix.valAt, h_lo_foldl, h_hi_foldl, h_lo_sum, h_hi_sum,
             h_intVal_sum_lo, h_intVal_sum_hi]
  exact h_sum

end LeanCert.ML.Optimized
