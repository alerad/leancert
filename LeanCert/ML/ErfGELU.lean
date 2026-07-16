/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.ML.IntervalVector
import LeanCert.Engine.Eval.Core

/-!
# Exact erf-GELU Feed-Forward Blocks

PyTorch `nn.GELU()` defaults to the exact erf form

`gelu(x) = 0.5 * x * (1 + erf(x / sqrt 2))`.

This module provides a computable interval forward pass for the architecture
`Linear -> erf-GELU -> Linear`, using LeanCert's verified `erfInterval`
primitive. It intentionally lives beside the transformer tanh-GELU
approximation instead of replacing it.
-/

namespace LeanCert.ML

open LeanCert.Core
open LeanCert.Engine

/-- Real specification of PyTorch's default exact GELU. -/
noncomputable def Real.erfGELU (x : ℝ) : ℝ :=
  (1 / 2 : ℝ) * x * (1 + Real.erf (x / Real.sqrt 2))

/-- A rational interval enclosing `1 / sqrt 2`. -/
def erfGELUInvSqrt2 : IntervalRat :=
  ⟨7071067811865475 / 10000000000000000,
    7071067811865476 / 10000000000000000,
    by norm_num⟩

/-- Computable interval enclosure for exact erf-GELU over rational intervals. -/
def erfGELUIntervalRat (I : IntervalRat) (taylorDepth : Nat := 15) : IntervalRat :=
  let arg := IntervalRat.mul I erfGELUInvSqrt2
  let erfArg := erfInterval arg taylorDepth
  let onePlus := IntervalRat.add (IntervalRat.singleton 1) erfArg
  let halfX := IntervalRat.scale (1 / 2) I
  IntervalRat.mul halfX onePlus

/-- The constant interval used by exact GELU contains `1 / √2`. -/
theorem mem_erfGELUInvSqrt2 :
    1 / Real.sqrt 2 ∈ erfGELUInvSqrt2 := by
  have hsqrt_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsqrt_sq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  simp only [erfGELUInvSqrt2, IntervalRat.mem_def]
  constructor
  · rw [le_div_iff₀ hsqrt_pos]
    have hconst :
        (((7071067811865475 / 10000000000000000 : ℚ) : ℝ) ^ 2) * 2 < 1 := by
      norm_num
    nlinarith [sq_nonneg
      (Real.sqrt 2 - ((7071067811865475 / 10000000000000000 : ℚ) : ℝ))]
  · rw [div_le_iff₀ hsqrt_pos]
    have hconst : 1 <
        (((7071067811865476 / 10000000000000000 : ℚ) : ℝ) ^ 2) * 2 := by
      norm_num
    nlinarith [sq_nonneg
      (Real.sqrt 2 - ((7071067811865476 / 10000000000000000 : ℚ) : ℝ))]

/-- Soundness of the rational exact erf-GELU enclosure. -/
theorem mem_erfGELUIntervalRat {x : ℝ} {I : IntervalRat} (hx : x ∈ I)
    (taylorDepth : Nat := 15) :
    Real.erfGELU x ∈ erfGELUIntervalRat I taylorDepth := by
  have harg : x / Real.sqrt 2 ∈ IntervalRat.mul I erfGELUInvSqrt2 := by
    have hmul := IntervalRat.mem_mul hx mem_erfGELUInvSqrt2
    convert hmul using 1
    field_simp [ne_of_gt (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2))]
  have herf := mem_erfInterval harg taylorDepth
  have hone := IntervalRat.mem_add (IntervalRat.mem_singleton (1 : ℚ)) herf
  have hhalf := IntervalRat.mem_scale (1 / 2) hx
  have hresult := IntervalRat.mem_mul hhalf hone
  simpa [Real.erfGELU, erfGELUIntervalRat] using hresult

/-- Computable interval enclosure for exact erf-GELU over dyadic intervals. -/
def erfGELUInterval (I : IntervalDyadic) (prec : Int := -53)
    (taylorDepth : Nat := 15) : IntervalDyadic :=
  IntervalDyadic.ofIntervalRat (erfGELUIntervalRat I.toIntervalRat taylorDepth) prec

/-- Soundness of the dyadic exact erf-GELU enclosure. -/
theorem mem_erfGELUInterval {x : ℝ} {I : IntervalDyadic} (hx : x ∈ I)
    (prec : Int := -53) (taylorDepth : Nat := 15) (hprec : prec ≤ 0 := by norm_num) :
    Real.erfGELU x ∈ erfGELUInterval I prec taylorDepth := by
  apply IntervalDyadic.mem_ofIntervalRat
  · exact mem_erfGELUIntervalRat (IntervalDyadic.mem_toIntervalRat.mp hx) taylorDepth
  · exact hprec

/-- Vectorized exact erf-GELU interval transform. -/
def erfGELUVector (v : IntervalVector) (prec : Int := -53)
    (taylorDepth : Nat := 15) : IntervalVector :=
  v.map (fun I => erfGELUInterval I prec taylorDepth)

/-- Componentwise soundness of `erfGELUVector`. -/
theorem mem_erfGELUVector {xs : List ℝ} {Is : IntervalVector}
    (hlen : xs.length = Is.length)
    (hmem : ∀ i, (hi : i < Is.length) → xs[i]'(by omega) ∈ Is[i]'hi)
    (prec : Int := -53) (taylorDepth : Nat := 15) (hprec : prec ≤ 0 := by norm_num) :
    ∀ i, (hi : i < Is.length) →
      Real.erfGELU (xs[i]'(by omega)) ∈
        (erfGELUVector Is prec taylorDepth)[i]'(by simpa [erfGELUVector] using hi) := by
  intro i hi
  simp only [erfGELUVector, List.getElem_map]
  exact mem_erfGELUInterval (hmem i hi) prec taylorDepth hprec

/-- Pure affine layer: no baked-in activation. -/
structure AffineLayer where
  weights : List (List ℚ)
  bias : List ℚ
  deriving Repr

namespace AffineLayer

/-- Real affine forward pass. -/
noncomputable def forwardReal (l : AffineLayer) (x : List ℝ) : List ℝ :=
  LeanCert.Engine.IntervalVector.realAddBias
    (LeanCert.Engine.IntervalVector.realMatVecMul l.weights x)
    l.bias

/-- Interval affine forward pass. -/
def forwardInterval (l : AffineLayer) (x : IntervalVector)
    (prec : Int := -53) : IntervalVector :=
  LeanCert.Engine.IntervalVector.addBias
    (LeanCert.Engine.IntervalVector.matVecMul l.weights x prec)
    l.bias
    prec

/-- Soundness of an affine layer under explicit matrix dimensions. -/
theorem forwardInterval_correct (l : AffineLayer) {xs : List ℝ} {Is : IntervalVector}
    (hrows : ∀ row ∈ l.weights, row.length = Is.length)
    (hmem : List.Forall₂ (fun x I => x ∈ I) xs Is)
    (hbias : l.bias.length = l.weights.length)
    (prec : Int := -53) (hprec : prec ≤ 0 := by norm_num) :
    List.Forall₂ (fun y J => y ∈ J) (l.forwardReal xs) (l.forwardInterval Is prec) := by
  let matReal := LeanCert.Engine.IntervalVector.realMatVecMul l.weights xs
  let matInterval := LeanCert.Engine.IntervalVector.matVecMul l.weights Is prec
  have hmatlen : matReal.length = matInterval.length := by
    simp [matReal, matInterval, LeanCert.Engine.IntervalVector.realMatVecMul,
      LeanCert.Engine.IntervalVector.matVecMul]
  have hxlen : xs.length = Is.length := hmem.length_eq
  have hmatmem : ∀ i, (hi : i < matInterval.length) →
      matReal[i]'(by omega) ∈ matInterval[i]'hi := by
    intro i hi
    have hiW : i < l.weights.length := by
      simpa [matInterval, LeanCert.Engine.IntervalVector.matVecMul] using hi
    simpa [matReal, matInterval] using
      (LeanCert.Engine.IntervalVector.mem_matVecMul hrows hmem.length_eq
        (fun _ hj => hmem.get (by simpa [hxlen] using hj) hj) prec hprec i hiW)
  have hbias' : l.bias.length = matInterval.length := by
    simpa [matInterval, LeanCert.Engine.IntervalVector.matVecMul] using hbias
  have hadd := LeanCert.Engine.IntervalVector.mem_addBias hmatlen hbias' hmatmem prec hprec
  rw [List.forall₂_iff_get]
  constructor
  · simp only [forwardReal, forwardInterval, LeanCert.Engine.IntervalVector.realAddBias,
      LeanCert.Engine.IntervalVector.addBias, List.length_zipWith]
    rw [hmatlen]
  · intro i hireal hiinterval
    have hi : i < matInterval.length := by
      simp only [forwardInterval, LeanCert.Engine.IntervalVector.addBias,
        List.length_zipWith] at hiinterval
      omega
    simpa [forwardReal, forwardInterval, matReal, matInterval] using hadd i hi

end AffineLayer

/-- A depth-2 MLP cell: `Linear -> exact erf-GELU -> Linear`. -/
structure ErfGELUFFN where
  linear1 : AffineLayer
  linear2 : AffineLayer
  dims_match : True := by trivial
  deriving Repr

namespace ErfGELUFFN

/-- Real forward pass for the exact erf-GELU cell. -/
noncomputable def forwardReal (net : ErfGELUFFN) (x : List ℝ) : List ℝ :=
  let hidden := net.linear1.forwardReal x
  let activated := hidden.map Real.erfGELU
  net.linear2.forwardReal activated

/-- Interval forward pass for the exact erf-GELU cell. -/
def forwardInterval (net : ErfGELUFFN) (x : IntervalVector)
    (prec : Int := -53) (taylorDepth : Nat := 15) : IntervalVector :=
  let hidden := net.linear1.forwardInterval x prec
  let activated := erfGELUVector hidden prec taylorDepth
  net.linear2.forwardInterval activated prec

/-- Network-level soundness of `Linear → erf-GELU → Linear`.

The dimension assumptions are explicit because the executable structures retain
dimension-mismatch fallbacks for compatibility. -/
theorem forwardInterval_correct (net : ErfGELUFFN) {xs : List ℝ} {Is : IntervalVector}
    (hxmem : List.Forall₂ (fun x I => x ∈ I) xs Is)
    (hrows1 : ∀ row ∈ net.linear1.weights, row.length = Is.length)
    (hbias1 : net.linear1.bias.length = net.linear1.weights.length)
    (hrows2 : ∀ row ∈ net.linear2.weights,
      row.length = net.linear1.weights.length)
    (hbias2 : net.linear2.bias.length = net.linear2.weights.length)
    (prec : Int := -53) (taylorDepth : Nat := 15)
    (hprec : prec ≤ 0 := by norm_num) :
    List.Forall₂ (fun y J => y ∈ J)
      (net.forwardReal xs) (net.forwardInterval Is prec taylorDepth) := by
  let hiddenReal := net.linear1.forwardReal xs
  let hiddenInterval := net.linear1.forwardInterval Is prec
  have hhidden := net.linear1.forwardInterval_correct hrows1 hxmem hbias1 prec hprec
  have hhiddenLen : hiddenReal.length = hiddenInterval.length := hhidden.length_eq
  let activatedReal := hiddenReal.map Real.erfGELU
  let activatedInterval := erfGELUVector hiddenInterval prec taylorDepth
  have hactivatedMem : List.Forall₂ (fun y J => y ∈ J)
      activatedReal activatedInterval := by
    rw [List.forall₂_iff_get]
    constructor
    · simp [activatedReal, activatedInterval, erfGELUVector, hhiddenLen]
    · intro i hireal hiinterval
      simp only [activatedReal, activatedInterval, erfGELUVector, List.get_eq_getElem,
        List.getElem_map]
      exact mem_erfGELUInterval (hhidden.get (by simpa [activatedReal] using hireal)
        (by simpa [activatedInterval, erfGELUVector] using hiinterval))
        prec taylorDepth hprec
  have hhiddenIntervalLen : hiddenInterval.length = net.linear1.weights.length := by
    simp [hiddenInterval, AffineLayer.forwardInterval,
      LeanCert.Engine.IntervalVector.addBias, LeanCert.Engine.IntervalVector.matVecMul, hbias1]
  have hactivatedIntervalLen : activatedInterval.length = net.linear1.weights.length := by
    simpa [activatedInterval, erfGELUVector] using hhiddenIntervalLen
  have hrows2' : ∀ row ∈ net.linear2.weights, row.length = activatedInterval.length := by
    intro row hrow
    rw [hactivatedIntervalLen]
    exact hrows2 row hrow
  exact net.linear2.forwardInterval_correct hrows2' hactivatedMem
    hbias2 prec hprec

end ErfGELUFFN

end LeanCert.ML
