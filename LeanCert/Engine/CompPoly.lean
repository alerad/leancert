/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Core.IntervalDyadic
import LeanCert.Core.IntervalRat.Basic
import LeanCert.Core.IntervalRat.Taylor
import LeanCert.Engine.Integrate
import LeanCert.Engine.IntervalEvalDyadic

/-!
# Dyadic Polynomial Taylor Models

Computable polynomial Taylor models using `Dyadic` coefficients and `IntervalDyadic`
for all intermediate computations. This avoids the rational coefficient explosion that
occurs with `ℚ` polynomials, since all Dyadic operations use `roundOut` to control
precision.

## Main definitions

* `DyPoly` — polynomial with `Dyadic` coefficients
* `DyTM` — Taylor model: `DyPoly` + `IntervalDyadic` remainder
-/

namespace LeanCert.Engine

open LeanCert.Core (IntervalDyadic IntervalRat Expr)

/-- Alias for `LeanCert.Core.Dyadic` to avoid clash with Mathlib's `_root_.Dyadic`. -/
abbrev Dy := LeanCert.Core.Dyadic

/-! ### DyPoly: Dyadic polynomial -/

/-- A polynomial with Dyadic coefficients.
    p(u) = coeffs[0] + coeffs[1]*u + coeffs[2]*u² + ... -/
structure DyPoly where
  coeffs : Array Dy
  deriving Inhabited

namespace DyPoly

def zero : DyPoly := ⟨#[]⟩

def const (c : Dy) : DyPoly := ⟨#[c]⟩

/-- Coefficient i (0 if out of range). -/
def coeff (p : DyPoly) (i : ℕ) : Dy :=
  if h : i < p.coeffs.size then p.coeffs[i] else LeanCert.Core.Dyadic.zero

/-- Evaluate on a Dyadic interval (Horner's method with rounding). -/
def evalInterval (p : DyPoly) (I : IntervalDyadic) (prec : Int) : IntervalDyadic :=
  p.coeffs.foldr
    (fun c acc =>
      IntervalDyadic.addRounded (IntervalDyadic.singleton c) (IntervalDyadic.mulRounded I acc prec) prec)
    (IntervalDyadic.singleton LeanCert.Core.Dyadic.zero)

/-- Add two polynomials. -/
def add (p q : DyPoly) : DyPoly :=
  let n := max p.coeffs.size q.coeffs.size
  ⟨Array.ofFn (fun i : Fin n => LeanCert.Core.Dyadic.add (p.coeff i.val) (q.coeff i.val))⟩

def neg (p : DyPoly) : DyPoly :=
  ⟨p.coeffs.map LeanCert.Core.Dyadic.neg⟩

/-- Scale by a Dyadic constant. -/
def scale (p : DyPoly) (c : Dy) : DyPoly :=
  ⟨p.coeffs.map (LeanCert.Core.Dyadic.mul c ·)⟩

/-- Normalize all coefficients to bounded precision. -/
def normalize (p : DyPoly) (maxBits : Nat := 256) : DyPoly :=
  ⟨p.coeffs.map (LeanCert.Core.Dyadic.normalize · maxBits)⟩

/-- Multiply two polynomials with truncation to maxDeg.
    Each coefficient is normalized to prevent growth. -/
def mulTrunc (p q : DyPoly) (maxDeg : ℕ) (maxBits : Nat := 256) : DyPoly :=
  if p.coeffs.size == 0 || q.coeffs.size == 0 then zero
  else
    let n := min (p.coeffs.size + q.coeffs.size - 1) (maxDeg + 1)
    ⟨Array.ofFn (fun k : Fin n =>
      let k' := k.val
      let raw := (List.range (k' + 1)).foldl (fun acc j =>
        if j < p.coeffs.size && k' - j < q.coeffs.size then
          LeanCert.Core.Dyadic.add acc (LeanCert.Core.Dyadic.mul (p.coeff j) (q.coeff (k' - j)))
        else acc) LeanCert.Core.Dyadic.zero
      LeanCert.Core.Dyadic.normalize raw maxBits)⟩

/-- Full multiply (no truncation). -/
def mul (p q : DyPoly) (maxBits : Nat := 256) : DyPoly :=
  if p.coeffs.size == 0 || q.coeffs.size == 0 then zero
  else
    let n := p.coeffs.size + q.coeffs.size - 1
    ⟨Array.ofFn (fun k : Fin n =>
      let k' := k.val
      let raw := (List.range (k' + 1)).foldl (fun acc j =>
        if j < p.coeffs.size && k' - j < q.coeffs.size then
          LeanCert.Core.Dyadic.add acc (LeanCert.Core.Dyadic.mul (p.coeff j) (q.coeff (k' - j)))
        else acc) LeanCert.Core.Dyadic.zero
      LeanCert.Core.Dyadic.normalize raw maxBits)⟩

/-- Tail: coefficients with degree > maxDeg. -/
def tail (p : DyPoly) (maxDeg : ℕ) : DyPoly :=
  if maxDeg + 1 ≥ p.coeffs.size then zero
  else
    let padding := Array.ofFn (fun _ : Fin (maxDeg + 1) => LeanCert.Core.Dyadic.zero)
    ⟨padding ++ p.coeffs.extract (maxDeg + 1) p.coeffs.size⟩

/-- Scale coefficient i by 1/(i+1) for antiderivative.
    Uses directed rounding: lo rounds down, hi rounds up. -/
def antiderivativeCoeffDown (c : Dy) (i : ℕ) (prec : Int) : Dy :=
  -- c / (i+1), rounding down
  let num := c
  let denom := LeanCert.Core.Dyadic.ofInt (i + 1 : Int)
  -- Compute as Dyadic: c * (1/(i+1)) ≈ c.mantissa * 2^c.exponent / (i+1)
  -- Rounding down: use shiftDown on the result
  let result := LeanCert.Core.Dyadic.mul num (LeanCert.Core.Dyadic.ofInt 1)  -- just c
  -- Actually divide mantissa by (i+1)
  let newMantissa := result.mantissa / (i + 1 : Int)
  LeanCert.Core.Dyadic.shiftDown ⟨newMantissa, result.exponent⟩ prec

def antiderivativeCoeffUp (c : Dy) (i : ℕ) (prec : Int) : Dy :=
  let newMantissa := -((-c.mantissa) / (i + 1 : Int))
  LeanCert.Core.Dyadic.shiftUp ⟨newMantissa, c.exponent⟩ prec

/-- Compute definite integral ∫_a^b p(u) du as IntervalDyadic.
    Uses Horner evaluation of the antiderivative at endpoints. -/
def definiteIntegral (p : DyPoly) (a b : IntervalDyadic) (prec : Int) : IntervalDyadic :=
  let n := p.coeffs.size
  if n == 0 then IntervalDyadic.singleton LeanCert.Core.Dyadic.zero
  else
    let evalInner (x : IntervalDyadic) : IntervalDyadic :=
      let init := IntervalDyadic.singleton LeanCert.Core.Dyadic.zero
      (List.range n).foldr (fun i acc =>
        let cDown := antiderivativeCoeffDown (p.coeff i) i prec
        let cUp := antiderivativeCoeffUp (p.coeff i) i prec
        let cI : IntervalDyadic := ⟨LeanCert.Core.Dyadic.min cDown cUp, LeanCert.Core.Dyadic.max cDown cUp,
          le_trans (LeanCert.Core.Dyadic.min_toRat_le_left cDown cUp)
            (LeanCert.Core.Dyadic.le_max_toRat_left cDown cUp)⟩
        IntervalDyadic.addRounded cI (IntervalDyadic.mulRounded x acc prec) prec
      ) init

    let innerB := evalInner b
    let innerA := evalInner a
    let antiB := IntervalDyadic.mulRounded b innerB prec
    let antiA := IntervalDyadic.mulRounded a innerA prec
    IntervalDyadic.addRounded antiB (IntervalDyadic.neg antiA) prec

end DyPoly

/-! ### DyTM: Dyadic Taylor Model -/

/-- Dyadic Taylor model: f(x) ∈ P(x - center) + remainder for x ∈ domain. -/
structure DyTM where
  poly : DyPoly
  remainder : IntervalDyadic
  center : Dy
  domain : IntervalDyadic
  prec : Int  -- precision for roundOut
  deriving Inhabited

namespace DyTM

private def shiftedDomain (tm : DyTM) : IntervalDyadic :=
  IntervalDyadic.addRounded tm.domain (IntervalDyadic.neg (IntervalDyadic.singleton tm.center)) tm.prec

def bound (tm : DyTM) : IntervalDyadic :=
  IntervalDyadic.addRounded (tm.poly.evalInterval tm.shiftedDomain tm.prec) tm.remainder tm.prec

def const (c : Dy) (domain : IntervalDyadic) (prec : Int) : DyTM :=
  { poly := DyPoly.const c
    remainder := IntervalDyadic.singleton LeanCert.Core.Dyadic.zero
    center := domain.midpoint
    domain := domain
    prec := prec }

def identity (domain : IntervalDyadic) (prec : Int) : DyTM :=
  let mid := domain.midpoint
  { poly := ⟨#[mid, LeanCert.Core.Dyadic.one]⟩
    remainder := IntervalDyadic.singleton LeanCert.Core.Dyadic.zero
    center := mid
    domain := domain
    prec := prec }

def add (tm1 tm2 : DyTM) : DyTM :=
  { poly := tm1.poly.add tm2.poly
    remainder := IntervalDyadic.addRounded tm1.remainder tm2.remainder tm1.prec
    center := tm1.center
    domain := tm1.domain
    prec := tm1.prec }

def neg (tm : DyTM) : DyTM :=
  { poly := tm.poly.neg
    remainder := IntervalDyadic.neg tm.remainder
    center := tm.center
    domain := tm.domain
    prec := tm.prec }

def scaleDyadic (tm : DyTM) (c : Dy) : DyTM :=
  { poly := tm.poly.scale c
    remainder := IntervalDyadic.mulRounded (IntervalDyadic.singleton c) tm.remainder tm.prec
    center := tm.center
    domain := tm.domain
    prec := tm.prec }

/-- Multiply two DyTMs with truncation. -/
def mul (tm1 tm2 : DyTM) (maxDeg : ℕ) (maxBits : Nat := 256) : DyTM :=
  let prodPoly := tm1.poly.mulTrunc tm2.poly maxDeg maxBits
  let fullProd := tm1.poly.mul tm2.poly maxBits
  let sd := tm1.shiftedDomain
  let p := tm1.prec
  let tailBound := fullProd.tail maxDeg |>.evalInterval sd p
  let p1Bound := tm1.poly.evalInterval sd p
  let p2Bound := tm2.poly.evalInterval sd p
  let p1r2 := IntervalDyadic.mulRounded p1Bound tm2.remainder p
  let p2r1 := IntervalDyadic.mulRounded p2Bound tm1.remainder p
  let r1r2 := IntervalDyadic.mulRounded tm1.remainder tm2.remainder p
  let totalRem := IntervalDyadic.addRounded tailBound
    (IntervalDyadic.addRounded p1r2 (IntervalDyadic.addRounded p2r1 r1r2 p) p) p
  { poly := prodPoly
    remainder := totalRem
    center := tm1.center
    domain := tm1.domain
    prec := tm1.prec }

/-- Inverse using geometric series: 1/f = (1/a₀) Σ (-S)ᵏ
    where S = (f-a₀)/a₀. Uses dyadic arithmetic throughout. -/
def inv (tm : DyTM) (maxDeg nTerms : ℕ) (cfg : DyadicConfig) (maxBits : Nat := 256) : Option DyTM := do
  let a0 := tm.poly.coeff 0
  let p := tm.prec
  -- Check a0 + remainder doesn't contain zero
  let a0I := IntervalDyadic.addRounded (IntervalDyadic.singleton a0) tm.remainder p
  guard (a0I.hi.toRat < 0 || a0I.lo.toRat > 0)
  -- Build pPrime (polynomial without constant term, shifted)
  let pPrime : DyPoly := ⟨if tm.poly.coeffs.size > 0
    then #[LeanCert.Core.Dyadic.zero] ++ tm.poly.coeffs.extract 1 tm.poly.coeffs.size
    else #[]⟩
  let sd := tm.shiftedDomain
  let pPrimeBound := pPrime.evalInterval sd p
  -- Compute 1/a₀ as interval
  let invA0I := invIntervalDyadic (IntervalDyadic.singleton a0) cfg
  -- S = pPrime/a₀ + remainder/a₀
  let sBound := IntervalDyadic.addRounded
    (IntervalDyadic.mulRounded pPrimeBound invA0I p)
    (IntervalDyadic.mulRounded tm.remainder invA0I p) p
  let sMaxLo := (LeanCert.Core.Dyadic.abs sBound.lo).toRat
  let sMaxHi := (LeanCert.Core.Dyadic.abs sBound.hi).toRat
  let sMax := max sMaxLo sMaxHi
  guard (sMax < 1)
  -- Build S as TM: poly = pPrime * (1/a₀), remainder = tm.remainder * (1/a₀)
  let invA0Mid := invA0I.midpoint
  let sTM : DyTM :=
    { poly := pPrime.scale invA0Mid |>.normalize maxBits
      remainder := IntervalDyadic.mulRounded tm.remainder invA0I p
      center := tm.center, domain := tm.domain, prec := p }
  let negS := sTM.neg
  -- Sum geometric series: Σ (-S)^k for k = 0..nTerms
  let init : DyTM := { poly := DyPoly.const LeanCert.Core.Dyadic.one,
                        remainder := IntervalDyadic.singleton LeanCert.Core.Dyadic.zero,
                        center := tm.center, domain := tm.domain, prec := p }
  let (acc, _) := (List.range nTerms).foldl (fun (acc, curPow) _ =>
    let newPow := DyTM.mul curPow negS maxDeg maxBits
    (DyTM.add acc newPow, newPow)) (init, init)
  -- Geometric series remainder: |s|^(n+1) / (1 - |s|)
  let geomRem := sMax ^ (nTerms + 1) / (1 - sMax)
  let geomRemDyad := IntervalDyadic.ofIntervalRat ⟨-|geomRem|, |geomRem|,
    neg_le_self (abs_nonneg geomRem)⟩ p
  -- Result = (1/a₀) * (acc + geomRem)
  pure { poly := acc.poly.scale invA0Mid |>.normalize maxBits
         remainder := IntervalDyadic.mulRounded invA0I
           (IntervalDyadic.addRounded acc.remainder geomRemDyad p) p
         center := tm.center, domain := tm.domain, prec := p }

/-- Log using series: log(f) = log(a₀) + Σ (-1)^{k+1} Sᵏ/k -/
def log (tm : DyTM) (maxDeg nTerms : ℕ) (cfg : DyadicConfig) (maxBits : Nat := 256) : Option DyTM := do
  let a0 := tm.poly.coeff 0
  let p := tm.prec
  -- Check entire function range is positive
  let fBound := tm.bound
  guard (fBound.lo.toRat > 0)
  -- Compute log(a₀) using existing infrastructure
  let a0Rat := a0.toRat
  let a0IRat : IntervalRat := ⟨a0Rat, a0Rat, le_refl a0Rat⟩
  let logA0Rat := IntervalRat.logComputable a0IRat cfg.taylorDepth
  let logA0 := IntervalDyadic.ofIntervalRat logA0Rat p
  -- Build S = (f - a₀)/a₀
  let pPrime : DyPoly := ⟨if tm.poly.coeffs.size > 0
    then #[LeanCert.Core.Dyadic.zero] ++ tm.poly.coeffs.extract 1 tm.poly.coeffs.size
    else #[]⟩
  let sd := tm.shiftedDomain
  let invA0I := invIntervalDyadic (IntervalDyadic.singleton a0) cfg
  let pPrimeBound := pPrime.evalInterval sd p
  let sBound := IntervalDyadic.addRounded
    (IntervalDyadic.mulRounded pPrimeBound invA0I p)
    (IntervalDyadic.mulRounded tm.remainder invA0I p) p
  let sMaxLo := (LeanCert.Core.Dyadic.abs sBound.lo).toRat
  let sMaxHi := (LeanCert.Core.Dyadic.abs sBound.hi).toRat
  let sMax := max sMaxLo sMaxHi
  guard (sMax < 1)
  let invA0Mid := invA0I.midpoint
  let sTM : DyTM :=
    { poly := pPrime.scale invA0Mid |>.normalize maxBits
      remainder := IntervalDyadic.mulRounded tm.remainder invA0I p
      center := tm.center, domain := tm.domain, prec := p }
  -- Initialize with log(a₀)
  let logA0Mid := logA0.midpoint
  let logA0Err := IntervalDyadic.addRounded logA0 (IntervalDyadic.neg (IntervalDyadic.singleton logA0Mid)) p
  let init : DyTM := { poly := DyPoly.const logA0Mid,
                        remainder := logA0Err,
                        center := tm.center, domain := tm.domain, prec := p }
  let unitTM : DyTM := { poly := DyPoly.const LeanCert.Core.Dyadic.one,
                          remainder := IntervalDyadic.singleton LeanCert.Core.Dyadic.zero,
                          center := tm.center, domain := tm.domain, prec := p }
  -- Sum: log(a₀) + Σ_{k=1}^{nTerms} (-1)^{k+1}/k * S^k
  let (acc, _) := (List.range nTerms).foldl (fun (acc, sPow) k =>
    let newPow := DyTM.mul sPow sTM maxDeg maxBits
    let sign := if k % 2 == 0 then LeanCert.Core.Dyadic.one else LeanCert.Core.Dyadic.neg LeanCert.Core.Dyadic.one
    -- Scale by sign/(k+1): approximate as Dyadic
    let kp1 := (k + 1 : Int)
    let scaleFactor := LeanCert.Core.Dyadic.normalize ⟨sign.mantissa, sign.exponent⟩ maxBits  -- ±1
    -- Division by (k+1): scale mantissa of each coeff
    let termPoly : DyPoly := ⟨newPow.poly.coeffs.map (fun c =>
      LeanCert.Core.Dyadic.normalize ⟨c.mantissa * scaleFactor.mantissa / kp1, c.exponent + scaleFactor.exponent⟩ maxBits)⟩
    let kp1Dyad := IntervalDyadic.singleton (LeanCert.Core.Dyadic.ofInt kp1)
    let scaleI := IntervalDyadic.mulRounded (IntervalDyadic.singleton scaleFactor) (invIntervalDyadic kp1Dyad cfg) p
    let termRem := IntervalDyadic.mulRounded newPow.remainder scaleI p
    let term : DyTM := { poly := termPoly, remainder := termRem,
                          center := tm.center, domain := tm.domain, prec := p }
    (DyTM.add acc term, newPow)) (init, unitTM)
  -- Log series remainder: |s|^(n+1) / ((n+1) * (1 - |s|))
  let logRem := sMax ^ (nTerms + 1) / ((nTerms + 1 : ℚ) * (1 - sMax))
  let logRemDyad := IntervalDyadic.ofIntervalRat ⟨-|logRem|, |logRem|,
    neg_le_self (abs_nonneg logRem)⟩ p
  pure { poly := acc.poly.normalize maxBits
         remainder := IntervalDyadic.addRounded acc.remainder logRemDyad p
         center := tm.center, domain := tm.domain, prec := p }

def fromInterval (I : IntervalDyadic) (domain : IntervalDyadic) (prec : Int) : DyTM :=
  { poly := DyPoly.zero, remainder := I,
    center := domain.midpoint, domain := domain, prec := prec }

end DyTM

/-! ### Expression to DyTM -/

def dyTMFromExpr (e : Expr) (domain : IntervalDyadic)
    (maxDeg : ℕ := 8) (nTerms : ℕ := 8) (cfg : DyadicConfig := {}) (maxBits : Nat := 256) : Option DyTM :=
  let p := cfg.precision
  match e with
  | .const q =>
    let cDyad := (IntervalDyadic.ofIntervalRat ⟨q, q, le_refl q⟩ p).midpoint
    some (DyTM.const cDyad domain p)
  | .var _ => some (DyTM.identity domain p)
  | .add e₁ e₂ => do
    let tm1 ← dyTMFromExpr e₁ domain maxDeg nTerms cfg maxBits
    let tm2 ← dyTMFromExpr e₂ domain maxDeg nTerms cfg maxBits
    pure (DyTM.add tm1 tm2)
  | .mul e₁ e₂ => do
    let tm1 ← dyTMFromExpr e₁ domain maxDeg nTerms cfg maxBits
    let tm2 ← dyTMFromExpr e₂ domain maxDeg nTerms cfg maxBits
    pure (DyTM.mul tm1 tm2 maxDeg maxBits)
  | .neg e => do
    let tm ← dyTMFromExpr e domain maxDeg nTerms cfg maxBits
    pure (DyTM.neg tm)
  | .inv e => do
    let tm ← dyTMFromExpr e domain maxDeg nTerms cfg maxBits
    DyTM.inv tm maxDeg nTerms cfg maxBits
  | .log e => do
    let tm ← dyTMFromExpr e domain maxDeg nTerms cfg maxBits
    DyTM.log tm maxDeg nTerms cfg maxBits
  | .exp e => do
    let tm ← dyTMFromExpr e domain maxDeg nTerms cfg maxBits
    let expBound := evalIntervalDyadic (.exp e) (fun _ => domain) cfg
    pure (DyTM.fromInterval expBound domain cfg.precision)
  | .sin e => do
    let tm ← dyTMFromExpr e domain maxDeg nTerms cfg maxBits
    let sinBound := evalIntervalDyadic (.sin e) (fun _ => domain) cfg
    pure (DyTM.fromInterval sinBound domain cfg.precision)
  | .cos e => do
    let tm ← dyTMFromExpr e domain maxDeg nTerms cfg maxBits
    let cosBound := evalIntervalDyadic (.cos e) (fun _ => domain) cfg
    pure (DyTM.fromInterval cosBound domain cfg.precision)
  | _ => none

/-! ### DyTM Integration -/

/-- Integrate a DyTM over its domain, returning result as IntervalRat. -/
def integrateDyTM (tm : DyTM) : IntervalRat :=
  let p := tm.prec
  let sd := tm.shiftedDomain
  -- Polynomial integral: ∫_a^b P(u) du where [a,b] = shifted domain
  let polyIntegral := tm.poly.definiteIntegral
    (IntervalDyadic.singleton sd.lo) (IntervalDyadic.singleton sd.hi) p
  -- Remainder integral: width * remainder
  let width := IntervalDyadic.addRounded (IntervalDyadic.singleton tm.domain.hi)
    (IntervalDyadic.neg (IntervalDyadic.singleton tm.domain.lo)) p
  let remIntegral := IntervalDyadic.mulRounded width tm.remainder p
  let total := IntervalDyadic.addRounded polyIntegral remIntegral p
  total.toIntervalRat

/-- Fallback: integrate via dyadic interval evaluation. -/
def integrateDyadicFallback (e : Expr) (partRat : IntervalRat)
    (cfg : DyadicConfig) : IntervalRat :=
  let partDyad := IntervalDyadic.ofIntervalRat partRat cfg.precision
  let fBound := evalIntervalDyadic e (fun _ => partDyad) cfg
  let widthDyad := IntervalDyadic.addRounded (IntervalDyadic.singleton partDyad.hi)
    (IntervalDyadic.neg (IntervalDyadic.singleton partDyad.lo)) cfg.precision
  (IntervalDyadic.mulRounded widthDyad fBound cfg.precision).toIntervalRat

def integrateDyPolyAux (e : Expr) (parts : List IntervalRat)
    (maxDeg nTerms : ℕ) (cfg : DyadicConfig) (maxBits : Nat := 256) : IntervalRat :=
  parts.foldl (fun acc part =>
    let partDyad := IntervalDyadic.ofIntervalRat part cfg.precision
    let partIntegral := match dyTMFromExpr e partDyad maxDeg nTerms cfg maxBits with
      | some tm => integrateDyTM tm
      | none => integrateDyadicFallback e part cfg
    IntervalRat.add acc partIntegral) (IntervalRat.singleton 0)

def integrateDyPoly (e : Expr) (I : IntervalRat) (n : ℕ) (hn : 0 < n)
    (maxDeg : ℕ := 8) (nTerms : ℕ := 8) (cfg : DyadicConfig := {}) (maxBits : Nat := 256) : IntervalRat :=
  let parts := uniformPartition I n hn
  integrateDyPolyAux e parts maxDeg nTerms cfg maxBits

def checkIntegralLowerBoundDyPoly (e : Expr) (I : IntervalRat) (n : ℕ)
    (c : ℚ) (maxDeg : ℕ := 8) (nTerms : ℕ := 8) (cfg : DyadicConfig := {}) (maxBits : Nat := 256) : Bool :=
  if hn : 0 < n then
    decide (c ≤ (integrateDyPoly e I n hn maxDeg nTerms cfg maxBits).lo)
  else false

def checkIntegralUpperBoundDyPoly (e : Expr) (I : IntervalRat) (n : ℕ)
    (c : ℚ) (maxDeg : ℕ := 8) (nTerms : ℕ := 8) (cfg : DyadicConfig := {}) (maxBits : Nat := 256) : Bool :=
  if hn : 0 < n then
    decide ((integrateDyPoly e I n hn maxDeg nTerms cfg maxBits).hi ≤ c)
  else false

end LeanCert.Engine
