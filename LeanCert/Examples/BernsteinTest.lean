/-
Copyright (c) 2024 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Engine.TaylorModel.Core

/-!
# Bernstein Bounds Test

Quick test to verify Bernstein polynomial conversion is working.
-/

namespace LeanCert.Examples.BernsteinTest

open LeanCert.Engine
open LeanCert.Core

-- Domain [0, 1]
def testDomain : IntervalRat := ⟨0, 1, by norm_num⟩

-- Test: directly test the transformation functions
-- For P(x) = x - x² = 0 + 1*x + (-1)*x² on [0,1] centered at 0
-- Transformed to t ∈ [0,1]: u = 0 + t*1 = t, so Q(t) = t - t²
-- Monomial coeffs of Q: [0, 1, -1]
-- Bernstein coeffs: b₀ = 0, b₁ = 1/2, b₂ = 0 (should give range [0, 0.5])

-- Test monomialToBernstein directly with coefficient lists
#eval
  let monomialCoeffs : List ℚ := [0, 1, -1]  -- represents t - t²
  let bernstein := monomialToBernstein monomialCoeffs
  s!"Bernstein coeffs for t - t² on [0,1]: {bernstein}\n" ++
  s!"Expected: [0, 0.5, 0] (i.e., [0, 1/2, 0])"

#eval
  let monomialCoeffs : List ℚ := [0, 0, 1]  -- represents t²
  let bernstein := monomialToBernstein monomialCoeffs
  s!"Bernstein coeffs for t² on [0,1]: {bernstein}\n" ++
  s!"Expected: [0, 0, 1]"

#eval
  let monomialCoeffs : List ℚ := [1, -1]  -- represents 1 - t
  let bernstein := monomialToBernstein monomialCoeffs
  s!"Bernstein coeffs for 1-t on [0,1]: {bernstein}\n" ++
  s!"Expected: [1, 0]"

-- Test min/max
#eval
  let coeffs : List ℚ := [0, 1/2, 0]
  let bounds := listMinMax coeffs 0
  s!"Min/max of [0, 1/2, 0]: ({bounds.1}, {bounds.2})"

end LeanCert.Examples.BernsteinTest
