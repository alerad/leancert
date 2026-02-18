import LeanCert.Engine.ChebyshevTheta

open LeanCert.Engine.ChebyshevTheta

-- Quick test: theta(N) <= 1.11 * N for all N = 1..599
-- (analogous to the psi test in ChebyshevPsiTest)
example : checkAllThetaLeMulWith 599 (111 / 100) 20 = true := by native_decide

-- PNT+ issue #990: Eθ(x) = |θ(x) - x| / x ≤ 1 - log(3)/3 for 2 < x ≤ 599.
-- 1 - log(3)/3 ≈ 0.6338...; we over-approximate with 634/1000.
-- The proof in PNT+ will verify 634/1000 ≥ 1 - log(3)/3 via interval arithmetic.
-- Range starts at N = 3 since the bound is for x > 2 (i.e. ⌊x⌋ ≥ 3).
example : checkAllThetaRelError 3 599 (634 / 1000) 20 = true := by native_decide

-- Eval versions for quick testing
#eval checkAllThetaLeMulWith 599 (111 / 100) 20
#eval checkAllThetaRelError 3 599 (634 / 1000) 20
