/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/

import LeanCert.ANT.Asymp.Pointwise

/-!
# Explicit-PNT compiler theorem schemas

This module contains project-agnostic theorem schemas for the two standard
explicit-PNT envelope transfers:

* `psi -> theta`, after bounding prime-power contributions;
* `theta -> pi`, after a partial-summation decomposition has been proved.

The actual functions `ψ`, `θ`, `π`, and `Li` are intentionally parameters.
LeanCert supplies the reusable inequality algebra; project files supply the
semantic definitions and decomposition identities.
-/

namespace LeanCert.ANT.PNTCompilers

/--
Generic `ψ -> θ` envelope transfer.

If `theta x - x = (psi x - x) - powerContribution`, the psi error is bounded by
`psiError`, and the prime-power contribution is between `0` and `powerBound`,
then the theta error is bounded by `psiError + powerBound`.
-/
theorem psi_to_theta_bound
    {psi theta : ℝ → ℝ} {x psiError powerContribution powerBound : ℝ}
    (hdecomp : theta x - x = (psi x - x) - powerContribution)
    (hpsi : |psi x - x| ≤ psiError)
    (hpower_nonneg : 0 ≤ powerContribution)
    (hpower_bound : powerContribution ≤ powerBound) :
    |theta x - x| ≤ psiError + powerBound := by
  rw [hdecomp]
  have htri : |(psi x - x) - powerContribution| ≤
      |psi x - x| + |powerContribution| := by
    have hrewrite :
        |(psi x - x) - powerContribution| =
          |(psi x - x) + (-powerContribution)| := by ring_nf
    rw [hrewrite]
    simpa [abs_neg] using abs_add_le (psi x - x) (-powerContribution)
  have hpow_abs : |powerContribution| = powerContribution := abs_of_nonneg hpower_nonneg
  linarith

/--
Generic `θ -> π` envelope transfer after partial summation.

The decomposition field should package the project-specific partial-summation
identity.  The endpoint and integral terms are supplied as already-bounded
absolute values, which keeps this theorem independent of the concrete choice of
`Li`, endpoint constants, and integral certificate backend.
-/
theorem theta_to_pi_bound_of_decomposition
    {primeCount li : ℝ → ℝ} {x : ℝ}
    {constant endpointX endpointBase integralTerm
      endpointXBound endpointBaseBound integralBound : ℝ}
    (hdecomp :
      primeCount x - li x =
        constant + endpointX - endpointBase + integralTerm)
    (hEndpointX : |endpointX| ≤ endpointXBound)
    (hEndpointBase : |endpointBase| ≤ endpointBaseBound)
    (hIntegral : |integralTerm| ≤ integralBound) :
    |primeCount x - li x| ≤
      |constant| + endpointXBound + endpointBaseBound + integralBound := by
  rw [hdecomp]
  have hmain :
      |constant + endpointX - endpointBase + integralTerm| ≤
        |constant| + |endpointX| + |endpointBase| + |integralTerm| := by
    have hrewrite :
        |constant + endpointX - endpointBase + integralTerm| =
          |constant + (endpointX + (-endpointBase) + integralTerm)| := by ring_nf
    rw [hrewrite]
    have h1 :
        |constant + (endpointX + (-endpointBase) + integralTerm)| ≤
          |constant| + |endpointX + (-endpointBase) + integralTerm| :=
      abs_add_le _ _
    have h2 :
        |endpointX + (-endpointBase) + integralTerm| ≤
          |endpointX + (-endpointBase)| + |integralTerm| :=
      abs_add_le _ _
    have h3 :
        |endpointX + (-endpointBase)| ≤ |endpointX| + |-endpointBase| :=
      abs_add_le _ _
    have hneg : |-endpointBase| = |endpointBase| := abs_neg _
    linarith
  linarith

/--
Endpoint form of the `θ -> π` transfer where the endpoint terms are explicitly
`deltaTheta / log`.

This theorem only needs positivity of the logarithms to turn bounds on
`deltaTheta` into bounds on the divided endpoint terms.
-/
theorem theta_to_pi_bound
    {primeCount li deltaTheta thetaError : ℝ → ℝ} {x x0 : ℝ}
    {constant integralTerm integralBound : ℝ}
    (hdecomp :
      primeCount x - li x =
        constant +
          deltaTheta x / Real.log x -
            deltaTheta x0 / Real.log x0 +
              integralTerm)
    (hThetaX : |deltaTheta x| ≤ thetaError x)
    (hThetaX0 : |deltaTheta x0| ≤ thetaError x0)
    (hLogX : 0 < Real.log x)
    (hLogX0 : 0 < Real.log x0)
    (hIntegral : |integralTerm| ≤ integralBound) :
    |primeCount x - li x| ≤
      |constant| +
        thetaError x / Real.log x +
          thetaError x0 / Real.log x0 +
            integralBound := by
  apply theta_to_pi_bound_of_decomposition (hdecomp := hdecomp)
  · rw [abs_div, abs_of_pos hLogX]
    exact div_le_div_of_nonneg_right hThetaX (le_of_lt hLogX)
  · rw [abs_div, abs_of_pos hLogX0]
    exact div_le_div_of_nonneg_right hThetaX0 (le_of_lt hLogX0)
  · exact hIntegral

end LeanCert.ANT.PNTCompilers
