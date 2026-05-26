# Chebyshev Certificates

LeanCert includes specialized certificate engines for finite Chebyshev function
bounds. These engines use computable rational upper/lower envelopes for
logarithmic summands, then expose Golden Theorems that turn successful boolean
checks into real-number bounds.

## Imports

```lean
import LeanCert.Engine.ChebyshevPsi
import LeanCert.Engine.ChebyshevTheta
```

or use the aggregate import:

```lean
import LeanCert
```

## Psi Bounds

`LeanCert.Engine.ChebyshevPsi` certifies upper bounds for the second Chebyshev
function `ψ`.

Core checkers:

```lean
checkPsiLeMulWith (N : Nat) (slope : ℚ) (depth : Nat)
checkAllPsiLeMulWith (bound : Nat) (slope : ℚ) (depth : Nat)
```

Golden Theorems:

```lean
theorem verify_psi_le_mul (N depth : Nat) (slope : ℚ)
    (hcheck : checkPsiLeMulWith N slope depth = true) :
    Chebyshev.psi (N : ℝ) ≤ (slope : ℝ) * N

theorem verify_all_psi_le_mul
    (bound depth : Nat) (slope : ℚ)
    (hcheck : checkAllPsiLeMulWith bound slope depth = true) :
    ∀ N : Nat, 0 < N → N ≤ bound →
      Chebyshev.psi (N : ℝ) ≤ (slope : ℝ) * N
```

Real-variable form:

```lean
theorem verify_all_psi_le_mul_real
    (bound depth : Nat) (slope : ℚ)
    (hslope : 0 ≤ slope)
    (hcheck : checkAllPsiLeMulWith bound slope depth = true) :
    ∀ x : ℝ, 0 < x → x ≤ (bound : ℝ) →
      Chebyshev.psi x ≤ (slope : ℝ) * x
```

## Theta Bounds

`LeanCert.Engine.ChebyshevTheta` certifies upper, absolute-error, and
relative-error bounds for the first Chebyshev function `θ`.

Core checkers:

```lean
checkThetaLeMulWith
checkAllThetaLeMulWith
checkThetaAbsError
checkAllThetaAbsError
checkThetaRelError
checkAllThetaRelError
checkThetaRelErrorReal
checkAllThetaRelErrorReal
```

Golden Theorems:

```lean
theorem verify_theta_le_mul (N depth : Nat) (slope : ℚ)
    (hcheck : checkThetaLeMulWith N slope depth = true) :
    Chebyshev.theta (N : ℝ) ≤ (slope : ℝ) * N

theorem verify_theta_abs_error (N depth : Nat) (bound : ℚ)
    (hcheck : checkThetaAbsError N bound depth = true) :
    |Chebyshev.theta (N : ℝ) - N| ≤ (bound : ℝ)

theorem verify_theta_rel_error (N depth : Nat) (bound : ℚ)
    (hcheck : checkThetaRelError N bound depth = true) :
    |Chebyshev.theta (N : ℝ) - N| ≤ (bound : ℝ) * N
```

Range checkers have corresponding range Golden Theorems:

```lean
theorem verify_all_theta_le_mul
theorem verify_all_theta_abs_error
theorem verify_all_theta_rel_error
```

For real `x ∈ [N, N+1)`, use the strengthened interval certificate:

```lean
theorem verify_theta_rel_error_real (N depth : Nat) (bound : ℚ)
    (hbound : 0 ≤ bound) (hbound1 : bound ≤ 1)
    (hcheck : checkThetaRelErrorReal N bound depth = true)
    (x : ℝ) (hxlo : (N : ℝ) ≤ x) (hxhi : x < (N : ℝ) + 1) :
    |Chebyshev.theta x - x| ≤ (bound : ℝ) * x
```

## Example

```lean
import LeanCert.Engine.ChebyshevPsi

open Chebyshev (psi)
open LeanCert.Engine.ChebyshevPsi

example :
    ∀ N : Nat, 0 < N → N ≤ 20 →
      psi (N : ℝ) ≤ (3 : ℝ) * N := by
  exact verify_all_psi_le_mul 20 20 3 (by native_decide)
```

## Notes

The older theorem names such as `psi_le_of_checkPsiLeMulWith` and
`abs_theta_sub_le_mul_of_checkThetaRelError` remain available. The `verify_*`
names are thin public aliases matching the rest of LeanCert's Golden Theorem
style.
