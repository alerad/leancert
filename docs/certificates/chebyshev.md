# Chebyshev Certificates

LeanCert includes specialized certificate engines for finite Chebyshev function
bounds. These engines use computable rational upper/lower envelopes for
logarithmic summands, then expose Golden Theorems that turn successful boolean
checks into real-number bounds.

## Imports

```lean
import LeanCert.Engine.Chebyshev.Psi
import LeanCert.Engine.Chebyshev.Theta
```

or use the aggregate import:

```lean
import LeanCert
```

## Psi Bounds

`LeanCert.Engine.Chebyshev.Psi` certifies upper bounds for the second Chebyshev
function `ψ`.

Core checkers:

```text
checkPsiLeMulWith (N : Nat) (slope : ℚ) (depth : Nat)
checkAllPsiLeMulWith (bound : Nat) (slope : ℚ) (depth : Nat)
```
Golden Theorems:

```lean
#check verify_psi_le_mul
```
Real-variable form:

```lean
#check verify_all_psi_le_mul_real
```
## Theta Bounds

`LeanCert.Engine.Chebyshev.Theta` certifies upper, absolute-error, and
relative-error bounds for the first Chebyshev function `θ`.

Core checkers:

```text
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
#check verify_theta_le_mul
```
Range checkers have corresponding range Golden Theorems:

```lean
#check verify_all_theta_le_mul
```
For real `x ∈ [N, N+1)`, use the strengthened interval certificate:

```lean
#check verify_theta_rel_error_real
```
## Example

```lean
import LeanCert.Engine.Chebyshev.Psi

open Chebyshev (psi)
open LeanCert.Engine.Chebyshev.Psi

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
