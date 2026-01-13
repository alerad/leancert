/-
Copyright (c) 2024 LeanBound Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanBound Contributors
-/
import LeanBound.Numerics.TaylorModel.Trig
import LeanBound.Numerics.TaylorModel.ExpLog
import LeanBound.Numerics.TaylorModel.Hyperbolic
import LeanBound.Numerics.TaylorModel.Special

/-!
# Taylor Models - Function-Specific Definitions

This file re-exports all function-specific Taylor model definitions.
The implementation is split into:

* `TaylorModel/Trig.lean` - Sin, Cos, Sinc (and future Tan)
* `TaylorModel/ExpLog.lean` - Exp, Log
* `TaylorModel/Hyperbolic.lean` - Sinh, Cosh, Tanh, Atan, Atanh, Asinh
* `TaylorModel/Special.lean` - Erf (and future Sqrt)

## Main definitions (re-exported)

### Trig
* `sinTaylorPoly`, `cosTaylorPoly`, `sincTaylorPoly`
* `tmSin`, `tmCos`, `tmSinc`
* `tmSin_correct`, `tmCos_correct`

### ExpLog
* `expTaylorPoly`, `logTaylorPolyAtCenter`
* `tmExp`, `tmLog`
* `tmExp_correct`, `tmLog_correct`

### Hyperbolic
* `sinhTaylorPoly`, `coshTaylorPoly`, `atanTaylorPoly`, `atanhTaylorPoly`, `asinhTaylorPoly`
* `tmSinh`, `tmCosh`, `tmTanh`, `tmAtan`, `tmAtanh`, `tmAsinh`
* `tmSinh_correct`, `tmCosh_correct`, `tmAtanh_correct`

### Special
* `erfTaylorPoly`
* `tmErf`
-/
