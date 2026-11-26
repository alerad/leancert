/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
module

public import LeanCert.Tactic.IntervalAuto
public import LeanCert.Tactic.Refute
public import LeanCert.Tactic.FinSumExpand
public import LeanCert.Tactic.FinSumBound
public import LeanCert.Tactic.FinSumWitness
public import LeanCert.Tactic.EventualBound
public import LeanCert.Tactic.Krawczyk
public import LeanCert.Tactic.VecSimp
public import LeanCert.Tactic.LeanCert
public import LeanCert.Tactic.Discovery
public import LeanCert.Tactic.Extension
public import LeanCert.Tactic.Enclosure

/-!
# LeanCert tactic API

Stable umbrella import for LeanCert's supported tactics. Downstream projects
should prefer

```lean
public import LeanCert.Tactic
```

over importing tactic implementation modules directly.
-/
