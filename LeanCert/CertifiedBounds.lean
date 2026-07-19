/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.CertifiedBounds.Li2
import LeanCert.CertifiedBounds.BKLNW
import LeanCert.CertifiedBounds.Chebyshev

/-!
# LeanCert certified-bounds API

Stable umbrella for generated and pre-verified numerical bounds intended for
downstream use. New downstream developments should prefer

```lean
import LeanCert.CertifiedBounds
```

and declarations below `LeanCert.CertifiedBounds` over implementation modules
under `LeanCert.Engine` or historical interfaces under `LeanCert.Examples`.

## Stability

Names in `LeanCert.CertifiedBounds` are part of LeanCert's supported downstream
API. Changes to their statements or removal require a compatibility period and
must keep the downstream pattern suite green.
-/
