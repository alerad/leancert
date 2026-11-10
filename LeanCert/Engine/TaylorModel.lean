/-
Copyright (c) 2024 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
module

public import LeanCert.Engine.TaylorModel.Core
public import LeanCert.Engine.TaylorModel.Functions
public import LeanCert.Engine.TaylorModel.Expr
public import LeanCert.Engine.TaylorModel.Integral

/-!
# Taylor Models

This file re-exports all Taylor model functionality. The implementation is split into:

* `TaylorModel.Core` - Core data structure, polynomial helpers, basic operations
* `TaylorModel.Functions` - Function-specific Taylor series (sin, cos, exp, etc.)
* `TaylorModel.Expr` - Composition operations and expression integration
* `TaylorModel.Integral` - Definite-integral enclosures from Taylor-model bounds
-/
