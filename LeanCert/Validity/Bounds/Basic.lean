/-
Copyright (c) 2024 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
module

public import LeanCert.Validity.Bounds.Core
public import LeanCert.Validity.Bounds.Checked
public import LeanCert.Validity.Bounds.Smart
public import LeanCert.Validity.Bounds.Bridge

/-!
# Bounds Module Index

This module re-exports all components of the bounds verification infrastructure.

## Submodules

- `Core`: Basic boolean checkers and golden theorems for bound verification
- `Checked`: Support for expressions with inverse-like operations (inv, log, atan, etc.)
- `Smart`: Monotonicity-aware bounds using derivative information
- `Bridge`: Set.Icc bridge theorems and subdivision combinators

## Usage

Import this module to get access to all bound verification functionality:

```lean
public import LeanCert.Validity.Bounds.Basic
```
-/
