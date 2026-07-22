/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import Mathlib.Tactic
import LeanCert.Meta.ToExpr

/-!
# Reification Bridge Normalization

The reflected expression is often definitionally related to the user's term
but not syntactically identical: custom wrappers were unfolded, subtraction
was lowered to addition and negation, and powers became multiplication.  This
module centralizes that final, proof-producing conversion.
-/

open Lean Meta Elab Tactic

namespace LeanCert.Tactic

/-- Delta-reduce exactly the user definitions recorded by reification. -/
def unfoldReifiedDefinitions (unfolded : Array Name) : TacticM Unit := do
  for name in unfolded do
    let ident := mkIdent name
    evalTactic (← `(tactic| try unfold $ident))

/-- Close a semantic bridge between a user's real expression and its reflected
`LeanCert.Core.Expr.eval` form.

Only definitions actually unfolded by the reifier are delta-reduced.  The
remaining normalization is a fixed, auditable collection of evaluation and
ordinary arithmetic identities. -/
def closeReificationBridge (report : LeanCert.Meta.ReifyReport) : TacticM Unit := do
  unfoldReifiedDefinitions report.unfolded
  evalTactic (← `(tactic|
    first
    | rfl
    | (simp only [
        LeanCert.Core.Expr.eval_add,
        LeanCert.Core.Expr.eval_mul,
        LeanCert.Core.Expr.eval_neg,
        LeanCert.Core.Expr.eval_inv,
        LeanCert.Core.Expr.eval_const,
        LeanCert.Core.Expr.eval_var,
        LeanCert.Core.Expr.eval_sin,
        LeanCert.Core.Expr.eval_cos,
        LeanCert.Core.Expr.eval_exp,
        LeanCert.Core.Expr.eval_log,
        LeanCert.Core.Expr.eval_atan,
        LeanCert.Core.Expr.eval_arsinh,
        LeanCert.Core.Expr.eval_atanh,
        LeanCert.Core.Expr.eval_sinc,
        LeanCert.Core.Expr.eval_erf,
        LeanCert.Core.Expr.eval_sinh,
        LeanCert.Core.Expr.eval_cosh,
        LeanCert.Core.Expr.eval_tanh,
        LeanCert.Core.Expr.eval_sqrt,
        LeanCert.Core.Expr.eval_namedConst,
        LeanCert.Core.Expr.eval_sub,
        LeanCert.Core.Expr.eval_div,
        LeanCert.Core.Expr.eval_pow,
        Rat.divInt_eq_div,
        sq, pow_two, pow_succ, pow_zero, pow_one,
        sub_eq_add_neg, div_eq_mul_inv,
        one_mul, mul_one];
       try push_cast;
       try ring)))

end LeanCert.Tactic
