//! Best-effort TrustVcExpr type inference helpers.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use crate::ir::TrustVcType;
use crate::ir_expr::TrustVcExpr;

/// Best-effort type inference from a TrustVcExpr.
pub(crate) fn infer_expr_type(expr: &TrustVcExpr) -> TrustVcType {
    match expr {
        TrustVcExpr::UnitLit => TrustVcType::Unit,
        TrustVcExpr::BoolLit(_)
        | TrustVcExpr::Compare { .. }
        | TrustVcExpr::Logic { .. }
        | TrustVcExpr::Implies { .. }
        | TrustVcExpr::Quantifier { .. } => TrustVcType::Bool,
        // `!` is overloaded: logical-not over a `bool` yields `bool`, but
        // bitwise-not over a finite-width integer (`!x` where `x: i32`) yields
        // that integer type. Reporting `bool` for the bitwise case mis-typed a
        // surrounding `(!x) as i64` cast as `bool as i64`, which routed to the
        // bool→int lowering and fed a `BitVec` term into an `ite` condition
        // ("sort mismatch in ite: expected Bool, got (_ BitVec N)"). Mirror the
        // `Neg` rule: propagate an integer operand's type, fall back to `bool`.
        TrustVcExpr::Not(inner) => {
            let inner_ty = infer_expr_type(inner);
            if inner_ty.is_integer() {
                inner_ty
            } else {
                TrustVcType::Bool
            }
        }
        TrustVcExpr::StringLit(_) => TrustVcType::StrSlice,
        TrustVcExpr::IntLit { ty, .. }
        | TrustVcExpr::Var { ty, .. }
        | TrustVcExpr::Arith { ty, .. }
        | TrustVcExpr::Ite { ty, .. }
        | TrustVcExpr::Match { ty, .. }
        | TrustVcExpr::CollectionOp { ty, .. }
        | TrustVcExpr::SpecClosure { ty, .. }
        | TrustVcExpr::IntConst { ty, .. }
        | TrustVcExpr::SpecialArith { ty, .. }
        | TrustVcExpr::WrappingArith { ty, .. } => ty.clone(),
        TrustVcExpr::Neg(inner) => infer_expr_type(inner),
        TrustVcExpr::Let { body, .. } => infer_expr_type(body),
        TrustVcExpr::Cast { to_ty, .. } => to_ty.clone(),
        TrustVcExpr::Index { elem_ty, .. } => elem_ty.clone(),
        TrustVcExpr::FnCall { return_ty, .. } => return_ty.clone(),
        TrustVcExpr::Choose { var_ty, .. } => var_ty.clone(),
        TrustVcExpr::ReadPlace { ty, .. } => ty.clone(),
        TrustVcExpr::PlaceDisjoint { .. } => TrustVcType::Bool,
        TrustVcExpr::ProphecyNew { ty, .. } => ty.clone(),
        TrustVcExpr::ProphecyResolve { value, .. } => infer_expr_type(value),
    }
}
