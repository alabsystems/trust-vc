// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Type-inferring builder variants for codegen paths.
//!
//! These functions infer the result type from operands and coerce unsuffixed
//! `Int{32}` literals to match the peer operand's type. Used by
//! `expr_codegen.rs` where the result type is not known at compile time.

use crate::ir::TrustVcType;
use crate::ir_expr::{ArithOp, CollectionOp, CompareOp, SpecialArithOp, TrustVcExpr, WrappingMode};

/// Coerces unsuffixed `Int{32}` literals to match a peer operand's type.
///
/// Local mirror of `ir_lowering::operators::coerce_unsuffixed_literal` to
/// avoid reaching into the private `operators` module, which breaks clean-
/// clone builds (module `operators` is `mod`, not `pub(crate) mod`).
/// Part of #2187.
fn coerce_unsuffixed_literal(expr: TrustVcExpr, peer_ty: &TrustVcType) -> TrustVcExpr {
    match expr {
        TrustVcExpr::IntLit {
            value,
            ty: TrustVcType::Int { width: 32 },
        } if matches!(peer_ty, TrustVcType::Uint { .. } | TrustVcType::Int { .. }) => {
            TrustVcExpr::IntLit {
                value,
                ty: peer_ty.clone(),
            }
        }
        TrustVcExpr::Neg(inner)
            if matches!(
                inner.as_ref(),
                TrustVcExpr::IntLit {
                    ty: TrustVcType::Int { width: 32 },
                    ..
                }
            ) && matches!(peer_ty, TrustVcType::Uint { .. } | TrustVcType::Int { .. }) =>
        {
            TrustVcExpr::Neg(Box::new(coerce_unsuffixed_literal(*inner, peer_ty)))
        }
        other => other,
    }
}

fn collection_receiver_name(expr: &TrustVcExpr) -> Option<String> {
    match expr {
        TrustVcExpr::Var { name, .. } => Some(name.clone()),
        TrustVcExpr::FnCall { name, args, .. } if args.is_empty() => Some(name.clone()),
        TrustVcExpr::CollectionOp {
            receiver_name,
            receiver,
            ..
        }
        | TrustVcExpr::Index {
            receiver_name,
            receiver,
            ..
        } => receiver_name
            .clone()
            .or_else(|| collection_receiver_name(receiver)),
        TrustVcExpr::Cast { expr, .. } => collection_receiver_name(expr),
        _ => None,
    }
}

fn try_seq_add_operator(
    left: TrustVcExpr,
    right: TrustVcExpr,
    left_ty: &TrustVcType,
    right_ty: &TrustVcType,
) -> Result<TrustVcExpr, Box<(TrustVcExpr, TrustVcExpr)>> {
    if matches!(left_ty, TrustVcType::Seq(_)) && left_ty == right_ty {
        let receiver_name = collection_receiver_name(&left);
        Ok(TrustVcExpr::CollectionOp {
            op: CollectionOp::Add,
            receiver: Box::new(left),
            receiver_name,
            args: vec![right],
            ty: left_ty.clone(),
        })
    } else {
        Err(Box::new((left, right)))
    }
}

/// Like `arith` but infers the result type from operands and coerces
/// unsuffixed `Int{32}` literals to match the peer operand's type.
///
/// Matches the behavior of `ir_lowering::operators::lower_arith`. Use this
/// from codegen paths where the result type is not known at compile time.
#[must_use]
pub fn arith_inferred(op: ArithOp, left: TrustVcExpr, right: TrustVcExpr) -> TrustVcExpr {
    use crate::ir_lowering::infer_expr_type;
    let left_ty = infer_expr_type(&left);
    let right_ty = infer_expr_type(&right);
    if matches!(op, ArithOp::Add) {
        match try_seq_add_operator(left, right, &left_ty, &right_ty) {
            Ok(expr) => return expr,
            Err(returned) => {
                let (returned_left, returned_right) = *returned;
                let left = coerce_unsuffixed_literal(returned_left, &right_ty);
                let right = coerce_unsuffixed_literal(returned_right, &left_ty);
                let ty = infer_expr_type(&left);
                return TrustVcExpr::Arith {
                    op,
                    left: Box::new(left),
                    right: Box::new(right),
                    ty,
                };
            }
        }
    }
    let left = coerce_unsuffixed_literal(left, &right_ty);
    let right = coerce_unsuffixed_literal(right, &left_ty);
    let ty = infer_expr_type(&left);
    TrustVcExpr::Arith {
        op,
        left: Box::new(left),
        right: Box::new(right),
        ty,
    }
}

/// Like `special_arith` but infers the result type from operands and coerces
/// unsuffixed `Int{32}` literals to match the peer operand's type.
///
/// Matches the behavior of `ir_lowering::operators::lower_special`. Use this
/// from codegen paths where the result type is not known at compile time.
#[must_use]
pub fn special_arith_inferred(
    op: SpecialArithOp,
    left: TrustVcExpr,
    right: TrustVcExpr,
) -> TrustVcExpr {
    use crate::ir_lowering::infer_expr_type;
    let left_ty = infer_expr_type(&left);
    let right_ty = infer_expr_type(&right);
    if matches!(op, SpecialArithOp::BitXor)
        && matches!(left_ty, TrustVcType::Bool)
        && matches!(right_ty, TrustVcType::Bool)
    {
        return TrustVcExpr::Compare {
            op: CompareOp::Ne,
            left: Box::new(left),
            right: Box::new(right),
        };
    }
    let left = coerce_unsuffixed_literal(left, &right_ty);
    let right = coerce_unsuffixed_literal(right, &left_ty);
    let ty = infer_expr_type(&left);
    TrustVcExpr::SpecialArith {
        op,
        left: Box::new(left),
        right: Box::new(right),
        ty,
    }
}

/// Like `ite` but infers the result type from branches and coerces
/// unsuffixed `Int{32}` literals to match the peer branch's type.
///
/// Use this from codegen paths where the result type is not known at
/// compile time.
#[must_use]
pub fn ite_inferred(
    cond: TrustVcExpr,
    then_branch: TrustVcExpr,
    else_branch: TrustVcExpr,
) -> TrustVcExpr {
    use crate::ir_lowering::infer_expr_type;
    let then_ty = infer_expr_type(&then_branch);
    let else_ty = infer_expr_type(&else_branch);
    let then_branch = coerce_unsuffixed_literal(then_branch, &else_ty);
    let else_branch = coerce_unsuffixed_literal(else_branch, &then_ty);
    let ty = infer_expr_type(&then_branch);
    TrustVcExpr::Ite {
        cond: Box::new(cond),
        then_branch: Box::new(then_branch),
        else_branch: Box::new(else_branch),
        ty,
    }
}

/// Like `wrapping_arith` but infers the result type from operands and coerces
/// unsuffixed `Int{32}` literals to match the peer operand's type.
///
/// Use this from codegen paths where the result type is not known at
/// compile time.
#[must_use]
pub fn wrapping_arith_inferred(
    mode: WrappingMode,
    op: ArithOp,
    left: TrustVcExpr,
    right: TrustVcExpr,
) -> TrustVcExpr {
    use crate::ir_lowering::infer_expr_type;
    let left_ty = infer_expr_type(&left);
    let right_ty = infer_expr_type(&right);
    let left = coerce_unsuffixed_literal(left, &right_ty);
    let right = coerce_unsuffixed_literal(right, &left_ty);
    let ty = infer_expr_type(&left);
    TrustVcExpr::WrappingArith {
        mode,
        op,
        left: Box::new(left),
        right: Box::new(right),
        ty,
    }
}

/// Like `cast` but infers `from_ty` from the inner expression.
///
/// Use this from codegen paths where the source type is not known at
/// compile time.
#[must_use]
pub fn cast_inferred(expr: TrustVcExpr, to_ty: TrustVcType) -> TrustVcExpr {
    use crate::ir_lowering::infer_expr_type;
    let from_ty = infer_expr_type(&expr);
    TrustVcExpr::Cast {
        expr: Box::new(expr),
        from_ty,
        to_ty,
    }
}
