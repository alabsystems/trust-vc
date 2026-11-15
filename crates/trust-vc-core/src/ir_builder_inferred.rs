// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Type-inferring builder variants for codegen paths.
//!
//! These functions derive the result type from the operands and type an
//! unsuffixed `Int{32}` literal by its peer operand where its value fits — the
//! syn lowering's rules (design-trust-proof-backend.md §5b). Used by
//! `expr_codegen.rs` where the result type is not known at compile time.

use crate::ir::TrustVcType;
use crate::ir_expr::{ArithOp, CollectionOp, CompareOp, SpecialArithOp, TrustVcExpr, WrappingMode};

/// Types an unsuffixed `Int{32}` literal by a peer operand's type — only
/// where that never changes its value: the literal (for `-v`, the literal
/// `-v`) takes the peer's type exactly when it is a value of that type
/// (`ir_lowering::untyped_literal_at_peer`, the rule the syn lowering's
/// `coerce_unsuffixed_literal` applies). This mirror used to retype by SHAPE:
/// `-1` next to a `u8` became `Neg(IntLit { 1, u8 })` — the `u8` negation of
/// 1, i.e. 255 — and `300` a `u8` literal no `u8` holds.
fn coerce_unsuffixed_literal(expr: TrustVcExpr, peer_ty: &TrustVcType) -> TrustVcExpr {
    let literal = match &expr {
        TrustVcExpr::IntLit { .. } => true,
        TrustVcExpr::Neg(inner) => matches!(inner.as_ref(), TrustVcExpr::IntLit { .. }),
        _ => false,
    };
    if !literal {
        return expr;
    }
    crate::ir_lowering::untyped_literal_at_peer(&expr, peer_ty).unwrap_or(expr)
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
                let ty = crate::ir_lowering::arith_node_type(op, &left, &right);
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
    // Derived from BOTH operands, as the syn lowering types the node
    // (`ir_lowering::arith_node_type`), never copied from the left one.
    let ty = crate::ir_lowering::arith_node_type(op, &left, &right);
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
    // Shifts take the LEFT operand's type; only the amount is typed by it (the
    // syn lowering's `lower_special`). Coercing the value toward the amount's
    // type re-typed a `1i32 << k` (`k: u32`) as a `u32` shift.
    if matches!(op, SpecialArithOp::Shl | SpecialArithOp::Shr) {
        let right = coerce_unsuffixed_literal(right, &left_ty);
        return TrustVcExpr::SpecialArith {
            op,
            left: Box::new(left),
            right: Box::new(right),
            ty: left_ty,
        };
    }
    let left = coerce_unsuffixed_literal(left, &right_ty);
    let right = coerce_unsuffixed_literal(right, &left_ty);
    let ty = crate::ir_lowering::derived_node_type(&left, &right);
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
    // Derived from both branches (`ir_lowering::derived_node_type`).
    let ty = crate::ir_lowering::derived_node_type(&then_branch, &else_branch);
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
