//! Cast and indexing lowering helpers.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Part of #2526.

use super::super::{infer_expr_type, lower_syn_expr_with_depth, LoweringError, TypeEnv};
use super::collections::{extract_receiver_name, lowered_receiver_name};
use crate::ir::TrustVcType;
use crate::ir_expr::TrustVcExpr;

pub(in crate::ir_lowering) fn lower_cast(
    cast: &syn::ExprCast,
    env: &TypeEnv,
    depth: usize,
) -> Result<TrustVcExpr, LoweringError> {
    let inner = lower_syn_expr_with_depth(&cast.expr, env, depth)?;
    let from_ty = infer_expr_type(&inner);
    let to_ty = env
        .resolve_syn_type(&cast.ty)
        .map_err(|err| LoweringError::InvalidCast(err.to_string()))?;
    if matches!(to_ty, TrustVcType::Bool) {
        return Err(LoweringError::InvalidCast(
            "unsupported cast target type: bool".into(),
        ));
    }
    // An exact real cast to a fixed-width integer: the source is a Rust float
    // (an unsuffixed float literal, the value of a `let` of one), whose `as`
    // truncates toward zero and SATURATES (NaN is 0), while the real cast
    // floors and wraps — `let f = 300.0; f as u8 == 44` and `-1.5 as i8 ==
    // -2` were `Verified` (Rust gives 255 and -1). Refused.
    if matches!(from_ty, TrustVcType::Real)
        && matches!(to_ty, TrustVcType::Int { .. } | TrustVcType::Uint { .. })
    {
        return Err(LoweringError::InvalidCast(format!(
            "`as {}` from an exact real is not modelled: the value is a Rust float, whose \
             cast to an integer truncates and saturates",
            to_ty.to_type_string()
        )));
    }
    // SOUNDNESS (H3, latent): rustc accepts an integer-to-`char` cast ONLY from
    // `u8` (E0604) — every `u8` is a Unicode scalar value, so the cast needs no
    // validity guard. Any other source (`0xD800u32 as char`) is not Rust, and
    // the cast node carries no validity guard, so `(0xD800u32 as char) as u32
    // == 0xD800u32` would verify. Admit `u8`, `char`, and an unsuffixed integer
    // literal in `0..=255` (rustc infers it `u8`); fail closed on the rest.
    if matches!(to_ty, TrustVcType::Char)
        && !int_to_char_cast_source_is_valid(&cast.expr, &inner, &from_ty)
    {
        return Err(LoweringError::InvalidCast(format!(
            "only `u8` can be cast as `char`, not `{}` (rustc E0604); an unchecked \
             integer-to-char reinterpretation fails closed",
            from_ty.to_type_string()
        )));
    }
    Ok(TrustVcExpr::Cast {
        expr: Box::new(inner),
        from_ty,
        to_ty,
    })
}

fn int_to_char_cast_source_is_valid(
    source: &syn::Expr,
    inner: &TrustVcExpr,
    from_ty: &TrustVcType,
) -> bool {
    match from_ty {
        TrustVcType::Char | TrustVcType::Uint { width: 8 } => true,
        // The placeholder type of an UNSUFFIXED integer literal (see
        // `type_from_int_suffix("")`): rustc infers `u8` for `97 as char`. An
        // explicitly `i32`-suffixed literal (`97i32 as char`, E0604) shares
        // the placeholder, so the SOURCE literal must carry no suffix.
        TrustVcType::Int { width: 32 } => {
            is_unsuffixed_int_literal(source)
                && matches!(
                    inner,
                    TrustVcExpr::IntLit { value, .. } if (0..=255).contains(value)
                )
        }
        _ => false,
    }
}

fn is_unsuffixed_int_literal(expr: &syn::Expr) -> bool {
    match expr {
        syn::Expr::Paren(paren) => is_unsuffixed_int_literal(&paren.expr),
        syn::Expr::Group(group) => is_unsuffixed_int_literal(&group.expr),
        syn::Expr::Lit(syn::ExprLit {
            lit: syn::Lit::Int(int_lit),
            ..
        }) => int_lit.suffix().is_empty(),
        _ => false,
    }
}

pub(in crate::ir_lowering) fn lower_index(
    idx: &syn::ExprIndex,
    env: &TypeEnv,
    depth: usize,
) -> Result<TrustVcExpr, LoweringError> {
    let receiver = lower_syn_expr_with_depth(&idx.expr, env, depth)?;
    // An element of an array of unsuffixed literals whose element type its
    // uses do not determine (`untyped_site`): read as an element of the
    // array's `i32` placeholder type, it met its peers as a typed value and
    // escaped the every-type check.
    if crate::ir_lowering::holds_undetermined_form(&receiver) {
        return Err(LoweringError::UnsupportedExpr(format!(
            "`{}` reads an element of an array of unsuffixed integer literals whose element \
             type is not determined here",
            quote::ToTokens::to_token_stream(idx)
        )));
    }
    let index = lower_syn_expr_with_depth(&idx.index, env, depth)?;
    let receiver_name =
        extract_receiver_name(&idx.expr).or_else(|| lowered_receiver_name(&receiver));
    let receiver_ty = infer_expr_type(&receiver);
    let elem_ty = match &receiver_ty {
        TrustVcType::Seq(elem) | TrustVcType::Array(elem, _) => *elem.clone(),
        TrustVcType::Map(_, val) => *val.clone(),
        _ => {
            return Err(LoweringError::TypeInference(format!(
                "indexing requires Seq/Map/array receiver, got '{}'",
                receiver_ty.to_type_string()
            )))
        }
    };
    Ok(TrustVcExpr::Index {
        receiver: Box::new(receiver),
        index: Box::new(index),
        receiver_name,
        elem_ty,
    })
}
