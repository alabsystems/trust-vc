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
    Ok(TrustVcExpr::Cast {
        expr: Box::new(inner),
        from_ty,
        to_ty,
    })
}

pub(in crate::ir_lowering) fn lower_index(
    idx: &syn::ExprIndex,
    env: &TypeEnv,
    depth: usize,
) -> Result<TrustVcExpr, LoweringError> {
    let receiver = lower_syn_expr_with_depth(&idx.expr, env, depth)?;
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
