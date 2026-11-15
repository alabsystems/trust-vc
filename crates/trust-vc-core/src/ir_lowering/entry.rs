//! Top-level expression lowering entrypoints and depth guards.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use crate::expr_depth::MAX_EXPR_DEPTH;
use crate::ir::TrustVcType;
use crate::ir_expr::{tuple_datatype_type, TrustVcExpr, TUPLE_VARIANT_NAME};

use super::{
    arrays::{lower_array_literal, lower_array_repeat},
    atoms::{lower_lit, lower_path},
    control_flow, dispatch, infer_expr_type, match_lowering, operators, LoweringError, TypeEnv,
};

/// Refuse an UNSUFFIXED float literal form (`0.1`, `-(1.5)`, `0.1 * 3.0`)
/// held by an aggregate — a tuple, an array, an `Option`/`Result` payload.
/// Its type is a Rust float that only a later use fixes, but it is lowered as
/// the exact `real` it is next to a `real` peer, so `let p = (0.1, 0.2);
/// p.0 + p.1 == 0.3` was `Verified` where `f64` arithmetic makes it false.
pub(super) fn refuse_unsuffixed_float_elements<'e>(
    elems: impl Iterator<Item = &'e syn::Expr>,
    holder: &str,
) -> Result<(), LoweringError> {
    for elem in elems {
        if operators::is_unsuffixed_float_literal_tree(elem) {
            return Err(LoweringError::UnsupportedExpr(format!(
                "`{}` is an unsuffixed float literal held by {holder}: its type is a Rust \
                 float (`f64` by default), whose rounding an exact real does not model",
                quote::ToTokens::to_token_stream(elem)
            )));
        }
    }
    Ok(())
}

/// Refuse an unsuffixed float literal form written into a field of a struct
/// literal or an enum-variant struct literal whose declared type is not the
/// exact `real`: a generic field (`struct W<T> { x: T }`) takes the literal's
/// own Rust float type, which only a later use fixes, and the literal was the
/// exact `real` through it, so `W { x: 0.1 }.x + 0.2 == 0.3` was `Verified`
/// where `f64` arithmetic makes it false. A field of a Rust float type is
/// refused alike: the literal's `f64` rounding is not modelled.
pub(super) fn refuse_unsuffixed_float_fields<'e>(
    fields: impl Iterator<Item = &'e syn::FieldValue>,
    declared: &[(String, TrustVcType)],
    holder: &str,
) -> Result<(), LoweringError> {
    for field in fields {
        let name = match &field.member {
            syn::Member::Named(ident) => ident.to_string(),
            syn::Member::Unnamed(index) => index.index.to_string(),
        };
        let exact_real = declared
            .iter()
            .any(|(declared_name, ty)| *declared_name == name && *ty == TrustVcType::Real);
        if !exact_real {
            refuse_unsuffixed_float_elements(std::iter::once(&field.expr), holder)?;
        }
    }
    Ok(())
}

/// Lowers a `syn::Expr` into a `TrustVcExpr`.
///
/// Every `syn::Expr` variant is explicitly handled. No silent drops.
pub(crate) fn lower_syn_expr(
    expr: &syn::Expr,
    env: &TypeEnv,
) -> Result<TrustVcExpr, LoweringError> {
    lower_syn_expr_with_depth(expr, env, 0)
}

pub(crate) fn lower_syn_expr_with_depth(
    expr: &syn::Expr,
    env: &TypeEnv,
    depth: usize,
) -> Result<TrustVcExpr, LoweringError> {
    let current_depth = next_lowering_depth(depth)?;
    match expr {
        syn::Expr::Lit(lit) => lower_lit(lit),
        syn::Expr::Path(path) => lower_path(path, env),
        syn::Expr::Binary(bin) => operators::lower_binary(bin, env, current_depth),
        syn::Expr::Unary(un) => operators::lower_unary(un, env, current_depth),
        syn::Expr::Paren(p) => lower_syn_expr_with_depth(&p.expr, env, current_depth),
        syn::Expr::Group(g) => lower_syn_expr_with_depth(&g.expr, env, current_depth),
        syn::Expr::If(if_expr) => control_flow::lower_if(if_expr, env, current_depth),
        syn::Expr::Block(b) => control_flow::lower_block_expr(&b.block, env, current_depth),
        syn::Expr::Match(m) => match_lowering::lower_match(m, env, current_depth),
        syn::Expr::MethodCall(mc) => dispatch::lower_method_call(mc, env, current_depth),
        syn::Expr::Call(call) => dispatch::lower_call(call, env, current_depth),
        syn::Expr::Cast(cast) => dispatch::lower_cast(cast, env, current_depth),
        syn::Expr::Index(idx) => dispatch::lower_index(idx, env, current_depth),
        syn::Expr::Return(ret) => match &ret.expr {
            Some(inner) => lower_syn_expr_with_depth(inner, env, current_depth),
            None => Err(LoweringError::UnsupportedExpr(
                "return without value".into(),
            )),
        },
        syn::Expr::Reference(r) => {
            if r.mutability.is_some() {
                Err(LoweringError::UnsupportedExpr("&mut not supported".into()))
            } else {
                lower_syn_expr_with_depth(&r.expr, env, current_depth)
            }
        }
        syn::Expr::Closure(_) => Err(LoweringError::UnsupportedExpr(
            "standalone closure (only supported as quantifier argument or SpecFn::new argument)"
                .into(),
        )),
        syn::Expr::Field(field) => {
            match lower_direct_tuple_field_access(field, env, current_depth)? {
                Some(expr) => Ok(expr),
                None => dispatch::lower_field_access(field, env, current_depth),
            }
        }
        syn::Expr::Tuple(tuple) if tuple.elems.is_empty() => Ok(TrustVcExpr::UnitLit),
        syn::Expr::Tuple(tuple) => {
            refuse_unsuffixed_float_elements(tuple.elems.iter(), "a tuple")?;
            lower_tuple_expr(tuple, env, current_depth)
        }
        syn::Expr::Range(_) => Err(LoweringError::UnsupportedExpr("range".into())),
        syn::Expr::Assign(_) => Err(LoweringError::UnsupportedExpr("assignment".into())),
        syn::Expr::Let(_) => Err(LoweringError::UnsupportedExpr("if-let pattern".into())),
        syn::Expr::Array(array) => {
            refuse_unsuffixed_float_elements(array.elems.iter(), "an array")?;
            lower_array_literal(array, env, current_depth)
        }
        syn::Expr::Async(_) => Err(LoweringError::UnsupportedExpr("async block".into())),
        syn::Expr::Await(_) => Err(LoweringError::UnsupportedExpr("await".into())),
        syn::Expr::Break(_) => Err(LoweringError::UnsupportedExpr("break".into())),
        syn::Expr::Continue(_) => Err(LoweringError::UnsupportedExpr("continue".into())),
        syn::Expr::ForLoop(_) => Err(LoweringError::UnsupportedExpr("for loop".into())),
        syn::Expr::Loop(_) => Err(LoweringError::UnsupportedExpr("loop".into())),
        syn::Expr::While(_) => Err(LoweringError::UnsupportedExpr("while loop".into())),
        syn::Expr::Repeat(repeat) => lower_array_repeat(repeat, env, current_depth),
        syn::Expr::Struct(struct_expr) => {
            dispatch::lower_struct_literal(struct_expr, env, current_depth)
        }
        syn::Expr::Try(_) => Err(LoweringError::UnsupportedExpr("try (?)".into())),
        syn::Expr::TryBlock(_) => Err(LoweringError::UnsupportedExpr("try block".into())),
        syn::Expr::Unsafe(_) => Err(LoweringError::UnsupportedExpr("unsafe block".into())),
        syn::Expr::Yield(_) => Err(LoweringError::UnsupportedExpr("yield".into())),
        syn::Expr::Macro(mac) => dispatch::lower_macro_expr(mac, env, current_depth),
        syn::Expr::Const(_) => Err(LoweringError::UnsupportedExpr("const block".into())),
        syn::Expr::Infer(_) => Err(LoweringError::UnsupportedExpr("infer (_)".into())),
        syn::Expr::RawAddr(_) => Err(LoweringError::UnsupportedExpr("raw address".into())),
        syn::Expr::Verbatim(_) => Err(LoweringError::UnsupportedExpr("verbatim".into())),
        _ => Err(LoweringError::UnsupportedExpr(
            "unknown syn::Expr variant".into(),
        )),
    }
}

fn lower_direct_tuple_field_access(
    field: &syn::ExprField,
    env: &TypeEnv,
    depth: usize,
) -> Result<Option<TrustVcExpr>, LoweringError> {
    let syn::Member::Unnamed(index) = &field.member else {
        return Ok(None);
    };
    let receiver = lower_syn_expr_with_depth(&field.base, env, depth)?;
    let TrustVcExpr::FnCall {
        name,
        args,
        return_ty,
    } = receiver
    else {
        return Ok(None);
    };
    let TrustVcType::Datatype {
        name: datatype_name,
        variants,
    } = &return_ty
    else {
        return Ok(None);
    };
    let [variant] = variants.as_slice() else {
        return Ok(None);
    };
    if variant.name != TUPLE_VARIANT_NAME
        || name != crate::encoder::datatype::variant_symbol_name(datatype_name, TUPLE_VARIANT_NAME)
    {
        return Ok(None);
    }
    let index = index.index as usize;
    let Some(arg) = args.get(index) else {
        return Err(LoweringError::UnsupportedExpr(format!(
            "tuple field '{}' on {}-element tuple",
            index,
            args.len()
        )));
    };
    Ok(Some(arg.clone()))
}

fn lower_tuple_expr(
    tuple: &syn::ExprTuple,
    env: &TypeEnv,
    depth: usize,
) -> Result<TrustVcExpr, LoweringError> {
    let elems = tuple
        .elems
        .iter()
        .map(|elem| lower_syn_expr_with_depth(elem, env, depth))
        .collect::<Result<Vec<_>, _>>()?;
    let elem_tys = elems.iter().map(infer_expr_type).collect();
    let tuple_ty = tuple_datatype_type(elem_tys);
    let TrustVcType::Datatype { name, .. } = &tuple_ty else {
        unreachable!(
            "tuple_datatype_type always returns TrustVcType::Datatype for non-unit tuples"
        );
    };

    Ok(TrustVcExpr::FnCall {
        name: crate::encoder::datatype::variant_symbol_name(name, TUPLE_VARIANT_NAME),
        args: elems,
        return_ty: tuple_ty,
    })
}

pub(crate) fn next_lowering_depth(depth: usize) -> Result<usize, LoweringError> {
    if depth >= MAX_EXPR_DEPTH {
        Err(LoweringError::ExpressionTooDeep {
            limit: MAX_EXPR_DEPTH,
            stage: "IR lowering",
        })
    } else {
        Ok(depth + 1)
    }
}
