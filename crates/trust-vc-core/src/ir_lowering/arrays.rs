//! Native Rust array literal lowering.
//!
//! Fixed-size array values use the same solver storage shape as `Seq<T>`.
//! Literal/repeat expressions are lowered to the existing empty-Seq plus push
//! chain so element and length facts remain executable.

use super::{
    infer_expr_type, lower_syn_expr_with_depth, operators::coerce_unsuffixed_literal,
    LoweringError, TypeEnv, COLLECTION_CONSTRUCTOR_PREFIX,
};
use crate::ir::TrustVcType;
use crate::ir_expr::{CollectionOp, TrustVcExpr};

const ARRAY_LITERAL_REPEAT_LIMIT: usize = 16;

pub(super) fn lower_array_literal(
    array: &syn::ExprArray,
    env: &TypeEnv,
    depth: usize,
) -> Result<TrustVcExpr, LoweringError> {
    if array.elems.is_empty() {
        return Err(LoweringError::TypeInference(
            "array literal [] requires an element type".to_string(),
        ));
    }

    let elements = array
        .elems
        .iter()
        .map(|element| lower_syn_expr_with_depth(element, env, depth))
        .collect::<Result<Vec<_>, _>>()?;
    lower_array_elements_to_seq(elements, "array literal")
}

pub(super) fn lower_array_repeat(
    repeat: &syn::ExprRepeat,
    env: &TypeEnv,
    depth: usize,
) -> Result<TrustVcExpr, LoweringError> {
    let repeat_len = literal_repeat_len(&repeat.len)?;
    if repeat_len > ARRAY_LITERAL_REPEAT_LIMIT {
        return Err(LoweringError::UnsupportedExpr(format!(
            "array repeat supports literal lengths up to {ARRAY_LITERAL_REPEAT_LIMIT}, got {repeat_len}",
        )));
    }

    super::entry::refuse_unsuffixed_float_elements(
        std::iter::once(&*repeat.expr),
        "an array repeat",
    )?;
    let lowered = lower_syn_expr_with_depth(&repeat.expr, env, depth)?;
    lower_array_elements_to_seq(vec![lowered; repeat_len], "array repeat")
}

fn literal_repeat_len(expr: &syn::Expr) -> Result<usize, LoweringError> {
    let syn::Expr::Lit(lit) = expr else {
        return Err(LoweringError::UnsupportedExpr(
            "array repeat requires a literal length".to_string(),
        ));
    };
    let syn::Lit::Int(len) = &lit.lit else {
        return Err(LoweringError::UnsupportedExpr(
            "array repeat requires an integer literal length".to_string(),
        ));
    };
    len.base10_parse::<usize>().map_err(|err| {
        LoweringError::UnsupportedExpr(format!(
            "array repeat requires a usize literal length: {err}"
        ))
    })
}

fn lower_array_elements_to_seq(
    elements: Vec<TrustVcExpr>,
    context: &'static str,
) -> Result<TrustVcExpr, LoweringError> {
    let Some(first) = elements.first() else {
        return Err(LoweringError::TypeInference(format!(
            "{context} requires an element type"
        )));
    };

    let elem_ty = infer_expr_type(first);
    let seq_ty = TrustVcType::Seq(Box::new(elem_ty.clone()));
    let empty_name = seq_literal_empty_constructor_name(&elem_ty);
    let mut seq = TrustVcExpr::FnCall {
        name: empty_name.clone(),
        args: vec![],
        return_ty: seq_ty.clone(),
    };

    for element in elements {
        let element = coerce_unsuffixed_literal(element, &elem_ty);
        let element_ty = infer_expr_type(&element);
        if element_ty != elem_ty {
            return Err(LoweringError::TypeInference(format!(
                "{context} element type mismatch: expected '{}', got '{}'",
                elem_ty.to_type_string(),
                element_ty.to_type_string()
            )));
        }
        seq = TrustVcExpr::CollectionOp {
            op: CollectionOp::Push,
            receiver: Box::new(seq),
            receiver_name: Some(empty_name.clone()),
            args: vec![element],
            ty: seq_ty.clone(),
        };
    }

    Ok(seq)
}

fn seq_literal_empty_constructor_name(elem_ty: &TrustVcType) -> String {
    format!(
        "{COLLECTION_CONSTRUCTOR_PREFIX}Seq_{}_empty",
        collection_literal_type_component(elem_ty)
    )
}

fn collection_literal_type_component(ty: &TrustVcType) -> String {
    let rendered = ty.to_type_string();
    let mut sanitized = String::with_capacity(rendered.len());
    let mut last_was_underscore = false;
    for ch in rendered.chars() {
        if ch.is_ascii_alphanumeric() {
            sanitized.push(ch);
            last_was_underscore = false;
        } else if !last_was_underscore {
            sanitized.push('_');
            last_was_underscore = true;
        }
    }
    while sanitized.ends_with('_') {
        sanitized.pop();
    }
    sanitized
}
