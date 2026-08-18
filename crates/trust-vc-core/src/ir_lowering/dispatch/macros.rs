//! Macro and quantifier lowering helpers.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Part of #2526.

use std::collections::{HashMap, HashSet};

use super::super::{
    infer_expr_type, lower_syn_expr_with_depth, operators::coerce_unsuffixed_literal,
    type_from_int_suffix, LoweringError, TypeEnv, COLLECTION_CONSTRUCTOR_PREFIX,
};
use crate::ir::TrustVcType;
use crate::ir_expr::{
    tuple_datatype_type, CollectionOp, LogicOp, QuantifierKind, TrustVcExpr, TUPLE_VARIANT_NAME,
};
use crate::ir_expr_traversal::ScopeAwareTrustVcExprFolder;
use syn::parse::{Parse, ParseStream, Parser};

const SEQ_LITERAL_REPEAT_LIMIT: usize = 16;

/// Parsed `decreases_to!(l1, l2, ... => r1, r2, ...)` arguments: the LHS ("from"
/// / larger) and RHS ("to" / smaller) measure tuples, comma-separated within each
/// side and split by `=>`. Mirrors the `trust-vc` crate's runtime parser, but here
/// for the SPEC-verification lowering (the runtime macro expands to a compile
/// marker; in a spec position the raw `Expr::Macro` reaches this path instead).
struct DecreasesToArgs {
    lhs: Vec<syn::Expr>,
    rhs: Vec<syn::Expr>,
}

impl Parse for DecreasesToArgs {
    fn parse(input: ParseStream<'_>) -> syn::Result<Self> {
        let mut lhs = Vec::new();
        loop {
            lhs.push(input.parse::<syn::Expr>()?);
            if input.peek(syn::Token![=>]) {
                break;
            }
            input.parse::<syn::Token![,]>()?;
        }
        input.parse::<syn::Token![=>]>()?;
        let rhs =
            syn::punctuated::Punctuated::<syn::Expr, syn::Token![,]>::parse_terminated(input)?
                .into_iter()
                .collect();
        Ok(DecreasesToArgs { lhs, rhs })
    }
}

/// Lowers `decreases_to!(from => to)` (Verus's multidecrease predicate) to the
/// lexicographic strict order asserting the `to` tuple is smaller than the `from`
/// tuple. Single-component is the scalar case; multiple components are compared
/// left-to-right with tie-breaks. Reuses the same per-component well-order as the
/// `is_smaller_than(..)` surface (`super::calls`).
fn lower_decreases_to_macro(
    mac: &syn::ExprMacro,
    env: &TypeEnv,
    depth: usize,
) -> Result<TrustVcExpr, LoweringError> {
    let parsed: DecreasesToArgs = syn::parse2(mac.mac.tokens.clone()).map_err(|err| {
        LoweringError::UnsupportedExpr(format!(
            "malformed decreases_to! arguments (expected `lhs, ... => rhs, ...`): {}",
            err
        ))
    })?;
    if parsed.lhs.is_empty() || parsed.lhs.len() != parsed.rhs.len() {
        return Err(LoweringError::UnsupportedExpr(format!(
            "decreases_to! requires equal, non-empty LHS/RHS arity (got {} and {})",
            parsed.lhs.len(),
            parsed.rhs.len()
        )));
    }
    // `decreases_to!(from => to)` holds iff `to` is strictly smaller than `from`,
    // so each component pair is `(smaller = to_i, larger = from_i)`.
    let mut components = Vec::with_capacity(parsed.lhs.len());
    for (from, to) in parsed.lhs.iter().zip(parsed.rhs.iter()) {
        let larger = lower_syn_expr_with_depth(from, env, depth)?;
        let smaller = lower_syn_expr_with_depth(to, env, depth)?;
        components.push((smaller, larger));
    }
    Ok(super::calls::lexicographic_smaller(components))
}

pub(in crate::ir_lowering) fn lower_macro_expr(
    mac: &syn::ExprMacro,
    env: &TypeEnv,
    depth: usize,
) -> Result<TrustVcExpr, LoweringError> {
    let trailing_name = mac
        .mac
        .path
        .segments
        .last()
        .map(|segment| segment.ident.to_string());

    if trailing_name.as_deref() == Some(crate::chained_comparisons::IMPLIES_MARKER_MACRO) {
        return lower_implies_marker(mac, env, depth);
    }

    if trailing_name.as_deref() == Some(crate::chained_comparisons::IFF_MARKER_MACRO) {
        return lower_iff_marker(mac, env, depth);
    }

    if trailing_name.as_deref() == Some("choose") {
        let closure: syn::ExprClosure = syn::parse2(mac.mac.tokens.clone()).map_err(|err| {
            LoweringError::UnsupportedExpr(format!("choose! macro body must be a closure: {}", err))
        })?;
        return lower_choose_closure(&closure, env, depth);
    }

    if trailing_name.as_deref() == Some("decreases_to") {
        return lower_decreases_to_macro(mac, env, depth);
    }

    if trailing_name.as_deref() == Some("seq") {
        return lower_seq_macro(mac, env, depth);
    }

    if trailing_name.as_deref() == Some("vec") {
        return lower_vec_macro(mac, env, depth);
    }

    if trailing_name.as_deref() == Some("map") {
        return lower_map_macro(mac, env, depth);
    }

    if trailing_name.as_deref() == Some("set") {
        return lower_set_macro(mac, env, depth);
    }

    let build = match trailing_name.as_deref() {
        Some("ext_eq") => crate::extensional_eq::build_ext_eq_expr,
        Some("ext_ne") => crate::extensional_eq::build_ext_ne_expr,
        Some("strict_eq" | "equal") => crate::extensional_eq::build_strict_eq_expr,
        _ => return Err(LoweringError::UnsupportedExpr("macro".into())),
    };

    let args = syn::punctuated::Punctuated::<syn::Expr, syn::Token![,]>::parse_terminated
        .parse2(mac.mac.tokens.clone())
        .map_err(|err| {
            LoweringError::UnsupportedExpr(format!(
                "malformed extensional macro arguments: {}",
                err
            ))
        })?;
    let [lhs, rhs] = args
        .into_iter()
        .collect::<Vec<_>>()
        .try_into()
        .map_err(|_| {
            LoweringError::UnsupportedExpr(
                "ext_eq!/ext_ne!/strict_eq!/equal! require exactly two expression arguments"
                    .to_string(),
            )
        })?;

    let lhs = lower_syn_expr_with_depth(&lhs, env, depth)?;
    let rhs = lower_syn_expr_with_depth(&rhs, env, depth)?;

    Ok(build(lhs, rhs))
}

/// Lowers the `__trust_vc_implies!(premise, conclusion)` marker (produced by the
/// `==>`/`<==` rewrite in `chained_comparisons`) into a real
/// `TrustVcExpr::Implies`.
///
/// The premise and conclusion are re-parsed through the chain-aware parser so
/// that comparison chains, nested connectives, and other Verus-surface forms
/// inside either operand are normalized exactly as they would be at the top
/// level.
fn lower_implies_marker(
    mac: &syn::ExprMacro,
    env: &TypeEnv,
    depth: usize,
) -> Result<TrustVcExpr, LoweringError> {
    let (premise, conclusion) = lower_binary_marker_operands(mac, env, depth, "implication")?;
    Ok(TrustVcExpr::Implies {
        premise: Box::new(premise),
        conclusion: Box::new(conclusion),
    })
}

/// Lowers the `__trust_vc_iff!(lhs, rhs)` marker (produced by the `<==>` rewrite
/// in `chained_comparisons`) into the pure-boolean equivalence
/// `(lhs ==> rhs) && (rhs ==> lhs)`.
///
/// This is a sound boolean rewrite: it introduces no new IR node and reuses the
/// existing `Implies`/`Logic(And)` encoding the engine already verifies. Both
/// operands are re-parsed through the chain-aware parser exactly like the
/// implication marker, and each is duplicated into the two directional
/// implications.
fn lower_iff_marker(
    mac: &syn::ExprMacro,
    env: &TypeEnv,
    depth: usize,
) -> Result<TrustVcExpr, LoweringError> {
    let (lhs, rhs) = lower_binary_marker_operands(mac, env, depth, "equivalence")?;
    let forward = TrustVcExpr::Implies {
        premise: Box::new(lhs.clone()),
        conclusion: Box::new(rhs.clone()),
    };
    let backward = TrustVcExpr::Implies {
        premise: Box::new(rhs),
        conclusion: Box::new(lhs),
    };
    Ok(TrustVcExpr::Logic {
        op: LogicOp::And,
        left: Box::new(forward),
        right: Box::new(backward),
    })
}

/// Parse and lower the two raw operand sub-streams of a binary connective marker
/// (`__trust_vc_implies!`, `__trust_vc_iff!`). Each operand is re-parsed through
/// the chain-aware parser so nested connectives and comparison chains normalize
/// identically to the top level. `label` is used in diagnostics.
fn lower_binary_marker_operands(
    mac: &syn::ExprMacro,
    env: &TypeEnv,
    depth: usize,
    label: &str,
) -> Result<(TrustVcExpr, TrustVcExpr), LoweringError> {
    let operands =
        crate::chained_comparisons::split_top_level_comma_operands(mac.mac.tokens.clone());
    let [left_tokens, right_tokens] = match <[_; 2]>::try_from(operands) {
        Ok(pair) => pair,
        Err(operands) => {
            return Err(LoweringError::UnsupportedExpr(format!(
                "logical {} lowers to exactly two operands, got {}",
                label,
                operands.len()
            )));
        }
    };

    let left_expr = crate::chained_comparisons::parse_expr_tokens_with_chains(left_tokens)
        .map_err(|err| {
            LoweringError::UnsupportedExpr(format!("{} left operand: {}", label, err))
        })?;
    let right_expr = crate::chained_comparisons::parse_expr_tokens_with_chains(right_tokens)
        .map_err(|err| {
            LoweringError::UnsupportedExpr(format!("{} right operand: {}", label, err))
        })?;

    let left = lower_syn_expr_with_depth(&left_expr, env, depth)?;
    let right = lower_syn_expr_with_depth(&right_expr, env, depth)?;
    Ok((left, right))
}

enum SeqMacroInput {
    Elements(Vec<syn::Expr>),
    Repeat {
        value: Box<syn::Expr>,
        len: syn::LitInt,
    },
}

struct MapMacroInput(Vec<(syn::Expr, syn::Expr)>);

struct SetMacroInput(Vec<syn::Expr>);

impl Parse for SeqMacroInput {
    fn parse(input: ParseStream<'_>) -> syn::Result<Self> {
        if input.is_empty() {
            return Ok(Self::Elements(Vec::new()));
        }

        let first: syn::Expr = input.parse()?;
        if input.peek(syn::Token![;]) {
            input.parse::<syn::Token![;]>()?;
            let len: syn::LitInt = input.parse()?;
            if !input.is_empty() {
                return Err(input.error("seq![value; len] does not accept trailing tokens"));
            }
            return Ok(Self::Repeat {
                value: Box::new(first),
                len,
            });
        }

        let mut elements = vec![first];
        while input.peek(syn::Token![,]) {
            input.parse::<syn::Token![,]>()?;
            if input.is_empty() {
                break;
            }
            elements.push(input.parse()?);
        }
        if !input.is_empty() {
            return Err(input.error("malformed seq! literal"));
        }
        Ok(Self::Elements(elements))
    }
}

impl Parse for MapMacroInput {
    fn parse(input: ParseStream<'_>) -> syn::Result<Self> {
        let mut entries = Vec::new();
        while !input.is_empty() {
            let key: syn::Expr = input.parse()?;
            input.parse::<syn::Token![=>]>()?;
            let value: syn::Expr = input.parse()?;
            entries.push((key, value));

            if input.peek(syn::Token![,]) {
                input.parse::<syn::Token![,]>()?;
            } else {
                break;
            }
        }
        if !input.is_empty() {
            return Err(input.error("malformed map! literal"));
        }
        Ok(Self(entries))
    }
}

impl Parse for SetMacroInput {
    fn parse(input: ParseStream<'_>) -> syn::Result<Self> {
        let elements =
            syn::punctuated::Punctuated::<syn::Expr, syn::Token![,]>::parse_terminated(input)?;
        Ok(Self(elements.into_iter().collect()))
    }
}

fn lower_seq_macro(
    mac: &syn::ExprMacro,
    env: &TypeEnv,
    depth: usize,
) -> Result<TrustVcExpr, LoweringError> {
    let input: SeqMacroInput = syn::parse2(mac.mac.tokens.clone()).map_err(|err| {
        LoweringError::UnsupportedExpr(format!("malformed seq! literal: {}", err))
    })?;

    let elements = match input {
        SeqMacroInput::Elements(elements) => {
            if elements.is_empty() {
                return Err(LoweringError::TypeInference(
                    "seq![] requires an element type; use Seq::<T>::empty()".to_string(),
                ));
            }
            elements
                .iter()
                .map(|element| lower_syn_expr_with_depth(element, env, depth))
                .collect::<Result<Vec<_>, _>>()?
        }
        SeqMacroInput::Repeat { value, len } => {
            let repeat_len = len.base10_parse::<usize>().map_err(|err| {
                LoweringError::UnsupportedExpr(format!(
                    "seq![value; len] requires a usize literal length: {}",
                    err
                ))
            })?;
            if repeat_len > SEQ_LITERAL_REPEAT_LIMIT {
                return Err(LoweringError::UnsupportedExpr(format!(
                    "seq![value; len] supports literal lengths up to {SEQ_LITERAL_REPEAT_LIMIT}, got {repeat_len}",
                )));
            }
            let lowered = lower_syn_expr_with_depth(&value, env, depth)?;
            vec![lowered; repeat_len]
        }
    };

    lower_seq_literal_values(elements, "seq")
}

fn lower_vec_macro(
    mac: &syn::ExprMacro,
    env: &TypeEnv,
    depth: usize,
) -> Result<TrustVcExpr, LoweringError> {
    let input: SeqMacroInput = syn::parse2(mac.mac.tokens.clone()).map_err(|err| {
        LoweringError::UnsupportedExpr(format!("malformed vec! literal: {}", err))
    })?;

    let elements =
        match input {
            SeqMacroInput::Elements(elements) if !elements.is_empty() => elements
                .iter()
                .map(|element| lower_syn_expr_with_depth(element, env, depth))
                .collect::<Result<Vec<_>, _>>()?,
            SeqMacroInput::Elements(_) => return Err(LoweringError::TypeInference(
                "vec![] requires an element type; empty Vec literals are not modeled in this slice"
                    .to_string(),
            )),
            SeqMacroInput::Repeat { .. } => {
                return Err(LoweringError::UnsupportedExpr(
                    "vec![value; len] repeat literals are not modeled in this slice".to_string(),
                ))
            }
        };

    lower_seq_literal_values(elements, "vec")
}

fn lower_seq_literal_values(
    elements: Vec<TrustVcExpr>,
    macro_name: &str,
) -> Result<TrustVcExpr, LoweringError> {
    let Some(first) = elements.first() else {
        return Err(LoweringError::TypeInference(format!(
            "{macro_name}![] requires an element type; use Seq::<T>::empty()"
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
                "{macro_name}! element type mismatch: expected '{}', got '{}'",
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

fn lower_map_macro(
    mac: &syn::ExprMacro,
    env: &TypeEnv,
    depth: usize,
) -> Result<TrustVcExpr, LoweringError> {
    let MapMacroInput(entries) = syn::parse2(mac.mac.tokens.clone()).map_err(|err| {
        LoweringError::UnsupportedExpr(format!("malformed map! literal: {}", err))
    })?;
    if entries.is_empty() {
        return Err(LoweringError::TypeInference(
            "map![] requires key/value types; use Map::<K, V>::empty()".to_string(),
        ));
    }

    let lowered_entries = entries
        .iter()
        .map(|(key, value)| {
            Ok((
                lower_syn_expr_with_depth(key, env, depth)?,
                lower_syn_expr_with_depth(value, env, depth)?,
            ))
        })
        .collect::<Result<Vec<_>, LoweringError>>()?;

    let (first_key, first_value) = lowered_entries.first().ok_or_else(|| {
        LoweringError::TypeInference(
            "map![] requires key/value types; use Map::<K, V>::empty()".to_string(),
        )
    })?;
    let key_ty = infer_expr_type(first_key);
    let value_ty = infer_expr_type(first_value);
    let map_ty = TrustVcType::Map(Box::new(key_ty.clone()), Box::new(value_ty.clone()));
    let empty_name = map_literal_empty_constructor_name(&key_ty, &value_ty);
    let mut map = TrustVcExpr::FnCall {
        name: empty_name.clone(),
        args: vec![],
        return_ty: map_ty.clone(),
    };

    for (key, value) in lowered_entries {
        let key = coerce_unsuffixed_literal(key, &key_ty);
        let value = coerce_unsuffixed_literal(value, &value_ty);
        let actual_key_ty = infer_expr_type(&key);
        let actual_value_ty = infer_expr_type(&value);
        if actual_key_ty != key_ty {
            return Err(LoweringError::TypeInference(format!(
                "map! key type mismatch: expected '{}', got '{}'",
                key_ty.to_type_string(),
                actual_key_ty.to_type_string()
            )));
        }
        if actual_value_ty != value_ty {
            return Err(LoweringError::TypeInference(format!(
                "map! value type mismatch: expected '{}', got '{}'",
                value_ty.to_type_string(),
                actual_value_ty.to_type_string()
            )));
        }

        map = TrustVcExpr::CollectionOp {
            op: CollectionOp::Insert,
            receiver: Box::new(map),
            receiver_name: Some(empty_name.clone()),
            args: vec![key, value],
            ty: map_ty.clone(),
        };
    }

    Ok(map)
}

fn lower_set_macro(
    mac: &syn::ExprMacro,
    env: &TypeEnv,
    depth: usize,
) -> Result<TrustVcExpr, LoweringError> {
    let SetMacroInput(elements) = syn::parse2(mac.mac.tokens.clone()).map_err(|err| {
        LoweringError::UnsupportedExpr(format!("malformed set! literal: {}", err))
    })?;
    if elements.is_empty() {
        return Err(LoweringError::TypeInference(
            "set![] requires an element type; use Set::<T>::empty()".to_string(),
        ));
    }

    let lowered_elements = elements
        .iter()
        .map(|element| lower_syn_expr_with_depth(element, env, depth))
        .collect::<Result<Vec<_>, _>>()?;

    let first = lowered_elements.first().ok_or_else(|| {
        LoweringError::TypeInference(
            "set![] requires an element type; use Set::<T>::empty()".to_string(),
        )
    })?;
    let elem_ty = infer_expr_type(first);
    let set_ty = TrustVcType::Set(Box::new(elem_ty.clone()));
    let empty_name = set_literal_empty_constructor_name(&elem_ty);
    let mut set = TrustVcExpr::FnCall {
        name: empty_name.clone(),
        args: vec![],
        return_ty: set_ty.clone(),
    };

    for element in lowered_elements {
        let element = coerce_unsuffixed_literal(element, &elem_ty);
        let element_ty = infer_expr_type(&element);
        if element_ty != elem_ty {
            return Err(LoweringError::TypeInference(format!(
                "set! element type mismatch: expected '{}', got '{}'",
                elem_ty.to_type_string(),
                element_ty.to_type_string()
            )));
        }

        set = TrustVcExpr::CollectionOp {
            op: CollectionOp::Insert,
            receiver: Box::new(set),
            receiver_name: Some(empty_name.clone()),
            args: vec![element],
            ty: set_ty.clone(),
        };
    }

    Ok(set)
}

fn seq_literal_empty_constructor_name(elem_ty: &TrustVcType) -> String {
    format!(
        "{COLLECTION_CONSTRUCTOR_PREFIX}Seq_{}_empty",
        collection_literal_type_component(elem_ty)
    )
}

fn set_literal_empty_constructor_name(elem_ty: &TrustVcType) -> String {
    format!(
        "{COLLECTION_CONSTRUCTOR_PREFIX}Set_{}_empty",
        collection_literal_type_component(elem_ty)
    )
}

fn map_literal_empty_constructor_name(key_ty: &TrustVcType, value_ty: &TrustVcType) -> String {
    format!(
        "{COLLECTION_CONSTRUCTOR_PREFIX}Map_{}_{}_empty",
        collection_literal_type_component(key_ty),
        collection_literal_type_component(value_ty)
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

pub(super) fn lower_choose(
    call: &syn::ExprCall,
    env: &TypeEnv,
    depth: usize,
) -> Result<TrustVcExpr, LoweringError> {
    if call.args.len() != 1 {
        return Err(LoweringError::UnsupportedExpr(format!(
            "choose expects 1 closure arg, got {}",
            call.args.len()
        )));
    }
    let arg = call.args.first().ok_or_else(|| {
        LoweringError::UnsupportedExpr(format!(
            "choose expects 1 closure arg, got {}",
            call.args.len()
        ))
    })?;
    match arg {
        syn::Expr::Closure(closure) => lower_choose_closure(closure, env, depth),
        _ => Err(LoweringError::UnsupportedExpr(
            "choose arg must be closure".into(),
        )),
    }
}

pub(super) fn lower_quantifier(
    kind: QuantifierKind,
    call: &syn::ExprCall,
    env: &TypeEnv,
    depth: usize,
) -> Result<TrustVcExpr, LoweringError> {
    if call.args.len() != 1 {
        return Err(LoweringError::UnsupportedExpr(format!(
            "quantifier expects 1 closure arg, got {}",
            call.args.len()
        )));
    }
    let arg = call.args.first().ok_or_else(|| {
        LoweringError::UnsupportedExpr(format!(
            "quantifier expects 1 closure arg, got {}",
            call.args.len()
        ))
    })?;
    match arg {
        syn::Expr::Closure(closure) => {
            let bound_vars = extract_closure_params(closure, env)?;
            if bound_vars.is_empty() {
                return Err(LoweringError::UnsupportedExpr(
                    "quantifier requires at least one bound variable; \
                     use |x: Type| instead of ||"
                        .into(),
                ));
            }
            let child_env = env.extend(&bound_vars);
            let triggers = lower_quantifier_triggers(&closure.body, &child_env, depth)?;
            let body = Box::new(lower_syn_expr_with_depth(&closure.body, &child_env, depth)?);
            Ok(TrustVcExpr::Quantifier {
                kind,
                bound_vars,
                body,
                triggers,
                trigger_inference_mode: crate::broadcast_state::get_trigger_inference_mode(),
            })
        }
        _ => Err(LoweringError::UnsupportedExpr(
            "quantifier arg must be closure".into(),
        )),
    }
}

fn lower_quantifier_triggers(
    body: &syn::Expr,
    env: &TypeEnv,
    depth: usize,
) -> Result<Option<Vec<Vec<TrustVcExpr>>>, LoweringError> {
    let mut trigger_exprs = Vec::new();
    collect_trigger_exprs(body, &mut trigger_exprs);
    if trigger_exprs.is_empty() {
        return Ok(None);
    }

    trigger_exprs
        .into_iter()
        .map(|expr| lower_syn_expr_with_depth(expr, env, depth).map(|trigger| vec![trigger]))
        .collect::<Result<Vec<_>, _>>()
        .map(Some)
}

fn collect_trigger_exprs<'a>(expr: &'a syn::Expr, out: &mut Vec<&'a syn::Expr>) {
    if expr_has_trigger_attr(expr) {
        out.push(expr);
        return;
    }

    match expr {
        syn::Expr::Binary(binary) => {
            collect_trigger_exprs(&binary.left, out);
            collect_trigger_exprs(&binary.right, out);
        }
        syn::Expr::Call(call) => {
            collect_trigger_exprs(&call.func, out);
            for arg in &call.args {
                collect_trigger_exprs(arg, out);
            }
        }
        syn::Expr::MethodCall(method) => {
            collect_trigger_exprs(&method.receiver, out);
            for arg in &method.args {
                collect_trigger_exprs(arg, out);
            }
        }
        syn::Expr::Paren(paren) => collect_trigger_exprs(&paren.expr, out),
        syn::Expr::Group(group) => collect_trigger_exprs(&group.expr, out),
        syn::Expr::Unary(unary) => collect_trigger_exprs(&unary.expr, out),
        syn::Expr::Reference(reference) => collect_trigger_exprs(&reference.expr, out),
        syn::Expr::Cast(cast) => collect_trigger_exprs(&cast.expr, out),
        syn::Expr::Index(index) => {
            collect_trigger_exprs(&index.expr, out);
            collect_trigger_exprs(&index.index, out);
        }
        syn::Expr::Field(field) => collect_trigger_exprs(&field.base, out),
        syn::Expr::Return(ret) => {
            if let Some(inner) = &ret.expr {
                collect_trigger_exprs(inner, out);
            }
        }
        _ => {}
    }
}

fn expr_has_trigger_attr(expr: &syn::Expr) -> bool {
    match expr {
        syn::Expr::Binary(binary) => attrs_have_trigger(&binary.attrs),
        syn::Expr::Call(call) => attrs_have_trigger(&call.attrs),
        syn::Expr::Cast(cast) => attrs_have_trigger(&cast.attrs),
        syn::Expr::Field(field) => attrs_have_trigger(&field.attrs),
        syn::Expr::Group(group) => attrs_have_trigger(&group.attrs),
        syn::Expr::Index(index) => attrs_have_trigger(&index.attrs),
        syn::Expr::Lit(lit) => attrs_have_trigger(&lit.attrs),
        syn::Expr::MethodCall(method) => attrs_have_trigger(&method.attrs),
        syn::Expr::Paren(paren) => attrs_have_trigger(&paren.attrs),
        syn::Expr::Path(path) => attrs_have_trigger(&path.attrs),
        syn::Expr::Reference(reference) => attrs_have_trigger(&reference.attrs),
        syn::Expr::Unary(unary) => attrs_have_trigger(&unary.attrs),
        _ => false,
    }
}

fn attrs_have_trigger(attrs: &[syn::Attribute]) -> bool {
    attrs.iter().any(|attr| {
        attr.path()
            .segments
            .last()
            .is_some_and(|segment| segment.ident == "trigger")
    })
}

/// A closed (variable-free) literal value, used to canonicalize `choose` closure
/// determinism keys.
#[derive(Clone, Copy)]
enum ClosedLit {
    Int(i128),
    Bool(bool),
}

/// Evaluate an expression that mentions NO variables — only integer/bool
/// literals combined by closed arithmetic / comparison / boolean / unary
/// operators — to its value. Returns `None` for anything containing a
/// path/ident, an unsupported operator, or an arithmetic overflow / division by
/// zero; such subterms are simply left unfolded (a conservative
/// under-normalization, never an unsound over-normalization).
fn eval_closed_literal(expr: &syn::Expr) -> Option<ClosedLit> {
    match expr {
        syn::Expr::Lit(lit) => match &lit.lit {
            syn::Lit::Int(i) => i.base10_parse::<i128>().ok().map(ClosedLit::Int),
            syn::Lit::Bool(b) => Some(ClosedLit::Bool(b.value)),
            _ => None,
        },
        syn::Expr::Paren(p) => eval_closed_literal(&p.expr),
        syn::Expr::Group(g) => eval_closed_literal(&g.expr),
        syn::Expr::Unary(u) => {
            let v = eval_closed_literal(&u.expr)?;
            match (&u.op, v) {
                (syn::UnOp::Not(_), ClosedLit::Bool(b)) => Some(ClosedLit::Bool(!b)),
                (syn::UnOp::Neg(_), ClosedLit::Int(i)) => i.checked_neg().map(ClosedLit::Int),
                _ => None,
            }
        }
        syn::Expr::Binary(b) => {
            let l = eval_closed_literal(&b.left)?;
            let r = eval_closed_literal(&b.right)?;
            match (l, r) {
                (ClosedLit::Int(x), ClosedLit::Int(y)) => match &b.op {
                    syn::BinOp::Add(_) => x.checked_add(y).map(ClosedLit::Int),
                    syn::BinOp::Sub(_) => x.checked_sub(y).map(ClosedLit::Int),
                    syn::BinOp::Mul(_) => x.checked_mul(y).map(ClosedLit::Int),
                    syn::BinOp::Div(_) => x.checked_div(y).map(ClosedLit::Int),
                    syn::BinOp::Rem(_) => x.checked_rem(y).map(ClosedLit::Int),
                    syn::BinOp::Eq(_) => Some(ClosedLit::Bool(x == y)),
                    syn::BinOp::Ne(_) => Some(ClosedLit::Bool(x != y)),
                    syn::BinOp::Lt(_) => Some(ClosedLit::Bool(x < y)),
                    syn::BinOp::Le(_) => Some(ClosedLit::Bool(x <= y)),
                    syn::BinOp::Gt(_) => Some(ClosedLit::Bool(x > y)),
                    syn::BinOp::Ge(_) => Some(ClosedLit::Bool(x >= y)),
                    _ => None,
                },
                (ClosedLit::Bool(x), ClosedLit::Bool(y)) => match &b.op {
                    syn::BinOp::And(_) => Some(ClosedLit::Bool(x && y)),
                    syn::BinOp::Or(_) => Some(ClosedLit::Bool(x || y)),
                    syn::BinOp::Eq(_) => Some(ClosedLit::Bool(x == y)),
                    syn::BinOp::Ne(_) => Some(ClosedLit::Bool(x != y)),
                    _ => None,
                },
                _ => None,
            }
        }
        _ => None,
    }
}

fn closed_lit_to_expr(v: ClosedLit) -> syn::Expr {
    match v {
        ClosedLit::Int(i) => {
            syn::parse_str(&i.to_string()).unwrap_or_else(|_| syn::parse_quote!(0))
        }
        ClosedLit::Bool(true) => syn::parse_quote!(true),
        ClosedLit::Bool(false) => syn::parse_quote!(false),
    }
}

/// Fold every closed (variable-free) SUBexpression of `expr` to its literal
/// value while PRESERVING the surrounding structure — no commuting operands, no
/// simplifying `x && true` to `x`. Only used to canonicalize `choose`
/// determinism keys.
fn fold_closed_literals(expr: &syn::Expr) -> syn::Expr {
    if let Some(v) = eval_closed_literal(expr) {
        return closed_lit_to_expr(v);
    }
    match expr {
        syn::Expr::Binary(b) => {
            let mut b = b.clone();
            b.left = Box::new(fold_closed_literals(&b.left));
            b.right = Box::new(fold_closed_literals(&b.right));
            syn::Expr::Binary(b)
        }
        syn::Expr::Unary(u) => {
            let mut u = u.clone();
            u.expr = Box::new(fold_closed_literals(&u.expr));
            syn::Expr::Unary(u)
        }
        syn::Expr::Paren(p) => {
            let mut p = p.clone();
            p.expr = Box::new(fold_closed_literals(&p.expr));
            syn::Expr::Paren(p)
        }
        syn::Expr::Group(g) => {
            let mut g = g.clone();
            g.expr = Box::new(fold_closed_literals(&g.expr));
            syn::Expr::Group(g)
        }
        syn::Expr::Call(c) => {
            let mut c = c.clone();
            c.args = c.args.iter().map(fold_closed_literals).collect();
            syn::Expr::Call(c)
        }
        syn::Expr::MethodCall(m) => {
            let mut m = m.clone();
            m.receiver = Box::new(fold_closed_literals(&m.receiver));
            m.args = m.args.iter().map(fold_closed_literals).collect();
            syn::Expr::MethodCall(m)
        }
        _ => expr.clone(),
    }
}

/// Canonical determinism key for a `choose` closure. Two `choose` expressions
/// receive the SAME Skolem witness iff they share this key, so it must match
/// Verus's own predicate identity: closed (constant) subterms are folded to
/// their values (`|i| f(i) && (1+1==2)` and `|i| f(i) && (2+2==4)` both become
/// `|i| f(i) && true`, so `test_choose_eq`'s `i1 == i2` verifies — Verus proves
/// it), but the boolean STRUCTURE is preserved so the REORDERED
/// `|i| (2+2==4) && f(i)` (→ `|i| true && f(i)`) keeps a DISTINCT key and
/// `test1_fails3` stays refuted — trust-vc must not prove more than Verus.
fn choose_closure_key(closure: &syn::ExprClosure) -> String {
    let mut normalized = closure.clone();
    normalized.body = Box::new(fold_closed_literals(&closure.body));
    quote::quote!(#normalized).to_string()
}

fn lower_choose_closure(
    closure: &syn::ExprClosure,
    env: &TypeEnv,
    depth: usize,
) -> Result<TrustVcExpr, LoweringError> {
    let params = extract_choose_params(closure, env)?;
    match params.len() {
        0 => Err(LoweringError::UnsupportedExpr(
            "choose requires at least one bound variable".into(),
        )),
        1 => lower_single_binder_choose_closure(closure, env, depth, params),
        _ => lower_multi_binder_choose_closure(closure, env, depth, params),
    }
}

fn lower_single_binder_choose_closure(
    closure: &syn::ExprClosure,
    env: &TypeEnv,
    depth: usize,
    params: Vec<(String, TrustVcType)>,
) -> Result<TrustVcExpr, LoweringError> {
    let mut params = params.into_iter();
    let (var_name, var_ty) = params.next().ok_or_else(|| {
        LoweringError::UnsupportedExpr("choose requires exactly one bound variable".into())
    })?;
    let child_env = env.extend(&[(var_name.clone(), var_ty.clone())]);
    let condition = Box::new(lower_syn_expr_with_depth(&closure.body, &child_env, depth)?);
    let key = choose_closure_key(closure);

    // PATH-B mirror (single-binder analog of `lower_multi_binder_choose_closure`).
    // If the predicate mentions a function call (a spec-fn / opaque application),
    // reproduce the multi-binder shape that yields a validated-Sat counterexample
    // for a WITNESSLESS spec-fn choose: a TRIVIAL plain guarded axiom
    // (`condition = true`, so the encoder emits `forall x. true => true`) plus a
    // SEPARATE combined Hilbert axiom `forall x. f(x) => f(chosen)`. The encoder
    // marks that combined axiom `no_mbqi` (it mentions a fn call), so it fires
    // ONLY on a genuine ground witness (an asserted `f(7)` or a pre-`choose`
    // assumed `exists` Skolemized to fresh consts) — MBQI/CEGQI cannot FABRICATE
    // one. With no witness present the combined axiom is never instantiated and
    // the finalize validates a model with the chosen skolem FREE (`¬f(chosen)`),
    // which the `restored_has_no_mbqi_forall` acceptance maps to a counterexample.
    // A purely DECIDABLE arithmetic predicate (no fn call) keeps the plain
    // real-condition path (`also_assert: None`) so it still verifies via
    // arithmetic; marking it would fail-close a legitimate case.
    if crate::ir_expr_traversal::expr_mentions_fncall(&condition) {
        let chosen = TrustVcExpr::Choose {
            var_name: var_name.clone(),
            var_ty: var_ty.clone(),
            condition: Box::new(TrustVcExpr::BoolLit(true)),
            key: key.clone(),
            also_assert: None,
        };
        let mut chosen_by_name = HashMap::new();
        chosen_by_name.insert(var_name.clone(), chosen);
        let combined_conclusion = substitute_unbound_vars((*condition).clone(), &chosen_by_name);
        let combined_axiom = TrustVcExpr::Quantifier {
            kind: QuantifierKind::Forall,
            bound_vars: vec![(var_name.clone(), var_ty.clone())],
            body: Box::new(TrustVcExpr::Implies {
                premise: condition,
                conclusion: Box::new(combined_conclusion),
            }),
            triggers: None,
            trigger_inference_mode: None,
        };
        return Ok(TrustVcExpr::Choose {
            var_name,
            var_ty,
            condition: Box::new(TrustVcExpr::BoolLit(true)),
            key,
            also_assert: Some(Box::new(combined_axiom)),
        });
    }

    Ok(TrustVcExpr::Choose {
        var_name,
        var_ty,
        condition,
        key,
        also_assert: None,
    })
}

fn lower_multi_binder_choose_closure(
    closure: &syn::ExprClosure,
    env: &TypeEnv,
    depth: usize,
    params: Vec<(String, TrustVcType)>,
) -> Result<TrustVcExpr, LoweringError> {
    let child_env = env.extend(&params);
    let condition = lower_syn_expr_with_depth(&closure.body, &child_env, depth)?;
    let tuple_ty = tuple_datatype_type(params.iter().map(|(_, ty)| ty.clone()).collect());
    let TrustVcType::Datatype { name, .. } = &tuple_ty else {
        unreachable!("tuple_datatype_type always returns a datatype for multi-binder choose");
    };

    let key = choose_closure_key(closure);

    // Trigger-gate on whether the predicate mentions a function call (an OPAQUE /
    // spec-fn application). A predicate over a spec-fn `P` cannot be discharged
    // by the nested-`exists` per-field trigger (its natural trigger binds the
    // inner existential) and, worse, would let MBQI *fabricate* a witness — a
    // false-verify when no ground witness exists. So a spec-fn predicate takes
    // the `no_mbqi` combined-axiom path (trivial per-field conditions + the
    // combined Hilbert axiom marked `no_mbqi` at encode time, so it fires ONLY
    // on a genuine ground witness). A purely DECIDABLE arithmetic predicate
    // (e.g. `i <= j`) keeps the OLD nested-`exists` path unchanged — it verifies
    // via arithmetic and marking it would fail-close a legitimate case.
    let trigger_gated = crate::ir_expr_traversal::expr_mentions_fncall(&condition);

    let mut chosen_by_name = HashMap::new();
    let mut tuple_args = Vec::with_capacity(params.len());
    for (index, (var_name, var_ty)) in params.iter().enumerate() {
        let field_condition = if trigger_gated {
            // The combined `no_mbqi` axiom carries the joint constraint; each
            // field's own Skolem-witness axiom is left trivial.
            TrustVcExpr::BoolLit(true)
        } else {
            let mut fc = substitute_unbound_vars(condition.clone(), &chosen_by_name);
            let remaining = params[index + 1..].to_vec();
            if !remaining.is_empty() {
                fc = TrustVcExpr::Quantifier {
                    kind: QuantifierKind::Exists,
                    bound_vars: remaining,
                    body: Box::new(fc),
                    triggers: None,
                    trigger_inference_mode: None,
                };
            }
            fc
        };

        let chosen = TrustVcExpr::Choose {
            var_name: var_name.clone(),
            var_ty: var_ty.clone(),
            condition: Box::new(field_condition),
            key: format!("{key}::__tuple_field_{index}"),
            also_assert: None,
        };
        chosen_by_name.insert(var_name.clone(), chosen.clone());
        tuple_args.push(chosen);
    }

    // The derivable combined axiom `forall <params>. P(<params>) ==> P(chosen_0,
    // chosen_1, ..)` is a theorem of the per-field Skolem axioms (sound — if any
    // tuple satisfies `P`, the jointly-chosen one does). Its scalar `P(<params>)`
    // trigger matches a surrounding ground witness `P(..)` (an asserted witness
    // or a `choose`-preceding assumed `exists` Skolemized to fresh consts),
    // closing the spec-fn gap (choose.rs `test1_tuple`, regression_1183).
    let combined_conclusion = substitute_unbound_vars(condition.clone(), &chosen_by_name);
    let combined_axiom = TrustVcExpr::Quantifier {
        kind: QuantifierKind::Forall,
        bound_vars: params.clone(),
        body: Box::new(TrustVcExpr::Implies {
            premise: Box::new(condition.clone()),
            conclusion: Box::new(combined_conclusion.clone()),
        }),
        triggers: None,
        trigger_inference_mode: None,
    };
    if trigger_gated {
        // Attach the combined axiom to EVERY field: each verification obligation
        // encodes ONLY the tuple fields it references (an `assert(t.0 >= 10)`
        // reaches field 0 only), so an axiom parked on a single field would be
        // invisible to an obligation over a different field. The encoder marks it
        // `no_mbqi` (it mentions a fn call), so a witnessless choose fails closed
        // rather than MBQI-fabricating a witness. Re-asserting the hash-consed
        // axiom per field is idempotent.
        for arg in tuple_args.iter_mut() {
            if let TrustVcExpr::Choose { also_assert, .. } = arg {
                *also_assert = Some(Box::new(combined_axiom.clone()));
            }
        }
    } else if let Some(TrustVcExpr::Choose { also_assert, .. }) = tuple_args.last_mut() {
        // Decidable arithmetic predicate: retain the universal Hilbert axiom,
        // and add bounded, GROUND instances at deterministic small witnesses.
        // ay's CEGQI can miss even `exists i,j. i < j`; each ground implication
        // here is just a valid universal instance `P(w) ==> P(chosen)`, never an
        // unconditional witness claim. Thus an unsatisfiable predicate leaves
        // every antecedent false, while an inhabited small arithmetic relation
        // avoids depending on incomplete quantifier search.
        let mut instances = vec![combined_axiom];
        for witness in small_integer_witness_assignments(&params) {
            let premise = substitute_unbound_vars(condition.clone(), &witness);
            instances.push(TrustVcExpr::Implies {
                premise: Box::new(premise),
                conclusion: Box::new(combined_conclusion.clone()),
            });
        }
        *also_assert = balanced_conjunction(instances).map(Box::new);
    }

    Ok(TrustVcExpr::FnCall {
        name: crate::encoder::datatype::variant_symbol_name(name, TUPLE_VARIANT_NAME),
        args: tuple_args,
        return_ty: tuple_ty,
    })
}

/// Build a logarithmic-depth conjunction, avoiding a new expression-depth cliff
/// when the full 27-instance basis is available.
fn balanced_conjunction(mut exprs: Vec<TrustVcExpr>) -> Option<TrustVcExpr> {
    while exprs.len() > 1 {
        let mut next = Vec::with_capacity(exprs.len().div_ceil(2));
        let mut iter = exprs.into_iter();
        while let Some(left) = iter.next() {
            if let Some(right) = iter.next() {
                next.push(TrustVcExpr::Logic {
                    op: LogicOp::And,
                    left: Box::new(left),
                    right: Box::new(right),
                });
            } else {
                next.push(left);
            }
        }
        exprs = next;
    }
    exprs.pop()
}

/// Enumerate a deliberately tiny Cartesian witness basis for arithmetic
/// multi-binder choice. The cap is structural (at most 3^3 = 27 assignments),
/// and unsupported or higher-arity types simply retain the universal axiom.
fn small_integer_witness_assignments(
    params: &[(String, TrustVcType)],
) -> Vec<HashMap<String, TrustVcExpr>> {
    const MAX_ARITY: usize = 3;
    if params.is_empty() || params.len() > MAX_ARITY {
        return Vec::new();
    }

    let mut assignments = vec![HashMap::new()];
    for (name, ty) in params {
        let values: &[i128] = match ty {
            TrustVcType::MathInt | TrustVcType::Int { .. } => &[-1, 0, 1],
            TrustVcType::Nat | TrustVcType::Uint { .. } => &[0, 1],
            _ => return Vec::new(),
        };
        let mut next = Vec::with_capacity(assignments.len() * values.len());
        for assignment in assignments {
            for value in values {
                let mut extended = assignment.clone();
                extended.insert(
                    name.clone(),
                    TrustVcExpr::IntLit {
                        value: *value,
                        ty: ty.clone(),
                    },
                );
                next.push(extended);
            }
        }
        assignments = next;
    }
    assignments
}

#[cfg(test)]
mod small_integer_witness_tests {
    use super::*;

    #[test]
    fn signed_basis_is_cartesian_and_type_correct() {
        let params = vec![
            ("i".to_string(), TrustVcType::MathInt),
            ("j".to_string(), TrustVcType::Int { width: 16 }),
        ];
        let assignments = small_integer_witness_assignments(&params);
        assert_eq!(assignments.len(), 9);
        for assignment in assignments {
            for (name, expected_ty) in &params {
                match assignment.get(name) {
                    Some(TrustVcExpr::IntLit { value, ty }) => {
                        assert!([-1, 0, 1].contains(value));
                        assert_eq!(ty, expected_ty);
                    }
                    other => panic!("expected typed integer witness for {name}, got {other:?}"),
                }
            }
        }
    }

    #[test]
    fn unsigned_basis_is_nonnegative() {
        let params = vec![
            ("n".to_string(), TrustVcType::Nat),
            ("u".to_string(), TrustVcType::Uint { width: 8 }),
        ];
        let assignments = small_integer_witness_assignments(&params);
        assert_eq!(assignments.len(), 4);
        assert!(assignments.iter().all(|assignment| {
            assignment
                .values()
                .all(|expr| matches!(expr, TrustVcExpr::IntLit { value: 0 | 1, .. }))
        }));
    }

    #[test]
    fn arity_cap_and_unsupported_types_keep_universal_only() {
        let four = (0..4)
            .map(|index| (format!("v{index}"), TrustVcType::MathInt))
            .collect::<Vec<_>>();
        assert!(small_integer_witness_assignments(&four).is_empty());
        assert!(
            small_integer_witness_assignments(&[("b".to_string(), TrustVcType::Bool,)]).is_empty()
        );
    }

    #[test]
    fn conjunction_depth_is_logarithmic() {
        fn depth(expr: &TrustVcExpr) -> usize {
            match expr {
                TrustVcExpr::Logic {
                    op: LogicOp::And,
                    left,
                    right,
                } => 1 + depth(left).max(depth(right)),
                _ => 1,
            }
        }

        let exprs = (0..28).map(|_| TrustVcExpr::BoolLit(true)).collect();
        let conjunction = balanced_conjunction(exprs).expect("non-empty conjunction");
        assert_eq!(depth(&conjunction), 6);
    }
}

fn substitute_unbound_vars(
    expr: TrustVcExpr,
    replacements: &HashMap<String, TrustVcExpr>,
) -> TrustVcExpr {
    struct Folder<'a> {
        replacements: &'a HashMap<String, TrustVcExpr>,
    }

    impl crate::ir_expr_traversal::ScopeAwareTrustVcExprFolder for Folder<'_> {
        fn fold_expr_scoped(&mut self, expr: TrustVcExpr, bound: &HashSet<&str>) -> TrustVcExpr {
            match expr {
                TrustVcExpr::Var { name, ty } if !bound.contains(name.as_str()) => self
                    .replacements
                    .get(&name)
                    .cloned()
                    .unwrap_or(TrustVcExpr::Var { name, ty }),
                other => crate::ir_expr_traversal::fold_expr_scoped_children(self, other, bound),
            }
        }
    }

    let mut folder = Folder { replacements };
    folder.fold_expr_scoped(expr, &HashSet::new())
}

fn extract_choose_params(
    closure: &syn::ExprClosure,
    env: &TypeEnv,
) -> Result<Vec<(String, TrustVcType)>, LoweringError> {
    if closure.inputs.len() == 1 {
        if let Some(syn::Pat::Ident(pi)) = closure.inputs.first() {
            let name = pi.ident.to_string();
            let ty = infer_choose_binder_type(&name, &closure.body, env)?;
            reject_opaque_bound_type("choose", &name, &ty)?;
            return Ok(vec![(name, ty)]);
        }
    }

    extract_closure_params(closure, env)
}

fn infer_choose_binder_type(
    name: &str,
    body: &syn::Expr,
    env: &TypeEnv,
) -> Result<TrustVcType, LoweringError> {
    let mut candidates = Vec::new();
    collect_choose_type_candidates(name, body, env, &mut candidates)?;
    let mut inferred: Option<TrustVcType> = None;
    for candidate in candidates {
        match &inferred {
            Some(existing) if existing != &candidate => {
                return Err(LoweringError::TypeInference(format!(
                    "conflicting inferred types for choose binder '{}': '{}' and '{}'",
                    name,
                    existing.to_type_string(),
                    candidate.to_type_string()
                )));
            }
            Some(_) => {}
            None => inferred = Some(candidate),
        }
    }

    inferred.ok_or_else(|| {
        LoweringError::InvalidType(format!(
            "closure parameter '{}' requires an explicit type annotation \
             (e.g., |{}: u32| ...). Untyped choose-bound variables can only \
             be inferred from a typed peer expression.",
            name, name,
        ))
    })
}

fn collect_choose_type_candidates(
    name: &str,
    expr: &syn::Expr,
    env: &TypeEnv,
    candidates: &mut Vec<TrustVcType>,
) -> Result<(), LoweringError> {
    match expr {
        syn::Expr::Binary(bin) => {
            let left_has = expr_contains_ident(&bin.left, name);
            let right_has = expr_contains_ident(&bin.right, name);
            match bin.op {
                syn::BinOp::Eq(_)
                | syn::BinOp::Ne(_)
                | syn::BinOp::Lt(_)
                | syn::BinOp::Le(_)
                | syn::BinOp::Gt(_)
                | syn::BinOp::Ge(_)
                | syn::BinOp::Add(_)
                | syn::BinOp::Sub(_)
                | syn::BinOp::Mul(_)
                | syn::BinOp::Div(_)
                | syn::BinOp::Rem(_)
                | syn::BinOp::BitAnd(_)
                | syn::BinOp::BitOr(_)
                | syn::BinOp::BitXor(_)
                | syn::BinOp::Shl(_)
                | syn::BinOp::Shr(_) => {
                    if left_has && !right_has {
                        push_peer_type(&bin.right, env, candidates)?;
                    }
                    if right_has && !left_has {
                        push_peer_type(&bin.left, env, candidates)?;
                    }
                }
                _ => {}
            }
            collect_choose_type_candidates(name, &bin.left, env, candidates)?;
            collect_choose_type_candidates(name, &bin.right, env, candidates)?;
        }
        syn::Expr::Cast(cast) => {
            if expr_contains_ident(&cast.expr, name) {
                candidates.push(env.resolve_syn_type(&cast.ty)?);
            }
            collect_choose_type_candidates(name, &cast.expr, env, candidates)?;
        }
        syn::Expr::Call(call) => {
            if let syn::Expr::Path(path) = &*call.func {
                let fn_name = crate::ir_lowering::expr_path_to_string(path);
                if let Some(param_types) = env.lookup_fn_params(&fn_name) {
                    for (arg, param_ty) in call.args.iter().zip(param_types.iter()) {
                        if expr_contains_ident(arg, name) {
                            candidates.push(param_ty.clone());
                        }
                    }
                }
            }
            collect_choose_type_candidates(name, &call.func, env, candidates)?;
            for arg in &call.args {
                collect_choose_type_candidates(name, arg, env, candidates)?;
            }
        }
        syn::Expr::MethodCall(method) => {
            collect_choose_type_candidates(name, &method.receiver, env, candidates)?;
            for arg in &method.args {
                collect_choose_type_candidates(name, arg, env, candidates)?;
            }
        }
        syn::Expr::Unary(unary) => {
            collect_choose_type_candidates(name, &unary.expr, env, candidates)?;
        }
        syn::Expr::Paren(paren) => {
            collect_choose_type_candidates(name, &paren.expr, env, candidates)?;
        }
        syn::Expr::Group(group) => {
            collect_choose_type_candidates(name, &group.expr, env, candidates)?;
        }
        syn::Expr::Reference(reference) => {
            collect_choose_type_candidates(name, &reference.expr, env, candidates)?;
        }
        syn::Expr::Index(index) => {
            collect_choose_type_candidates(name, &index.expr, env, candidates)?;
            collect_choose_type_candidates(name, &index.index, env, candidates)?;
        }
        syn::Expr::Field(field) => {
            collect_choose_type_candidates(name, &field.base, env, candidates)?;
        }
        syn::Expr::Tuple(tuple) => {
            for elem in &tuple.elems {
                collect_choose_type_candidates(name, elem, env, candidates)?;
            }
        }
        _ => {}
    }
    Ok(())
}

fn push_peer_type(
    expr: &syn::Expr,
    env: &TypeEnv,
    candidates: &mut Vec<TrustVcType>,
) -> Result<(), LoweringError> {
    if let Some(ty) = infer_typed_peer_expr(expr, env)? {
        candidates.push(ty);
    }
    Ok(())
}

fn infer_typed_peer_expr(
    expr: &syn::Expr,
    env: &TypeEnv,
) -> Result<Option<TrustVcType>, LoweringError> {
    match expr {
        syn::Expr::Lit(lit) => match &lit.lit {
            syn::Lit::Bool(_) => Ok(Some(TrustVcType::Bool)),
            syn::Lit::Char(_) => Ok(Some(TrustVcType::Char)),
            syn::Lit::Int(int_lit) if !int_lit.suffix().is_empty() => {
                Ok(Some(type_from_int_suffix(int_lit.suffix())?))
            }
            syn::Lit::Int(_) => Ok(None),
            _ => Ok(None),
        },
        syn::Expr::Path(path) => infer_typed_peer_path(path, env),
        syn::Expr::Cast(cast) => Ok(Some(env.resolve_syn_type(&cast.ty)?)),
        syn::Expr::Unary(unary) => {
            if matches!(unary.op, syn::UnOp::Not(_)) {
                Ok(Some(TrustVcType::Bool))
            } else {
                infer_typed_peer_expr(&unary.expr, env)
            }
        }
        syn::Expr::Paren(paren) => infer_typed_peer_expr(&paren.expr, env),
        syn::Expr::Group(group) => infer_typed_peer_expr(&group.expr, env),
        syn::Expr::Reference(reference) => infer_typed_peer_expr(&reference.expr, env),
        syn::Expr::Binary(bin) if binary_returns_bool(&bin.op) => Ok(Some(TrustVcType::Bool)),
        syn::Expr::Binary(bin) => merge_inferred_peer_types(
            infer_typed_peer_expr(&bin.left, env)?,
            infer_typed_peer_expr(&bin.right, env)?,
        ),
        syn::Expr::Tuple(tuple) if tuple.elems.is_empty() => Ok(Some(TrustVcType::Unit)),
        syn::Expr::Tuple(tuple) => {
            let mut elem_tys = Vec::with_capacity(tuple.elems.len());
            for elem in &tuple.elems {
                let Some(elem_ty) = infer_typed_peer_expr(elem, env)? else {
                    return Ok(None);
                };
                elem_tys.push(elem_ty);
            }
            Ok(Some(tuple_datatype_type(elem_tys)))
        }
        syn::Expr::Call(call) => {
            let syn::Expr::Path(path) = &*call.func else {
                return Ok(None);
            };
            let fn_name = crate::ir_lowering::expr_path_to_string(path);
            Ok(env.lookup_fn(&fn_name).cloned())
        }
        _ => Ok(None),
    }
}

fn binary_returns_bool(op: &syn::BinOp) -> bool {
    matches!(
        op,
        syn::BinOp::Eq(_)
            | syn::BinOp::Ne(_)
            | syn::BinOp::Lt(_)
            | syn::BinOp::Le(_)
            | syn::BinOp::Gt(_)
            | syn::BinOp::Ge(_)
            | syn::BinOp::And(_)
            | syn::BinOp::Or(_)
    )
}

fn infer_typed_peer_path(
    path: &syn::ExprPath,
    env: &TypeEnv,
) -> Result<Option<TrustVcType>, LoweringError> {
    if path.path.segments.len() == 1 {
        let name = path.path.segments[0].ident.to_string();
        return Ok(match name.as_str() {
            "true" | "false" => Some(TrustVcType::Bool),
            _ => env.lookup(&name).cloned(),
        });
    }
    if path.path.segments.len() == 2 {
        let type_name = path.path.segments[0].ident.to_string();
        let const_name = path.path.segments[1].ident.to_string();
        if matches!(const_name.as_str(), "MIN" | "MAX") {
            if let Ok(ty) = TrustVcType::try_from_str(&type_name) {
                return Ok(Some(ty));
            }
        }
    }
    Ok(None)
}

fn merge_inferred_peer_types(
    left: Option<TrustVcType>,
    right: Option<TrustVcType>,
) -> Result<Option<TrustVcType>, LoweringError> {
    match (left, right) {
        (Some(left), Some(right)) if left != right => Err(LoweringError::TypeInference(format!(
            "conflicting typed peer expression types '{}' and '{}'",
            left.to_type_string(),
            right.to_type_string()
        ))),
        (Some(ty), _) | (_, Some(ty)) => Ok(Some(ty)),
        (None, None) => Ok(None),
    }
}

fn expr_contains_ident(expr: &syn::Expr, name: &str) -> bool {
    match expr {
        syn::Expr::Path(path) if path.path.segments.len() == 1 => {
            path.path.segments[0].ident == name
        }
        syn::Expr::Binary(bin) => {
            expr_contains_ident(&bin.left, name) || expr_contains_ident(&bin.right, name)
        }
        syn::Expr::Unary(unary) => expr_contains_ident(&unary.expr, name),
        syn::Expr::Paren(paren) => expr_contains_ident(&paren.expr, name),
        syn::Expr::Group(group) => expr_contains_ident(&group.expr, name),
        syn::Expr::Reference(reference) => expr_contains_ident(&reference.expr, name),
        syn::Expr::Cast(cast) => expr_contains_ident(&cast.expr, name),
        syn::Expr::Call(call) => {
            expr_contains_ident(&call.func, name)
                || call.args.iter().any(|arg| expr_contains_ident(arg, name))
        }
        syn::Expr::MethodCall(method) => {
            expr_contains_ident(&method.receiver, name)
                || method.args.iter().any(|arg| expr_contains_ident(arg, name))
        }
        syn::Expr::Index(index) => {
            expr_contains_ident(&index.expr, name) || expr_contains_ident(&index.index, name)
        }
        syn::Expr::Field(field) => expr_contains_ident(&field.base, name),
        syn::Expr::Tuple(tuple) => tuple
            .elems
            .iter()
            .any(|elem| expr_contains_ident(elem, name)),
        _ => false,
    }
}

fn reject_opaque_bound_type(
    construct: &str,
    name: &str,
    ty: &TrustVcType,
) -> Result<(), LoweringError> {
    if let TrustVcType::Opaque(type_name) = ty {
        return Err(LoweringError::InvalidType(format!(
            "Unsupported type '{}' in {} bound variable '{}'",
            type_name, construct, name
        )));
    }
    Ok(())
}

fn extract_closure_params(
    closure: &syn::ExprClosure,
    env: &TypeEnv,
) -> Result<Vec<(String, TrustVcType)>, LoweringError> {
    let mut params = Vec::new();
    for input in &closure.inputs {
        match input {
            syn::Pat::Type(pt) => {
                if let syn::Pat::Ident(pi) = &*pt.pat {
                    let name = pi.ident.to_string();
                    let ty = env.resolve_syn_type(&pt.ty).map_err(|err| {
                        LoweringError::InvalidType(format!("param '{}': {}", name, err))
                    })?;
                    reject_opaque_bound_type("quantifier", &name, &ty)?;
                    params.push((name, ty));
                } else {
                    return Err(LoweringError::UnsupportedPattern(
                        "complex closure param".into(),
                    ));
                }
            }
            syn::Pat::Ident(pi) => {
                return Err(LoweringError::InvalidType(format!(
                    "closure parameter '{}' requires an explicit type annotation \
                     (e.g., |{}: u32| ...). Untyped quantifier-bound variables \
                     cannot be soundly defaulted.",
                    pi.ident, pi.ident,
                )));
            }
            _ => {
                return Err(LoweringError::UnsupportedPattern(
                    "unsupported closure param".into(),
                ))
            }
        }
    }
    Ok(params)
}
