// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Call-site binding helpers for `extern_spec` contracts.

use crate::error::{TrustVcError, TrustVcResult};
use quote::ToTokens;
use std::collections::HashMap;
use syn::visit_mut::{self, VisitMut};
use syn::Expr;

const CALL_EXPR_CONTEXT: &str = "parse extern_spec call expression";
const CONTRACT_EXPR_CONTEXT: &str = "parse extern_spec contract expression";
const BINDING_EXPR_CONTEXT: &str = "parse extern_spec binding expression";

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ExternSpecCallBindings {
    pub(crate) receiver_expr: Option<String>,
    pub(crate) arg_exprs: Vec<String>,
    pub(crate) result_expr: Option<String>,
}

pub(crate) fn bindings_from_call_expr_source(
    call_expr_source: &str,
    result_expr: Option<&str>,
) -> TrustVcResult<ExternSpecCallBindings> {
    let expr = parse_expr(call_expr_source, CALL_EXPR_CONTEXT)?;

    let (receiver_expr, arg_exprs) = match expr {
        Expr::MethodCall(method_call) => (
            Some(render_expr(&method_call.receiver)),
            method_call.args.iter().map(render_expr).collect(),
        ),
        Expr::Call(call) => (None, call.args.iter().map(render_expr).collect()),
        other => {
            return Err(TrustVcError::Parse {
                context: CALL_EXPR_CONTEXT,
                source: syn::Error::new_spanned(
                    other,
                    "extern_spec call-site binding requires a function or method call expression",
                ),
            });
        }
    };

    Ok(ExternSpecCallBindings {
        receiver_expr,
        arg_exprs,
        result_expr: result_expr.map(ToOwned::to_owned),
    })
}

pub(crate) fn substitute_contract_placeholders(
    contract: &str,
    param_names: &[String],
    bindings: &ExternSpecCallBindings,
) -> TrustVcResult<String> {
    let replacements = build_replacements(param_names, bindings)?;
    if replacements.is_empty() {
        return Ok(contract.to_string());
    }

    let mut expr = parse_expr(contract, CONTRACT_EXPR_CONTEXT)?;
    let mut rewriter = PlaceholderRewriter { replacements };
    rewriter.visit_expr_mut(&mut expr);
    Ok(render_expr(&expr))
}

fn build_replacements(
    param_names: &[String],
    bindings: &ExternSpecCallBindings,
) -> TrustVcResult<HashMap<String, Expr>> {
    if bindings.arg_exprs.len() != param_names.len() {
        return Err(TrustVcError::Internal {
            context: "bind extern_spec call arguments",
            detail: format!(
                "extern_spec call binding arity mismatch: expected {} argument binding(s) for [{}], got {}",
                param_names.len(),
                param_names.join(", "),
                bindings.arg_exprs.len()
            ),
        });
    }

    let mut replacements = HashMap::new();

    if let Some(receiver_expr) = &bindings.receiver_expr {
        replacements.insert(
            "self".to_string(),
            parenthesize(parse_expr(receiver_expr, BINDING_EXPR_CONTEXT)?),
        );
    }

    for (param_name, arg_expr) in param_names.iter().zip(&bindings.arg_exprs) {
        replacements.insert(
            param_name.clone(),
            parenthesize(parse_expr(arg_expr, BINDING_EXPR_CONTEXT)?),
        );
    }

    if let Some(result_expr) = &bindings.result_expr {
        replacements.insert(
            "result".to_string(),
            parenthesize(parse_expr(result_expr, BINDING_EXPR_CONTEXT)?),
        );
    }

    Ok(replacements)
}

fn parse_expr(source: &str, context: &'static str) -> TrustVcResult<Expr> {
    syn::parse_str::<Expr>(source).map_err(|source| TrustVcError::Parse { context, source })
}

fn render_expr(expr: &Expr) -> String {
    expr.to_token_stream().to_string()
}

fn parenthesize(expr: Expr) -> Expr {
    syn::parse_quote!((#expr))
}

struct PlaceholderRewriter {
    replacements: HashMap<String, Expr>,
}

impl VisitMut for PlaceholderRewriter {
    fn visit_expr_mut(&mut self, expr: &mut Expr) {
        visit_mut::visit_expr_mut(self, expr);

        let Some(name) = placeholder_name(expr) else {
            return;
        };

        if let Some(replacement) = self.replacements.get(&name) {
            *expr = replacement.clone();
        }
    }
}

fn placeholder_name(expr: &Expr) -> Option<String> {
    let Expr::Path(expr_path) = expr else {
        return None;
    };

    if expr_path.qself.is_some() || expr_path.path.leading_colon.is_some() {
        return None;
    }

    let mut segments = expr_path.path.segments.iter();
    let segment = segments.next()?;
    if segments.next().is_some() || !matches!(segment.arguments, syn::PathArguments::None) {
        return None;
    }

    Some(segment.ident.to_string())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_bindings_from_method_call_source_collects_receiver_args_and_result() {
        let bindings =
            bindings_from_call_expr_source("input.rotate_left(zero_amount)", Some("rotated"))
                .expect("method call bindings should parse");

        assert_eq!(bindings.receiver_expr.as_deref(), Some("input"));
        assert_eq!(bindings.arg_exprs, vec!["zero_amount"]);
        assert_eq!(bindings.result_expr.as_deref(), Some("rotated"));
    }

    #[test]
    fn test_bindings_from_function_call_source_collects_args_only() {
        let bindings = bindings_from_call_expr_source("abs(value)", Some("result_var"))
            .expect("function call bindings should parse");

        assert!(bindings.receiver_expr.is_none());
        assert_eq!(bindings.arg_exprs, vec!["value"]);
        assert_eq!(bindings.result_expr.as_deref(), Some("result_var"));
    }

    #[test]
    fn test_substitute_contract_placeholders_rewrites_receiver_argument_and_result() {
        let rewritten = substitute_contract_placeholders(
            "result == self && shift == 0",
            &[String::from("shift")],
            &ExternSpecCallBindings {
                receiver_expr: Some("input".to_string()),
                arg_exprs: vec!["zero_amount".to_string()],
                result_expr: Some("rotated".to_string()),
            },
        )
        .expect("contract substitution should succeed");

        assert!(rewritten.contains("rotated"));
        assert!(rewritten.contains("input"));
        assert!(rewritten.contains("zero_amount"));
        assert!(!rewritten.contains("result == self"));
    }

    #[test]
    fn test_substitute_contract_placeholders_rejects_argument_arity_mismatch() {
        let err = substitute_contract_placeholders(
            "result == self",
            &[String::from("shift")],
            &ExternSpecCallBindings {
                receiver_expr: Some("input".to_string()),
                arg_exprs: vec![],
                result_expr: Some("rotated".to_string()),
            },
        )
        .expect_err("arity mismatch should fail closed");

        assert!(err.to_string().contains("arity mismatch"));
    }
}
