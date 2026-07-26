// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Phase-1 SMT-LIB2 emission for static proof condition strings.
//!
//! Part of #2595: bridge `StaticProofContext` contracts into MergeBundle v4
//! using Int-mode SMT-LIB2 terms that the merge runner can execute directly.

use std::collections::HashMap;

use quote::ToTokens;
use syn::{BinOp, Expr, ExprBinary, ExprLit, ExprPath, ExprUnary, Lit, UnOp};

use crate::error::{TrustVcError, TrustVcResult};
use crate::ir::TrustVcType;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ExprSort {
    Bool,
    Int,
}

/// Converts a static proof condition string into an SMT-LIB2 term.
///
/// Phase 1 intentionally emits only the subset needed for the static proof
/// bridge: identifiers, integer/bool literals, boolean connectives,
/// comparisons, and parenthesized subexpressions. Arithmetic is supported only
/// for `int`/`nat`-style parameters; finite-width integer arithmetic fails
/// closed because the Int-mode bridge does not preserve modular BV semantics.
pub(crate) fn condition_to_smtlib2(
    condition: &str,
    params: &[(String, String)],
) -> TrustVcResult<String> {
    let expr = syn::parse_str::<Expr>(condition).map_err(|source| TrustVcError::Parse {
        context: "parse static proof condition",
        source,
    })?;
    let params = params
        .iter()
        .map(|(name, ty)| (name.as_str(), TrustVcType::parse_or_opaque(ty)))
        .collect::<HashMap<_, _>>();
    let sort = expr_sort(&expr, &params)?;
    if sort != ExprSort::Bool {
        return Err(emit_error(format!(
            "static proof condition must produce a Bool term, got {sort:?}: `{condition}`"
        )));
    }
    reject_finite_int_arithmetic_in_int_mode(&expr, &params)?;
    expr_to_smtlib2(&expr, &params)
}

fn reject_finite_int_arithmetic_in_int_mode(
    expr: &Expr,
    params: &HashMap<&str, TrustVcType>,
) -> TrustVcResult<()> {
    if contains_finite_int_arithmetic(expr, params)? {
        return Err(emit_error(
            "Int-mode static proof bridge does not support arithmetic over finite-width integer parameters"
                .to_string(),
        ));
    }
    Ok(())
}

fn contains_finite_int_arithmetic(
    expr: &Expr,
    params: &HashMap<&str, TrustVcType>,
) -> TrustVcResult<bool> {
    match expr {
        Expr::Binary(binary) => {
            let operator_is_arith =
                matches!(binary.op, BinOp::Add(_) | BinOp::Sub(_) | BinOp::Mul(_));
            if operator_is_arith
                && (mentions_finite_int(&binary.left, params)?
                    || mentions_finite_int(&binary.right, params)?)
            {
                return Ok(true);
            }
            Ok(contains_finite_int_arithmetic(&binary.left, params)?
                || contains_finite_int_arithmetic(&binary.right, params)?)
        }
        Expr::Unary(unary) => {
            if matches!(unary.op, UnOp::Neg(_)) && mentions_finite_int(&unary.expr, params)? {
                return Ok(true);
            }
            contains_finite_int_arithmetic(&unary.expr, params)
        }
        Expr::Paren(paren) => contains_finite_int_arithmetic(&paren.expr, params),
        Expr::Group(group) => contains_finite_int_arithmetic(&group.expr, params),
        _ => Ok(false),
    }
}

fn mentions_finite_int(expr: &Expr, params: &HashMap<&str, TrustVcType>) -> TrustVcResult<bool> {
    match expr {
        Expr::Path(path) => {
            let Some(ident) = path.path.get_ident() else {
                return Ok(false);
            };
            let name = ident.to_string();
            Ok(params.get(name.as_str()).is_some_and(is_finite_int_type))
        }
        Expr::Binary(binary) => Ok(mentions_finite_int(&binary.left, params)?
            || mentions_finite_int(&binary.right, params)?),
        Expr::Unary(unary) => mentions_finite_int(&unary.expr, params),
        Expr::Paren(paren) => mentions_finite_int(&paren.expr, params),
        Expr::Group(group) => mentions_finite_int(&group.expr, params),
        _ => Ok(false),
    }
}

fn is_finite_int_type(ty: &TrustVcType) -> bool {
    matches!(ty, TrustVcType::Int { .. } | TrustVcType::Uint { .. })
}

fn expr_to_smtlib2(expr: &Expr, params: &HashMap<&str, TrustVcType>) -> TrustVcResult<String> {
    match expr {
        Expr::Path(path) => path_to_smtlib2(path, params),
        Expr::Lit(lit) => lit_to_smtlib2(lit),
        Expr::Binary(binary) => binary_to_smtlib2(binary, params),
        Expr::Unary(unary) => unary_to_smtlib2(unary, params),
        Expr::Paren(paren) => expr_to_smtlib2(&paren.expr, params),
        Expr::Group(group) => expr_to_smtlib2(&group.expr, params),
        _ => Err(unsupported_expr(
            expr,
            "unsupported expression in static proof condition",
        )),
    }
}

fn path_to_smtlib2(path: &ExprPath, params: &HashMap<&str, TrustVcType>) -> TrustVcResult<String> {
    let ident = path
        .path
        .get_ident()
        .ok_or_else(|| unsupported_tokens(path, "complex path in static proof condition"))?;
    let name = ident.to_string();
    if !params.contains_key(name.as_str()) {
        return Err(emit_error(format!(
            "undeclared identifier `{name}` in static proof condition"
        )));
    }
    Ok(name)
}

fn lit_to_smtlib2(lit: &ExprLit) -> TrustVcResult<String> {
    match &lit.lit {
        Lit::Int(value) => Ok(value.base10_digits().to_string()),
        Lit::Bool(value) => Ok(if value.value {
            "true".to_string()
        } else {
            "false".to_string()
        }),
        _ => Err(unsupported_tokens(
            &lit.lit,
            "unsupported literal in static proof condition",
        )),
    }
}

fn binary_to_smtlib2(
    binary: &ExprBinary,
    params: &HashMap<&str, TrustVcType>,
) -> TrustVcResult<String> {
    let lhs = expr_to_smtlib2(&binary.left, params)?;
    let rhs = expr_to_smtlib2(&binary.right, params)?;
    let op = match &binary.op {
        BinOp::Gt(_) => ">",
        BinOp::Ge(_) => ">=",
        BinOp::Lt(_) => "<",
        BinOp::Le(_) => "<=",
        BinOp::Eq(_) => "=",
        BinOp::Ne(_) => "distinct",
        BinOp::Add(_) => "+",
        BinOp::Sub(_) => "-",
        BinOp::Mul(_) => "*",
        BinOp::And(_) => "and",
        BinOp::Or(_) => "or",
        _ => {
            return Err(unsupported_tokens(
                &binary.op,
                "unsupported binary operator in static proof condition",
            ))
        }
    };
    Ok(format!("({op} {lhs} {rhs})"))
}

fn expr_sort(expr: &Expr, params: &HashMap<&str, TrustVcType>) -> TrustVcResult<ExprSort> {
    match expr {
        Expr::Path(path) => path_sort(path, params),
        Expr::Lit(lit) => lit_sort(lit),
        Expr::Binary(binary) => binary_sort(binary, params),
        Expr::Unary(unary) => unary_sort(unary, params),
        Expr::Paren(paren) => expr_sort(&paren.expr, params),
        Expr::Group(group) => expr_sort(&group.expr, params),
        _ => Err(unsupported_expr(
            expr,
            "unsupported expression in static proof condition",
        )),
    }
}

fn path_sort(path: &ExprPath, params: &HashMap<&str, TrustVcType>) -> TrustVcResult<ExprSort> {
    let ident = path
        .path
        .get_ident()
        .ok_or_else(|| unsupported_tokens(path, "complex path in static proof condition"))?;
    let name = ident.to_string();
    let ty = params.get(name.as_str()).ok_or_else(|| {
        emit_error(format!(
            "undeclared identifier `{name}` in static proof condition"
        ))
    })?;
    match ty {
        TrustVcType::Bool => Ok(ExprSort::Bool),
        TrustVcType::Int { .. }
        | TrustVcType::Uint { .. }
        | TrustVcType::MathInt
        | TrustVcType::Nat => Ok(ExprSort::Int),
        _ => Err(emit_error(format!(
            "unsupported identifier type `{}` in static proof condition",
            ty.to_type_string()
        ))),
    }
}

fn lit_sort(lit: &ExprLit) -> TrustVcResult<ExprSort> {
    match &lit.lit {
        Lit::Int(_) => Ok(ExprSort::Int),
        Lit::Bool(_) => Ok(ExprSort::Bool),
        _ => Err(unsupported_tokens(
            &lit.lit,
            "unsupported literal in static proof condition",
        )),
    }
}

fn binary_sort(
    binary: &ExprBinary,
    params: &HashMap<&str, TrustVcType>,
) -> TrustVcResult<ExprSort> {
    let lhs = expr_sort(&binary.left, params)?;
    let rhs = expr_sort(&binary.right, params)?;
    match &binary.op {
        BinOp::Gt(_) | BinOp::Ge(_) | BinOp::Lt(_) | BinOp::Le(_) => {
            require_binary_sorts(binary, lhs, rhs, ExprSort::Int)?;
            Ok(ExprSort::Bool)
        }
        BinOp::Eq(_) | BinOp::Ne(_) => {
            if lhs != rhs {
                return Err(emit_error(format!(
                    "mismatched operand sorts in static proof condition equality: left={lhs:?}, right={rhs:?}"
                )));
            }
            Ok(ExprSort::Bool)
        }
        BinOp::Add(_) | BinOp::Sub(_) | BinOp::Mul(_) => {
            require_binary_sorts(binary, lhs, rhs, ExprSort::Int)?;
            Ok(ExprSort::Int)
        }
        BinOp::And(_) | BinOp::Or(_) => {
            require_binary_sorts(binary, lhs, rhs, ExprSort::Bool)?;
            Ok(ExprSort::Bool)
        }
        _ => Err(unsupported_tokens(
            &binary.op,
            "unsupported binary operator in static proof condition",
        )),
    }
}

fn require_binary_sorts(
    binary: &ExprBinary,
    lhs: ExprSort,
    rhs: ExprSort,
    expected: ExprSort,
) -> TrustVcResult<()> {
    if lhs != expected || rhs != expected {
        return Err(emit_error(format!(
            "operator `{}` requires {expected:?} operands, got left={lhs:?}, right={rhs:?}",
            binary.op.to_token_stream()
        )));
    }
    Ok(())
}

fn unary_to_smtlib2(
    unary: &ExprUnary,
    params: &HashMap<&str, TrustVcType>,
) -> TrustVcResult<String> {
    let operand = expr_to_smtlib2(&unary.expr, params)?;
    match &unary.op {
        UnOp::Not(_) => Ok(format!("(not {operand})")),
        UnOp::Neg(_) => Ok(format!("(- {operand})")),
        _ => Err(unsupported_tokens(
            &unary.op,
            "unsupported unary operator in static proof condition",
        )),
    }
}

fn unary_sort(unary: &ExprUnary, params: &HashMap<&str, TrustVcType>) -> TrustVcResult<ExprSort> {
    let operand = expr_sort(&unary.expr, params)?;
    match &unary.op {
        UnOp::Not(_) => {
            require_unary_sort(unary, operand, ExprSort::Bool)?;
            Ok(ExprSort::Bool)
        }
        UnOp::Neg(_) => {
            require_unary_sort(unary, operand, ExprSort::Int)?;
            Ok(ExprSort::Int)
        }
        _ => Err(unsupported_tokens(
            &unary.op,
            "unsupported unary operator in static proof condition",
        )),
    }
}

fn require_unary_sort(
    unary: &ExprUnary,
    actual: ExprSort,
    expected: ExprSort,
) -> TrustVcResult<()> {
    if actual != expected {
        return Err(emit_error(format!(
            "operator `{}` requires a {expected:?} operand, got {actual:?}",
            unary.op.to_token_stream()
        )));
    }
    Ok(())
}

fn unsupported_expr(expr: &Expr, detail: &str) -> TrustVcError {
    unsupported_tokens(expr, detail)
}

fn unsupported_tokens(tokens: &impl ToTokens, detail: &str) -> TrustVcError {
    emit_error(format!("{detail}: `{}`", tokens.to_token_stream()))
}

fn emit_error(detail: impl Into<String>) -> TrustVcError {
    TrustVcError::Encoding {
        context: "emit static proof SMT-LIB2",
        detail: detail.into(),
    }
}

#[cfg(test)]
mod tests {
    use super::condition_to_smtlib2;

    #[test]
    fn test_condition_to_smtlib2_simple_comparison() {
        let params = vec![("x".to_string(), "u64".to_string())];
        let term = condition_to_smtlib2("x > 0", &params).expect("simple comparison should emit");
        assert_eq!(term, "(> x 0)");
    }

    #[test]
    fn test_condition_to_smtlib2_nested_arithmetic_and_logic() {
        let params = vec![
            ("a".to_string(), "int".to_string()),
            ("b".to_string(), "int".to_string()),
            ("ready".to_string(), "bool".to_string()),
        ];
        let term = condition_to_smtlib2("ready && (a + b >= 1)", &params)
            .expect("nested arithmetic and logic should emit");
        assert_eq!(term, "(and ready (>= (+ a b) 1))");
    }

    #[test]
    fn test_condition_to_smtlib2_rejects_undeclared_variables() {
        let params = vec![("x".to_string(), "u64".to_string())];
        let err = condition_to_smtlib2("x > y", &params)
            .expect_err("undeclared variables should fail closed");
        assert!(
            err.to_string().contains("undeclared identifier `y`"),
            "unexpected error: {err}"
        );
    }

    #[test]
    fn test_condition_to_smtlib2_rejects_non_boolean_top_level_terms() {
        let params = vec![
            ("a".to_string(), "u64".to_string()),
            ("b".to_string(), "u64".to_string()),
        ];
        let err = condition_to_smtlib2("a + b", &params)
            .expect_err("top-level arithmetic term should fail closed");
        assert!(
            err.to_string().contains("must produce a Bool term"),
            "unexpected error: {err}"
        );
    }

    #[test]
    fn test_condition_to_smtlib2_rejects_finite_width_integer_arithmetic() {
        let params = vec![
            ("x".to_string(), "u32".to_string()),
            ("y".to_string(), "u32".to_string()),
        ];
        let err = condition_to_smtlib2("x + y > 0", &params)
            .expect_err("finite-width integer arithmetic should fail closed");
        assert!(
            err.to_string()
                .contains("does not support arithmetic over finite-width integer parameters"),
            "unexpected error: {err}"
        );
    }

    #[test]
    fn test_condition_to_smtlib2_allows_math_int_arithmetic() {
        let params = vec![("n".to_string(), "int".to_string())];
        let term = condition_to_smtlib2("n + 1 > n", &params)
            .expect("math-int arithmetic should remain supported");
        assert_eq!(term, "(> (+ n 1) n)");
    }
}
