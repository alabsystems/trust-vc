// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for `expr_references_any_name` variable-scope analysis.
//!
//! Split from `advanced.rs` for the 500-line limit (#2621).

use super::expr_references_any_name;
use crate::ir::{CompareOp, QuantifierKind, TrustVcExpr, TrustVcType};
use std::collections::HashSet;

fn bool_ty() -> TrustVcType {
    TrustVcType::Bool
}

fn u32_ty() -> TrustVcType {
    TrustVcType::Uint { width: 32 }
}

fn var(name: &str) -> TrustVcExpr {
    TrustVcExpr::Var {
        name: name.to_string(),
        ty: u32_ty(),
    }
}

fn fn_call(name: &str, args: Vec<TrustVcExpr>) -> TrustVcExpr {
    TrustVcExpr::FnCall {
        name: name.to_string(),
        args,
        return_ty: u32_ty(),
    }
}

fn eq(left: TrustVcExpr, right: TrustVcExpr) -> TrustVcExpr {
    TrustVcExpr::Compare {
        op: CompareOp::Eq,
        left: Box::new(left),
        right: Box::new(right),
    }
}

#[test]
fn test_expr_references_any_name_let_shadowing_keeps_value_scope() {
    let expr = TrustVcExpr::Let {
        name: "x".to_string(),
        ty: u32_ty(),
        value: Box::new(fn_call("f", vec![var("x")])),
        body: Box::new(fn_call("g", vec![var("x")])),
    };
    let names: HashSet<&str> = ["x"].into_iter().collect();
    assert!(
        expr_references_any_name(&expr, &names),
        "let value should still see the outer x even when the body shadows it"
    );
}

#[test]
fn test_expr_references_any_name_let_body_scoped_out() {
    // Negative test: body-only reference to let-bound x must not match outer scope.
    // Unlike test_let_shadowing_keeps_value_scope which passes with or without
    // the fix (value arm always matches), this test ONLY passes with scoping.
    let expr = TrustVcExpr::Let {
        name: "x".to_string(),
        ty: u32_ty(),
        value: Box::new(TrustVcExpr::IntLit {
            value: 42,
            ty: u32_ty(),
        }),
        body: Box::new(fn_call("g", vec![var("x")])),
    };
    let names: HashSet<&str> = ["x"].into_iter().collect();
    assert!(
        !expr_references_any_name(&expr, &names),
        "body-only reference to let-bound x must not satisfy outer scope check"
    );
}

#[test]
fn test_expr_references_any_name_quantifier_shadowing_applies_to_triggers() {
    let expr = TrustVcExpr::Quantifier {
        kind: QuantifierKind::Forall,
        bound_vars: vec![("x".to_string(), u32_ty())],
        body: Box::new(eq(var("x"), var("x"))),
        triggers: Some(vec![vec![fn_call("f", vec![var("x")])]]),
        trigger_inference_mode: None,
    };
    let names: HashSet<&str> = ["x"].into_iter().collect();
    assert!(
        !expr_references_any_name(&expr, &names),
        "inner quantifier-bound x must not satisfy outer trigger validation"
    );
}

#[test]
fn test_expr_references_any_name_choose_shadowing_removes_bound_var() {
    let expr = TrustVcExpr::Choose {
        var_name: "x".to_string(),
        var_ty: u32_ty(),
        condition: Box::new(eq(var("x"), var("x"))),
        key: "advanced_choose_shadowing".to_string(),
        also_assert: None,
    };
    let names: HashSet<&str> = ["x"].into_iter().collect();
    assert!(
        !expr_references_any_name(&expr, &names),
        "choose-bound x must not count as the outer bound variable"
    );
}

#[test]
fn test_expr_references_any_name_spec_closure_shadowing_removes_params() {
    let expr = TrustVcExpr::SpecClosure {
        params: vec![("x".to_string(), u32_ty())],
        body: Box::new(fn_call("f", vec![var("x")])),
        ty: bool_ty(),
    };
    let names: HashSet<&str> = ["x"].into_iter().collect();
    assert!(
        !expr_references_any_name(&expr, &names),
        "spec-closure params must shadow outer names during trigger validation"
    );
}
