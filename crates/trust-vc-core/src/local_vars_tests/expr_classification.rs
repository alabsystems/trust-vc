//! Tests for is_encodable_expr and is_arbitrary_expr classification.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;

// --- is_encodable_expr tests ---

#[test]
fn test_is_encodable_literal() {
    let expr: syn::Expr = syn::parse_str("42").unwrap();
    assert!(is_encodable_expr(&expr));
}

#[test]
fn test_is_encodable_bool_literal() {
    let expr: syn::Expr = syn::parse_str("true").unwrap();
    // `true` parses as a Path, not a Lit — single ident path is encodable
    assert!(is_encodable_expr(&expr));
}

#[test]
fn test_is_encodable_variable_ref() {
    let expr: syn::Expr = syn::parse_str("x").unwrap();
    assert!(is_encodable_expr(&expr));
}

#[test]
fn test_is_encodable_qualified_path_not_encodable() {
    let expr: syn::Expr = syn::parse_str("std::i32::MAX").unwrap();
    assert!(
        !is_encodable_expr(&expr),
        "Qualified paths should not be encodable"
    );
}

#[test]
fn test_is_encodable_binary_arithmetic() {
    let expr: syn::Expr = syn::parse_str("x + 1").unwrap();
    assert!(is_encodable_expr(&expr));
}

#[test]
fn test_is_encodable_nested_binary() {
    let expr: syn::Expr = syn::parse_str("a + b * c").unwrap();
    assert!(is_encodable_expr(&expr));
}

#[test]
fn test_is_encodable_comparison() {
    let expr: syn::Expr = syn::parse_str("x > 0").unwrap();
    assert!(is_encodable_expr(&expr));
}

#[test]
fn test_is_encodable_unary_negation() {
    let expr: syn::Expr = syn::parse_str("-x").unwrap();
    assert!(is_encodable_expr(&expr));
}

#[test]
fn test_is_not_encodable_deref() {
    let expr: syn::Expr = syn::parse_str("*x").unwrap();
    assert!(
        !is_encodable_expr(&expr),
        "Dereference expressions should not be treated as encodable let-bindings"
    );
}

#[test]
fn test_is_encodable_paren() {
    let expr: syn::Expr = syn::parse_str("(x + 1)").unwrap();
    assert!(is_encodable_expr(&expr));
}

#[test]
fn test_is_encodable_cast() {
    let expr: syn::Expr = syn::parse_str("x as u64").unwrap();
    assert!(is_encodable_expr(&expr));
}

#[test]
fn test_is_not_encodable_function_call() {
    let expr: syn::Expr = syn::parse_str("foo(x)").unwrap();
    assert!(
        !is_encodable_expr(&expr),
        "Function calls should not be encodable"
    );
}

#[test]
fn test_is_not_encodable_method_call() {
    let expr: syn::Expr = syn::parse_str("x.abs()").unwrap();
    assert!(
        !is_encodable_expr(&expr),
        "Method calls should not be encodable"
    );
}

#[test]
fn test_is_not_encodable_reference() {
    let expr: syn::Expr = syn::parse_str("&x").unwrap();
    assert!(
        !is_encodable_expr(&expr),
        "References should not be encodable"
    );
}

#[test]
fn test_is_not_encodable_closure() {
    let expr: syn::Expr = syn::parse_str("|x| x + 1").unwrap();
    assert!(
        !is_encodable_expr(&expr),
        "Closures should not be encodable"
    );
}

// --- is_arbitrary_expr tests (#2518) ---

#[test]
fn test_is_arbitrary_bare_macro() {
    let expr: syn::Expr = syn::parse_str("arbitrary!(i32)").unwrap();
    assert!(
        is_arbitrary_expr(&expr),
        "bare arbitrary! macro should be detected"
    );
}

#[test]
fn test_is_arbitrary_qualified_macro() {
    let expr: syn::Expr = syn::parse_str("trust_vc::arbitrary!(i32)").unwrap();
    assert!(
        is_arbitrary_expr(&expr),
        "qualified trust_vc::arbitrary! macro should be detected"
    );
}

#[test]
fn test_is_arbitrary_non_arbitrary_macro() {
    let expr: syn::Expr = syn::parse_str("choose!(|x: i32| x > 0)").unwrap();
    assert!(
        !is_arbitrary_expr(&expr),
        "choose! macro should NOT be detected as arbitrary"
    );
}

#[test]
fn test_is_arbitrary_function_call() {
    let expr: syn::Expr = syn::parse_str("Default::default()").unwrap();
    assert!(
        !is_arbitrary_expr(&expr),
        "Default::default() should NOT be detected as arbitrary"
    );
}
