//! Extensional equality expansion marker tests
//!
//! Tests that ext_eq and ext_ne properly add markers and preserve expressions.
//!
//! Split from expand_markers.rs per #2380.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use quote::quote;
use trust_vc_core::{expand_ext_eq, expand_ext_ne};

#[test]
fn expand_ext_eq_includes_markers() {
    let lhs = quote!(a);
    let rhs = quote!(b);
    let expanded = expand_ext_eq(lhs, rhs);
    let expanded_str = expanded.to_string();
    assert!(
        expanded_str.contains("__trust_vc_ext_eq_lhs"),
        "expected ext_eq lhs marker in expansion: {expanded_str}"
    );
    assert!(
        expanded_str.contains("__trust_vc_ext_eq_rhs"),
        "expected ext_eq rhs marker in expansion: {expanded_str}"
    );
}

#[test]
fn expand_ext_ne_includes_markers() {
    let lhs = quote!(x);
    let rhs = quote!(y);
    let expanded = expand_ext_ne(lhs, rhs);
    let expanded_str = expanded.to_string();
    assert!(
        expanded_str.contains("__trust_vc_ext_ne_lhs"),
        "expected ext_ne lhs marker in expansion: {expanded_str}"
    );
    assert!(
        expanded_str.contains("__trust_vc_ext_ne_rhs"),
        "expected ext_ne rhs marker in expansion: {expanded_str}"
    );
}

#[test]
fn expand_ext_eq_preserves_both_expressions() {
    let lhs = quote!(arr1[0..5]);
    let rhs = quote!(arr2.slice(0, 5));
    let expanded = expand_ext_eq(lhs, rhs);
    let expanded_str = expanded.to_string();
    // Verify LHS is preserved
    assert!(
        expanded_str.contains("arr1 [0 .. 5]") || expanded_str.contains("arr1[0..5]"),
        "expected lhs expression in expansion: {expanded_str}"
    );
    // Verify RHS is preserved
    assert!(
        expanded_str.contains("arr2 . slice") || expanded_str.contains("arr2.slice"),
        "expected rhs expression in expansion: {expanded_str}"
    );
}

#[test]
fn expand_ext_ne_preserves_both_expressions() {
    let lhs = quote!(seq.len());
    let rhs = quote!(other.len());
    let expanded = expand_ext_ne(lhs, rhs);
    let expanded_str = expanded.to_string();
    // Verify LHS is preserved
    assert!(
        expanded_str.contains("seq") && expanded_str.contains("len"),
        "expected lhs expression parts in expansion: {expanded_str}"
    );
    // Verify RHS is preserved
    assert!(
        expanded_str.contains("other"),
        "expected rhs expression in expansion: {expanded_str}"
    );
}

#[test]
fn expand_ext_eq_complex_expressions() {
    // Test with more complex expressions
    let lhs = quote!(vec1.iter().map(|x| x * 2).collect::<Vec<_>>());
    let rhs = quote!(vec2);
    let expanded = expand_ext_eq(lhs, rhs);
    let expanded_str = expanded.to_string();
    // Should contain parts of the complex expression
    assert!(
        expanded_str.contains("iter") && expanded_str.contains("map"),
        "expected complex lhs expression parts in expansion: {expanded_str}"
    );
}

#[test]
fn expand_ext_ne_different_types() {
    // Test with different expression types
    let lhs = quote!(a + b);
    let rhs = quote!(c - d);
    let expanded = expand_ext_ne(lhs, rhs);
    let expanded_str = expanded.to_string();
    // Both expressions should appear in stringify
    assert!(
        expanded_str.contains("a") && expanded_str.contains("b"),
        "expected lhs operands in expansion: {expanded_str}"
    );
    assert!(
        expanded_str.contains("c") && expanded_str.contains("d"),
        "expected rhs operands in expansion: {expanded_str}"
    );
}
