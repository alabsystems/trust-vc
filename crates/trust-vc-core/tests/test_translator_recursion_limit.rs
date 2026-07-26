//! Tests for recursion limits in the RustToSmtTranslator.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use trust_vc_core::RustToSmtTranslator;

#[test]
fn test_translator_extreme_nesting_depth() {
    let translator = RustToSmtTranslator::new();

    // Generate extremely nested expression (100 levels)
    let mut expr = "x".to_string();
    for _ in 0..100 {
        expr = format!("({})", expr);
    }

    // Deeply nested parentheses should translate successfully - Paren just unwraps
    let result = translator.translate(&expr);

    assert!(
        result.is_ok(),
        "100-level nested parens should translate, got: {:?}",
        result
    );
    assert_eq!(
        result.unwrap(),
        "x",
        "Nested parens around 'x' should produce 'x'"
    );
}

#[test]
fn test_translator_extreme_binary_chain() {
    let translator = RustToSmtTranslator::new();

    // Generate very long binary expression chain
    let mut expr = "a".to_string();
    for i in 0..50 {
        expr = format!("{} + b{}", expr, i);
    }

    // Should handle long chains without issue
    let result = translator.translate(&expr);
    assert!(result.is_ok(), "Should handle long expression chains");
}

#[test]
fn test_translator_complex_nested_methods() {
    let translator = RustToSmtTranslator::new();

    // Complex nested method calls
    let expr = "a.len().abs().min(b.len().max(c.len()))";

    // This will fail since we don't support chained methods, but shouldn't panic
    let result = translator.translate(expr);
    assert!(result.is_err(), "Chained methods not supported");
}
