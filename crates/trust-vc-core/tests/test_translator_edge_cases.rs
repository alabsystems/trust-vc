//! Tests for edge cases in the RustToSmtTranslator.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use trust_vc_core::RustToSmtTranslator;

#[test]
fn test_translator_handles_string_literals() {
    let translator = RustToSmtTranslator::new();

    // String literals are not currently supported
    let result = translator.translate(r#""hello""#);
    assert!(result.is_err(), "String literals should return error");
}

#[test]
fn test_translator_handles_cast_expressions() {
    let translator = RustToSmtTranslator::new();

    // Cast expressions like `x as u32` are not currently handled
    let result = translator.translate("x as u32");
    assert!(result.is_err(), "Cast expressions should return error");
}

#[test]
fn test_translator_handles_array_expressions() {
    let translator = RustToSmtTranslator::new();

    // Array literals are not currently supported
    let result = translator.translate("[1, 2, 3]");
    assert!(result.is_err(), "Array literals should return error");
}

#[test]
fn test_translator_handles_range_expressions() {
    let translator = RustToSmtTranslator::new();

    // Range expressions are not currently supported
    let result = translator.translate("1..10");
    assert!(result.is_err(), "Range expressions should return error");
}

#[test]
fn test_translator_handles_deeply_nested_expressions() {
    let translator = RustToSmtTranslator::new();

    // Test deeply nested expression doesn't cause stack overflow
    let deep_expr = "((((((((((a + b) + c) + d) + e) + f) + g) + h) + i) + j) + k)";
    let result = translator.translate(deep_expr);
    assert!(result.is_ok(), "Should handle deeply nested expressions");
}

#[test]
fn test_translator_handles_empty_input() {
    let translator = RustToSmtTranslator::new();

    // Empty string should fail to parse
    let result = translator.translate("");
    assert!(result.is_err(), "Empty input should return parse error");
}

#[test]
fn test_translator_handles_malformed_expressions() {
    let translator = RustToSmtTranslator::new();

    // Malformed expression should fail to parse
    let result = translator.translate("x + + y");
    assert!(
        result.is_err(),
        "Malformed expression should return parse error"
    );
}

#[test]
fn test_translator_handles_field_access() {
    let translator = RustToSmtTranslator::new();

    // Field access is not currently supported
    let result = translator.translate("point.x");
    assert!(
        result.is_err(),
        "Field access should return error for unknown method"
    );
}

#[test]
fn test_translator_handles_tuple_access() {
    let translator = RustToSmtTranslator::new();

    // Tuple index access is not currently supported
    let result = translator.translate("tuple.0");
    assert!(result.is_err(), "Tuple access should return error");
}

#[test]
fn test_translator_preserves_operator_precedence() {
    let translator = RustToSmtTranslator::new();

    // Test that parentheses are preserved for precedence
    let result = translator.translate("a + b * c");
    assert_eq!(result.unwrap(), "(a + (b * c))");

    let result2 = translator.translate("(a + b) * c");
    assert_eq!(result2.unwrap(), "((a + b) * c)");
}
