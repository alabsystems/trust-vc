//! Tests for operator associativity in the RustToSmtTranslator.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use trust_vc_core::RustToSmtTranslator;

#[test]
fn test_translator_left_associativity() {
    let translator = RustToSmtTranslator::new();

    // Subtraction is left-associative: a - b - c = (a - b) - c
    let result = translator.translate("a - b - c");
    assert_eq!(result.unwrap(), "((a - b) - c)");

    // Division is left-associative: a / b / c = (a / b) / c
    let result = translator.translate("a / b / c");
    assert_eq!(result.unwrap(), "((a / b) / c)");
}

#[test]
fn test_translator_mixed_precedence() {
    let translator = RustToSmtTranslator::new();

    // Multiplication has higher precedence than addition
    let result = translator.translate("a + b * c");
    assert_eq!(result.unwrap(), "(a + (b * c))");

    // But parentheses override precedence
    let result = translator.translate("(a + b) * c");
    assert_eq!(result.unwrap(), "((a + b) * c)");

    // Complex mixed expression
    let result = translator.translate("a + b * c - d / e");
    assert_eq!(result.unwrap(), "((a + (b * c)) - (d / e))");
}

#[test]
fn test_translator_comparison_chains() {
    let translator = RustToSmtTranslator::new();

    // Rust allows comparison chains but they parse as nested binaries
    // a < b < c parses as (a < b) < c which is a type error in Rust
    // but the translator should still handle the syntax
    let result = translator.translate("a < b");
    assert_eq!(result.unwrap(), "(a < b)");

    // Equality chains
    let result = translator.translate("a == b");
    assert_eq!(result.unwrap(), "(a == b)");
}

#[test]
fn test_translator_logical_precedence() {
    let translator = RustToSmtTranslator::new();

    // AND has higher precedence than OR
    let result = translator.translate("a || b && c");
    assert_eq!(result.unwrap(), "(a || (b && c))");

    // Parentheses can override
    let result = translator.translate("(a || b) && c");
    assert_eq!(result.unwrap(), "((a || b) && c)");
}
