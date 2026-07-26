//! Tests for bitwise operator handling in the RustToSmtTranslator.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use trust_vc_core::RustToSmtTranslator;

#[test]
fn test_translator_bitwise_operators_not_supported() {
    let translator = RustToSmtTranslator::new();

    // Bitwise AND
    let result = translator.translate("a & b");
    assert!(result.is_err(), "Bitwise AND should not be supported");

    // Bitwise OR
    let result = translator.translate("a | b");
    assert!(result.is_err(), "Bitwise OR should not be supported");

    // Bitwise XOR
    let result = translator.translate("a ^ b");
    assert!(result.is_err(), "Bitwise XOR should not be supported");

    // Left shift
    let result = translator.translate("a << 2");
    assert!(result.is_err(), "Left shift should not be supported");

    // Right shift
    let result = translator.translate("a >> 2");
    assert!(result.is_err(), "Right shift should not be supported");
}

#[test]
fn test_translator_distinguishes_logical_vs_bitwise() {
    let translator = RustToSmtTranslator::new();

    // Logical AND should work
    let result = translator.translate("a && b");
    assert!(result.is_ok(), "Logical AND should be supported");
    assert_eq!(result.unwrap(), "(a && b)");

    // Bitwise AND should fail
    let result = translator.translate("a & b");
    assert!(result.is_err(), "Bitwise AND should not be supported");

    // Logical OR should work
    let result = translator.translate("a || b");
    assert!(result.is_ok(), "Logical OR should be supported");
    assert_eq!(result.unwrap(), "(a || b)");

    // Bitwise OR should fail
    let result = translator.translate("a | b");
    assert!(result.is_err(), "Bitwise OR should not be supported");
}
