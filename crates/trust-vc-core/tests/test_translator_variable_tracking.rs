//! Tests for variable tracking in the RustToSmtTranslator.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use trust_vc_core::RustToSmtTranslator;

#[test]
fn test_translator_variable_registration_unused() {
    // Registration is intentionally side-effect free for translation today.
    let mut translator = RustToSmtTranslator::new();

    translator.register_variable("my_seq".to_string(), "Seq<i32>".to_string());

    assert_eq!(
        translator.translate("my_seq.len()").unwrap(),
        "(len my_seq)",
        "registered variables should remain valid translator inputs"
    );
}

#[test]
fn test_translator_doesnt_use_variable_context() {
    // Without variable registration, the translator can't distinguish
    // between different variable types which could lead to wrong translations
    let translator = RustToSmtTranslator::new();

    // This could be a Seq.len() or String.len() - translator doesn't know
    let result = translator.translate("x.len()");
    assert_eq!(result.unwrap(), "(len x)");

    // Without type info, can't validate if method is appropriate for type
}
