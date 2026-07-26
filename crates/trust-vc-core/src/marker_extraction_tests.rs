// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Unit tests for function marker extraction (requires, ensures, decreases).
//!
//! Extracted from `marker_extraction.rs` to keep production code under 500 lines.

use super::*;
use syn::parse_quote;

#[test]
fn malformed_requires_name_value_returns_error() {
    let func: ItemFn = parse_quote! {
        #[__trust_vc_requires = 123]
        fn malformed_name_value(x: i32) {}
    };

    let err = extract_function_markers(&func)
        .expect_err("malformed #[__trust_vc_requires = 123] must not be treated as absent marker")
        .to_string();
    assert!(
        err.contains("__trust_vc_requires"),
        "error should identify malformed marker: {}",
        err
    );
}

#[test]
fn malformed_requires_function_like_returns_error() {
    let func: ItemFn = parse_quote! {
        #[__trust_vc_requires(not_a_string)]
        fn malformed_function_like(x: i32) {}
    };

    let err = extract_function_markers(&func)
        .expect_err("malformed #[__trust_vc_requires(...)] must not be treated as absent marker")
        .to_string();
    assert!(
        err.contains("__trust_vc_requires"),
        "error should identify malformed marker: {}",
        err
    );
}

#[test]
fn valid_requires_marker_still_extracts() {
    let func: ItemFn = parse_quote! {
        #[__trust_vc_requires("x > 0")]
        fn valid_marker(x: i32) {}
    };

    let markers = extract_function_markers(&func)
        .expect("valid marker should parse")
        .expect("marker should be present");
    assert_eq!(markers.requires, vec!["x > 0".to_string()]);
    assert!(markers.ensures.is_empty());
    assert!(markers.decreases.is_none());
}

/// Documents the macro-to-encoder disconnection for decreases when/via (#1817).
///
/// The macro generates `__trust_vc_decreases_when` and `__trust_vc_decreases_via`
/// as let-bindings inside cfg(trust_mc) blocks (not as attributes). Even if they
/// were attributes, extract_function_markers does not recognize them.
///
/// This test catches the disconnection: when someone wires when/via through
/// the extraction path, this test must be updated to expect the new fields.
#[test]
fn extract_function_markers_ignores_decreases_when_via_attributes() {
    // Simulate hypothetical when/via as attributes alongside decreases.
    // extract_function_markers only recognizes __trust_vc_requires,
    // __trust_vc_ensures, and __trust_vc_decreases — the when/via are dropped.
    let func: ItemFn = parse_quote! {
        #[__trust_vc_decreases = "n"]
        #[__trust_vc_decreases_when = "n > 0"]
        #[__trust_vc_decreases_via = "prove_termination"]
        fn conditional_recursion(n: u64) -> u64 { n }
    };

    let markers = extract_function_markers(&func)
        .expect("extraction should succeed")
        .expect("decreases marker should be present");

    // Decreases is extracted
    assert_eq!(
        markers.decreases,
        Some("n".to_string()),
        "basic decreases should be extracted"
    );

    // FunctionMarkers has no when/via fields — this is the disconnection.
    // When #1817 is fixed, FunctionMarkers will gain decreases_when and
    // decreases_via fields, and this test should be updated to verify
    // they are populated.
    assert!(
        markers.requires.is_empty(),
        "when/via should not leak into requires"
    );
    assert!(
        markers.ensures.is_empty(),
        "when/via should not leak into ensures"
    );
}
