//! Source-extraction path tests: #[decreases] marker processing.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use super::super::*;
use crate::marker_extraction::{apply_markers_to_context, FunctionMarkers};
use crate::vc::ObligationKind;

fn compact(s: &str) -> String {
    s.chars().filter(|c| !c.is_whitespace()).collect()
}

#[test]
fn test_source_extraction_decreases_generates_nonneg_obligation() {
    // Verify that apply_markers_to_context generates a MeasureNonNegative
    // obligation when FunctionMarkers contains a decreases measure.
    // We test the context directly rather than through verify_markers_impl
    // to confirm the obligation exists (not just that verification passes,
    // which could happen vacuously with no obligations).
    use crate::vc::VerificationContext;

    let markers = FunctionMarkers {
        requires: vec![],
        ensures: vec![],
        decreases: Some("n".to_string()),
    };

    // Parse a minimal function for apply_markers_to_context
    let func: syn::ItemFn = syn::parse_quote! {
        fn countdown(n: u64) -> u64 { n }
    };

    let mut ctx = VerificationContext::new();
    let result = apply_markers_to_context(&mut ctx, "countdown", &markers, &func);
    assert!(
        result.is_ok(),
        "apply_markers_to_context should succeed, got: {:?}",
        result
    );

    // Check that MeasureNonNegative obligation was generated
    let nonneg_count = ctx
        .obligations
        .iter()
        .filter(|o| matches!(o.kind, ObligationKind::MeasureNonNegative))
        .count();
    assert_eq!(
        nonneg_count, 1,
        "Expected exactly 1 MeasureNonNegative obligation, got {}",
        nonneg_count
    );

    // Verify the obligation's condition references the measure variable
    let nonneg = ctx
        .obligations
        .iter()
        .find(|o| matches!(o.kind, ObligationKind::MeasureNonNegative))
        .unwrap();
    assert!(
        nonneg.condition.contains("n"),
        "MeasureNonNegative condition should reference 'n', got: {}",
        nonneg.condition
    );
}

#[test]
fn test_source_extraction_decreases_tuple_generates_nonneg() {
    // Verify that tuple measures generate MeasureNonNegative for EACH component.
    use crate::vc::VerificationContext;

    let markers = FunctionMarkers {
        requires: vec![],
        ensures: vec![],
        decreases: Some("(a, b)".to_string()),
    };

    let func: syn::ItemFn = syn::parse_quote! {
        fn lex_countdown(a: i64, b: i64) -> i64 { a + b }
    };

    let mut ctx = VerificationContext::new();
    let result = apply_markers_to_context(&mut ctx, "lex_countdown", &markers, &func);
    assert!(
        result.is_ok(),
        "apply_markers_to_context should succeed, got: {:?}",
        result
    );

    // Check that TWO MeasureNonNegative obligations were generated (one per component)
    let nonneg_obligations: Vec<_> = ctx
        .obligations
        .iter()
        .filter(|o| matches!(o.kind, ObligationKind::MeasureNonNegative))
        .collect();
    assert_eq!(
        nonneg_obligations.len(),
        2,
        "Expected 2 MeasureNonNegative obligations (one per tuple component), got {}",
        nonneg_obligations.len()
    );

    // Verify each component is referenced
    let conditions: Vec<&str> = nonneg_obligations
        .iter()
        .map(|o| o.condition.as_str())
        .collect();
    assert!(
        conditions.iter().any(|c| c.contains("a")),
        "Should have nonneg for 'a', got: {:?}",
        conditions
    );
    assert!(
        conditions.iter().any(|c| c.contains("b")),
        "Should have nonneg for 'b', got: {:?}",
        conditions
    );
}

#[test]
fn test_source_extraction_decreases_preserves_nested_comma_tuple_component() {
    use crate::vc::VerificationContext;

    let markers = FunctionMarkers {
        requires: vec![],
        ensures: vec![],
        decreases: Some("(f(a, b), c)".to_string()),
    };

    let func: syn::ItemFn = syn::parse_quote! {
        fn lex_countdown(a: i64, b: i64, c: i64) -> i64 { a + b + c }
    };

    let mut ctx = VerificationContext::new();
    let result = apply_markers_to_context(&mut ctx, "lex_countdown", &markers, &func);
    assert!(
        result.is_ok(),
        "nested-comma tuple should parse cleanly, got: {:?}",
        result
    );

    let nonneg_conditions: Vec<String> = ctx
        .obligations
        .iter()
        .filter(|o| matches!(o.kind, ObligationKind::MeasureNonNegative))
        .map(|o| compact(&o.condition))
        .collect();

    assert_eq!(
        nonneg_conditions.len(),
        2,
        "nested-comma tuple should split into two components, got {:?}",
        nonneg_conditions
    );
    assert!(
        nonneg_conditions.contains(&"f(a,b)>=0".to_string()),
        "first component should preserve nested comma, got {:?}",
        nonneg_conditions
    );
    assert!(
        nonneg_conditions.contains(&"c>=0".to_string()),
        "second component should remain intact, got {:?}",
        nonneg_conditions
    );
}

#[test]
fn test_source_extraction_parenthesized_nested_comma_as_single_measure() {
    use crate::vc::VerificationContext;

    let markers = FunctionMarkers {
        requires: vec![],
        ensures: vec![],
        decreases: Some("(f(a, b))".to_string()),
    };

    let func: syn::ItemFn = syn::parse_quote! {
        fn countdown(a: i64, b: i64) -> i64 { a + b }
    };

    let mut ctx = VerificationContext::new();
    let result = apply_markers_to_context(&mut ctx, "countdown", &markers, &func);
    assert!(
        result.is_ok(),
        "parenthesized singleton should stay a single measure, got: {:?}",
        result
    );

    let nonneg_conditions: Vec<String> = ctx
        .obligations
        .iter()
        .filter(|o| matches!(o.kind, ObligationKind::MeasureNonNegative))
        .map(|o| compact(&o.condition))
        .collect();

    assert_eq!(
        nonneg_conditions,
        vec!["(f(a,b))>=0".to_string()],
        "source extraction should preserve parenthesized singleton measures, got {:?}",
        nonneg_conditions
    );
}

#[test]
fn test_source_extraction_decreases_preserves_struct_literal_tuple_component() {
    use crate::vc::VerificationContext;

    let markers = FunctionMarkers {
        requires: vec![],
        ensures: vec![],
        decreases: Some("(f(Foo { x: a, y: b }), c)".to_string()),
    };

    let func: syn::ItemFn = syn::parse_quote! {
        fn lex_countdown(a: i64, b: i64, c: i64) -> i64 { a + b + c }
    };

    let mut ctx = VerificationContext::new();
    let result = apply_markers_to_context(&mut ctx, "lex_countdown", &markers, &func);
    assert!(
        result.is_ok(),
        "struct-literal tuple should parse cleanly, got: {:?}",
        result
    );

    let nonneg_conditions: Vec<String> = ctx
        .obligations
        .iter()
        .filter(|o| matches!(o.kind, ObligationKind::MeasureNonNegative))
        .map(|o| compact(&o.condition))
        .collect();

    assert_eq!(
        nonneg_conditions.len(),
        2,
        "struct-literal tuple should split into two components, got {:?}",
        nonneg_conditions
    );
    assert!(
        nonneg_conditions.contains(&"f(Foo{x:a,y:b})>=0".to_string()),
        "first component should preserve struct literal commas, got {:?}",
        nonneg_conditions
    );
    assert!(
        nonneg_conditions.contains(&"c>=0".to_string()),
        "second component should remain intact, got {:?}",
        nonneg_conditions
    );
}

#[test]
fn test_source_extraction_decreases_preserves_shift_operator_tuple_component() {
    use crate::vc::VerificationContext;

    let markers = FunctionMarkers {
        requires: vec![],
        ensures: vec![],
        decreases: Some("(n >> 1, c)".to_string()),
    };

    let func: syn::ItemFn = syn::parse_quote! {
        fn lex_countdown(n: i64, c: i64) -> i64 { n + c }
    };

    let mut ctx = VerificationContext::new();
    let result = apply_markers_to_context(&mut ctx, "lex_countdown", &markers, &func);
    assert!(
        result.is_ok(),
        "shift-operator tuple should parse cleanly, got: {:?}",
        result
    );

    let nonneg_conditions: Vec<String> = ctx
        .obligations
        .iter()
        .filter(|o| matches!(o.kind, ObligationKind::MeasureNonNegative))
        .map(|o| compact(&o.condition))
        .collect();

    assert_eq!(
        nonneg_conditions.len(),
        2,
        "shift-operator tuple should split into two components, got {:?}",
        nonneg_conditions
    );
    assert!(
        nonneg_conditions.contains(&"n>>1>=0".to_string()),
        "first component should preserve the shift expression, got {:?}",
        nonneg_conditions
    );
    assert!(
        nonneg_conditions.contains(&"c>=0".to_string()),
        "second component should remain intact, got {:?}",
        nonneg_conditions
    );
}

#[test]
fn test_source_extraction_decreases_rejects_numeric_literal() {
    // Invalid measure components (numeric literals) should return error,
    // matching the runtime path's panic behavior.
    use std::fs;
    use std::path::Path;

    let test_dir = Path::new("target/test_source_extraction_decreases_reject");
    fs::create_dir_all(test_dir).unwrap();
    let test_file = test_dir.join("decreases_invalid.rs");

    fs::write(
        &test_file,
        r#"
            #[__trust_vc_decreases = "5"]
            fn bad_measure(n: u64) -> u64 { n }
        "#,
    )
    .unwrap();

    let result = verify_markers_impl("test::decreases_invalid", test_file.to_str().unwrap());

    fs::remove_file(&test_file).ok();

    // Should fail with an error about invalid measure
    assert!(
        result.is_err(),
        "Numeric literal measure should be rejected, got: {:?}",
        result
    );
    let err = result.unwrap_err();
    assert!(
        err.contains("must reference a variable"),
        "Error should explain why measure is invalid, got: {}",
        err
    );
}

#[test]
fn test_source_extraction_decreases_rejects_numeric_tuple_component() {
    // Invalid tuple component should return error (not silently skip).
    use std::fs;
    use std::path::Path;

    let test_dir = Path::new("target/test_source_extraction_decreases_reject_tuple");
    fs::create_dir_all(test_dir).unwrap();
    let test_file = test_dir.join("decreases_bad_tuple.rs");

    fs::write(
        &test_file,
        r#"
            #[__trust_vc_decreases = "(n, 5)"]
            fn bad_tuple_measure(n: u64) -> u64 { n }
        "#,
    )
    .unwrap();

    let result = verify_markers_impl("test::decreases_bad_tuple", test_file.to_str().unwrap());

    fs::remove_file(&test_file).ok();

    // Should fail: "5" is a numeric literal, not a variable
    assert!(
        result.is_err(),
        "Numeric literal in tuple should be rejected, got: {:?}",
        result
    );
    let err = result.unwrap_err();
    assert!(
        err.contains("must reference a variable"),
        "Error should explain why component is invalid, got: {}",
        err
    );
}

#[test]
fn test_source_extraction_decreases_nonneg_counterexample() {
    // When no requires ensures n >= 0, MeasureNonNegative should fail
    // with a counterexample (n could be negative for signed types).
    use std::fs;
    use std::path::Path;

    let test_dir = Path::new("target/test_source_extraction_decreases_cex");
    fs::create_dir_all(test_dir).unwrap();
    let test_file = test_dir.join("decreases_no_bound.rs");

    fs::write(
        &test_file,
        r#"
            #[__trust_vc_decreases = "n"]
            fn unconstrained(n: i64) -> i64 { n }
        "#,
    )
    .unwrap();

    let result = verify_markers_impl("test::decreases_cex", test_file.to_str().unwrap());

    fs::remove_file(&test_file).ok();

    // Should fail: n is unconstrained i64, could be negative
    assert!(
        result.is_err(),
        "Unconstrained signed measure should produce counterexample, got: {:?}",
        result
    );
}
