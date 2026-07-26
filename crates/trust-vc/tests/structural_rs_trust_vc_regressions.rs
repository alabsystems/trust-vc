// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Executable guards for the first upstream structural.rs TrustVc scout slice.
//!
//! These tests intentionally keep `source/rust_verify_test/tests/structural.rs`
//! fail-closed in the manifest. They prove only the Rust-valid subset TrustVc can
//! express today: field-level structural equality over the upstream Car shape,
//! direct derived PartialEq equality for the same shape, wildcard enum payload
//! matches, fieldless explicit-value enums, false equality probes, and an
//! unsupported custom PartialEq boundary that must not silently verify.

mod common;

use std::{
    collections::{BTreeMap, BTreeSet},
    path::{Path, PathBuf},
};
use trust_vc_core::{verify_function_from_file, VerifyResult};

fn structural_port_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/ported/structural.rs")
}

fn verus_manifest_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/verus-tests.json")
}

fn pinned_upstream_structural_path() -> PathBuf {
    common::pinned_verus_test_path("structural.rs")
}

fn verify_case(path: &str, case: &str, upstream_case: &str) -> VerifyResult {
    verify_function_from_file(path, case)
        .unwrap_or_else(|err| panic!("{case} ({upstream_case}) should extract: {err}"))
}

fn verify_fail_closed(path: &str, case: &str) -> VerifyResult {
    verify_function_from_file(path, case).unwrap_or_else(|err| VerifyResult::Error {
        message: err.to_string(),
    })
}

const VERIFIED_CASES: &[(&str, &str)] = &[
    (
        "structural_car_field_equality_verified",
        "test_structural_eq",
    ),
    (
        "structural_car_direct_derived_partial_eq_verified",
        "test_structural_eq",
    ),
    (
        "structural_vehicle_direct_derived_partial_eq_verified",
        "test_structural_eq",
    ),
    (
        "structural_vehicle_wildcard_payload_match_verified",
        "test_structural_eq",
    ),
    (
        "structural_enum_value_status_derived_eq_verified",
        "test_structural_enum_with_values",
    ),
];

const COUNTEREXAMPLE_CASES: &[(&str, &str)] = &[
    (
        "structural_car_direct_derived_partial_eq_wrong_value",
        "test_structural_eq",
    ),
    (
        "structural_vehicle_direct_derived_partial_eq_wrong_variant",
        "test_structural_eq",
    ),
    (
        "structural_enum_value_status_wrong_value",
        "test_structural_enum_with_values",
    ),
];

const FAIL_CLOSED_CASES: &[(&str, &str)] = &[(
    "structural_manual_partial_eq_method_currently_blocked",
    "test_not_structural_generic",
)];

#[derive(Debug, Eq, PartialEq)]
struct CaseMetadata {
    case_id: String,
    upstream_case_id: String,
    expected_verdict: String,
    min_obligations: usize,
    expected_error_patterns: Vec<String>,
}

fn referenced_array_const(file: &syn::File, const_name: &str) -> syn::ExprArray {
    let const_item = file
        .items
        .iter()
        .find_map(|item| match item {
            syn::Item::Const(item) if item.ident == const_name => Some(item),
            _ => None,
        })
        .unwrap_or_else(|| panic!("structural port should define {const_name}"));

    let syn::Expr::Reference(reference) = const_item.expr.as_ref() else {
        panic!("{const_name} should be a referenced array");
    };
    let syn::Expr::Array(array) = reference.expr.as_ref() else {
        panic!("{const_name} should reference an array");
    };
    array.clone()
}

fn literal_string(expr: &syn::Expr) -> String {
    let syn::Expr::Lit(lit) = expr else {
        panic!("expected string literal");
    };
    let syn::Lit::Str(value) = &lit.lit else {
        panic!("expected string literal");
    };
    value.value()
}

fn literal_usize(expr: &syn::Expr) -> usize {
    let syn::Expr::Lit(lit) = expr else {
        panic!("expected integer literal");
    };
    let syn::Lit::Int(value) = &lit.lit else {
        panic!("expected integer literal");
    };
    value
        .base10_parse()
        .expect("min obligations should be a usize literal")
}

fn string_slice(expr: &syn::Expr) -> Vec<String> {
    let syn::Expr::Reference(reference) = expr else {
        panic!("expected referenced string-slice metadata");
    };
    let syn::Expr::Array(array) = reference.expr.as_ref() else {
        panic!("expected string-slice array metadata");
    };

    array.elems.iter().map(literal_string).collect()
}

fn error_pattern_entries(file: &syn::File) -> BTreeMap<String, Vec<String>> {
    let array = referenced_array_const(file, "STRUCTURAL_RS_EXPECTED_ERROR_PATTERNS");
    let mut entries = BTreeMap::new();

    for entry in &array.elems {
        let syn::Expr::Tuple(tuple) = entry else {
            panic!("expected tuple error-pattern metadata entry");
        };
        assert_eq!(
            tuple.elems.len(),
            2,
            "error-pattern entries should have case and fragments"
        );

        let case_id = literal_string(&tuple.elems[0]);
        let patterns = string_slice(&tuple.elems[1]);
        assert!(
            entries.insert(case_id.clone(), patterns).is_none(),
            "duplicate error-pattern metadata for {case_id}"
        );
    }

    entries
}

fn metadata_entries(file: &syn::File) -> Vec<CaseMetadata> {
    let array = referenced_array_const(file, "STRUCTURAL_RS_EXPECTED_CASES");
    let mut error_patterns = error_pattern_entries(file);
    let mut seen = BTreeSet::new();
    let mut entries = Vec::new();

    for entry in &array.elems {
        let syn::Expr::Tuple(tuple) = entry else {
            panic!("expected tuple expected-case metadata entry");
        };
        assert_eq!(
            tuple.elems.len(),
            4,
            "expected-case entries should have case, upstream case, verdict, and min obligations"
        );
        let case_id = literal_string(&tuple.elems[0]);
        assert!(
            seen.insert(case_id.clone()),
            "duplicate structural metadata for {case_id}"
        );
        let expected_error_patterns = error_patterns.remove(&case_id).unwrap_or_default();
        entries.push(CaseMetadata {
            case_id,
            upstream_case_id: literal_string(&tuple.elems[1]),
            expected_verdict: literal_string(&tuple.elems[2]),
            min_obligations: literal_usize(&tuple.elems[3]),
            expected_error_patterns,
        });
    }

    assert!(
        error_patterns.is_empty(),
        "error-pattern metadata should not contain orphan cases: {error_patterns:?}"
    );
    entries
}

fn expected_metadata() -> Vec<CaseMetadata> {
    vec![
        CaseMetadata {
            case_id: "structural_car_field_equality_verified".to_string(),
            upstream_case_id: "test_structural_eq".to_string(),
            expected_verdict: "verified".to_string(),
            min_obligations: 1,
            expected_error_patterns: Vec::new(),
        },
        CaseMetadata {
            case_id: "structural_car_direct_derived_partial_eq_verified".to_string(),
            upstream_case_id: "test_structural_eq".to_string(),
            expected_verdict: "verified".to_string(),
            min_obligations: 1,
            expected_error_patterns: Vec::new(),
        },
        CaseMetadata {
            case_id: "structural_vehicle_direct_derived_partial_eq_verified".to_string(),
            upstream_case_id: "test_structural_eq".to_string(),
            expected_verdict: "verified".to_string(),
            min_obligations: 1,
            expected_error_patterns: Vec::new(),
        },
        CaseMetadata {
            case_id: "structural_car_direct_derived_partial_eq_wrong_value".to_string(),
            upstream_case_id: "test_structural_eq".to_string(),
            expected_verdict: "counterexample".to_string(),
            min_obligations: 1,
            expected_error_patterns: Vec::new(),
        },
        CaseMetadata {
            case_id: "structural_vehicle_direct_derived_partial_eq_wrong_variant".to_string(),
            upstream_case_id: "test_structural_eq".to_string(),
            expected_verdict: "counterexample".to_string(),
            min_obligations: 1,
            expected_error_patterns: Vec::new(),
        },
        CaseMetadata {
            case_id: "structural_enum_value_status_derived_eq_verified".to_string(),
            upstream_case_id: "test_structural_enum_with_values".to_string(),
            expected_verdict: "verified".to_string(),
            min_obligations: 1,
            expected_error_patterns: Vec::new(),
        },
        CaseMetadata {
            case_id: "structural_enum_value_status_wrong_value".to_string(),
            upstream_case_id: "test_structural_enum_with_values".to_string(),
            expected_verdict: "counterexample".to_string(),
            min_obligations: 1,
            expected_error_patterns: Vec::new(),
        },
        CaseMetadata {
            case_id: "structural_manual_partial_eq_method_currently_blocked".to_string(),
            upstream_case_id: "test_not_structural_generic".to_string(),
            expected_verdict: "error".to_string(),
            min_obligations: 0,
            expected_error_patterns: vec!["unsupported method".to_string(), "eq()".to_string()],
        },
    ]
}

fn manifest_expected_metadata() -> Vec<CaseMetadata> {
    let source =
        std::fs::read_to_string(verus_manifest_path()).expect("Verus manifest should be readable");
    let manifest: serde_json::Value =
        serde_json::from_str(&source).expect("Verus manifest should parse as JSON");
    let row = manifest["entries"]
        .as_array()
        .expect("Verus manifest should contain entries")
        .iter()
        .find(|entry| {
            entry["upstream_path"].as_str() == Some("source/rust_verify_test/tests/structural.rs")
        })
        .expect("Verus manifest should contain structural.rs row");

    row["expected_cases"]
        .as_array()
        .expect("structural.rs row should contain expected_cases")
        .iter()
        .map(|entry| CaseMetadata {
            case_id: entry["case_id"]
                .as_str()
                .expect("case_id should be a string")
                .to_string(),
            upstream_case_id: entry["upstream_case_id"]
                .as_str()
                .expect("upstream_case_id should be a string")
                .to_string(),
            expected_verdict: entry["expected_verdict"]
                .as_str()
                .expect("expected_verdict should be a string")
                .to_string(),
            min_obligations: entry["min_obligations"]
                .as_u64()
                .expect("min_obligations should be an integer")
                as usize,
            expected_error_patterns: entry
                .get("expected_error_patterns")
                .and_then(serde_json::Value::as_array)
                .map(|patterns| {
                    patterns
                        .iter()
                        .map(|pattern| {
                            pattern
                                .as_str()
                                .expect("expected_error_patterns values should be strings")
                                .to_string()
                        })
                        .collect()
                })
                .unwrap_or_default(),
        })
        .collect()
}

#[test]
fn structural_rs_expected_case_metadata_is_exact() {
    let source = std::fs::read_to_string(structural_port_path())
        .expect("structural port should be readable");
    let file =
        syn::parse_file(&source).expect("structural port should parse as ordinary Rust syntax");
    assert_eq!(metadata_entries(&file), expected_metadata());
}

#[test]
fn structural_rs_expected_case_metadata_matches_manifest() {
    let source = std::fs::read_to_string(structural_port_path())
        .expect("structural port should be readable");
    let file =
        syn::parse_file(&source).expect("structural port should parse as ordinary Rust syntax");
    assert_eq!(metadata_entries(&file), manifest_expected_metadata());
}

#[test]
fn structural_rs_port_file_is_rust_syntax() {
    let source = std::fs::read_to_string(structural_port_path())
        .expect("structural port should be readable");
    syn::parse_file(&source).expect("structural port should parse as ordinary Rust syntax");
}

#[test]
fn structural_rs_pinned_upstream_case_shapes_are_present() {
    let path = pinned_upstream_structural_path();
    if !path.exists() {
        eprintln!(
            "skipping pinned upstream structural.rs shape check; missing {}",
            path.display()
        );
        return;
    }

    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", path.display()));
    for expected in [
        "#[test] test_structural_eq",
        "#[test] test_not_structural_generic",
        "#[test] test_not_structural_fields",
        "#[test] test_structural_enum_with_values",
        "#[test] test_structural_trait_bound",
    ] {
        assert!(
            source.contains(expected),
            "pinned upstream structural.rs should still contain {expected}"
        );
    }
}

#[test]
fn structural_rs_verified_subset_verifies_from_file() {
    let path = structural_port_path();
    let path = path.to_str().expect("structural port path should be UTF-8");

    for (case, upstream_case) in VERIFIED_CASES {
        let result = verify_case(path, case, upstream_case);
        assert!(
            matches!(result, VerifyResult::Verified),
            "{case} ({upstream_case}) should verify, got: {result:?}"
        );
    }
}

#[test]
fn structural_rs_false_equality_counterexamples_from_file() {
    let path = structural_port_path();
    let path = path.to_str().expect("structural port path should be UTF-8");

    for (case, upstream_case) in COUNTEREXAMPLE_CASES {
        let result = verify_case(path, case, upstream_case);
        eprintln!("{case} ({upstream_case}) => {result:?}");
        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "{case} ({upstream_case}) should produce a counterexample, got: {result:?}"
        );
    }
}

#[test]
fn structural_rs_unsupported_boundaries_fail_closed_from_file() {
    let path = structural_port_path();
    let path = path.to_str().expect("structural port path should be UTF-8");

    for (case, upstream_case) in FAIL_CLOSED_CASES {
        let result = verify_fail_closed(path, case);
        eprintln!("{case} ({upstream_case}) => {result:?}");
        assert!(
            !matches!(result, VerifyResult::Verified),
            "{case} ({upstream_case}) should fail closed until unsupported structural surfaces are modeled, got: {result:?}"
        );
    }
}
