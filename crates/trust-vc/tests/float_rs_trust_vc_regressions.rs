// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Executable guards for the upstream float.rs TrustVc scout slice.
//!
//! These tests intentionally keep `source/rust_verify_test/tests/float.rs`
//! as an unsupported gap. They prove only the Rust-valid subset TrustVc can
//! express today: deterministic finite float arithmetic/comparison, Rust cast
//! self-consistency, executable `f32_ieee` true-fact surrogates, stable false
//! literal/guarded cast-comparison probes, and direct f32 method/f16 uses as
//! fail-closed boundaries for the upstream bit/spec/unsupported-cast surface.

mod common;

use std::{
    collections::{BTreeMap, BTreeSet},
    path::{Path, PathBuf},
};
use trust_vc_core::{verify_function_from_file, VerifyResult};

#[derive(Debug, Eq, PartialEq)]
struct CaseMetadata {
    case_id: String,
    upstream_case_id: String,
    expected_verdict: String,
    min_obligations: usize,
    expected_error_patterns: Vec<String>,
}

fn float_port_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/ported/float.rs")
}

fn pinned_upstream_float_path() -> PathBuf {
    common::pinned_verus_test_path("float.rs")
}

fn verus_manifest_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/verus-tests.json")
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

fn expect_error_contains_any(
    path: &str,
    case: &str,
    upstream_case: &str,
    expected_fragments: &[&str],
) {
    let result = verify_fail_closed(path, case);
    eprintln!("{case} ({upstream_case}) => {result:?}");
    let message = match result {
        VerifyResult::Error { message } => message,
        VerifyResult::Unknown { reason, .. } => {
            panic!("{case} ({upstream_case}) returned solver Unknown, which is not stable evidence: {reason}")
        }
        other => {
            panic!("{case} ({upstream_case}) should fail closed with Error, got: {other:?}")
        }
    };

    assert!(
        expected_fragments
            .iter()
            .any(|expected_fragment| message.contains(expected_fragment)),
        "{case} ({upstream_case}) error should contain one of {expected_fragments:?}, got: {message}"
    );
}

const VERIFIED_CASES: &[(&str, &str)] = &[
    (
        "float_int_and_float_cast_self_consistency_verified",
        "int_to_f64_cast/int_to_f32_cast/float_to_float_cast Rust-valid cast theme",
    ),
    (
        "finite_float_casted_arithmetic_comparison_verified",
        "f32_ieee finite casted arithmetic/comparison true fact",
    ),
    (
        "f32_ieee_guarded_double_upper_bound_verified",
        "f32_ieee/test1 bounded double upper bound",
    ),
    (
        "f32_ieee_literal_add_commutes_verified",
        "f32_ieee/test1 literal addition commutativity",
    ),
    (
        "f32_ieee_literal_cast_equivalences_verified",
        "f32_ieee/test1 literal f32/u8/f64 cast facts",
    ),
    (
        "same_type_f64_literal_cast_identity_verified",
        "cast_same_float_identity",
    ),
    (
        "float_to_int_literal_round_trip_verified",
        "f64_to_int_cast Rust-valid literal cast theme",
    ),
    (
        "float_to_int_f32_i64_literal_round_trip_verified",
        "f32_to_int_cast Rust-valid literal cast theme",
    ),
    (
        "f32_clone_method_verified",
        "f32_basics non-NaN clone boundary",
    ),
];

const COUNTEREXAMPLE_CASES: &[(&str, &str)] = &[
    (
        "finite_float_casted_arithmetic_false_target_counterexample",
        "f32_ieee/test2 false finite casted arithmetic/comparison probe",
    ),
    (
        "f32_ieee_guarded_double_upper_bound_false_counterexample",
        "f32_ieee/test2 false guarded double upper bound",
    ),
    (
        "f32_ieee_guarded_add_wrong_sum_counterexample",
        "f32_ieee/test3 false guarded sum equality",
    ),
    (
        "float_to_int_literal_false_target_counterexample",
        "f32_ieee/test6 false float-to-int literal cast equality probe",
    ),
    (
        "float_int_to_float_false_target_counterexample",
        "f32_ieee/test7 false int-to-float literal cast equality probe",
    ),
    (
        "f64_to_f32_literal_false_target_counterexample",
        "f32_ieee/test8 false f64-to-f32 literal cast equality probe",
    ),
    (
        "f32_to_f64_literal_false_target_counterexample",
        "f32_ieee/test9 false f32-to-f64 literal cast equality probe",
    ),
];

const FAIL_CLOSED_CASES: &[(&str, &str, &[&str])] = &[
    (
        "f32_is_finite_method_currently_blocked",
        "f32_basics is_finite_spec boundary",
        &[
            "is_finite() on type `f32`",
            "is_finite",
            "unsupported method",
        ],
    ),
    (
        "float_to_bits_method_currently_blocked",
        "f32_basics f32_to_bits boundary",
        &["to_bits() on type `f32`", "to_bits", "unsupported method"],
    ),
    (
        "cast_int_to_f16_currently_blocked",
        "cast_int_to_f16_unsupported",
        &["f16", "unknown type", "unsupported"],
    ),
    (
        "cast_f16_to_int_currently_blocked",
        "cast_f16_to_int_unsupported",
        &["f16", "unknown type", "unsupported"],
    ),
    (
        "cast_f16_to_f64_currently_blocked",
        "cast_f16_to_f64_unsupported",
        &["f16", "unknown type", "unsupported"],
    ),
];

fn referenced_array_const(file: &syn::File, const_name: &str) -> syn::ExprArray {
    let const_item = file
        .items
        .iter()
        .find_map(|item| match item {
            syn::Item::Const(item) if item.ident == const_name => Some(item),
            _ => None,
        })
        .unwrap_or_else(|| panic!("float port should define {const_name}"));

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
    let array = referenced_array_const(file, "FLOAT_RS_EXPECTED_ERROR_PATTERNS");
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
    let array = referenced_array_const(file, "FLOAT_RS_EXPECTED_CASES");
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
            "duplicate float metadata for {case_id}"
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
    let verified = VERIFIED_CASES
        .iter()
        .map(|(case_id, upstream_case_id)| CaseMetadata {
            case_id: (*case_id).to_string(),
            upstream_case_id: (*upstream_case_id).to_string(),
            expected_verdict: "verified".to_string(),
            min_obligations: 1,
            expected_error_patterns: Vec::new(),
        });
    let counterexamples = COUNTEREXAMPLE_CASES
        .iter()
        .map(|(case_id, upstream_case_id)| CaseMetadata {
            case_id: (*case_id).to_string(),
            upstream_case_id: (*upstream_case_id).to_string(),
            expected_verdict: "counterexample".to_string(),
            min_obligations: 1,
            expected_error_patterns: Vec::new(),
        });
    let errors =
        FAIL_CLOSED_CASES
            .iter()
            .map(
                |(case_id, upstream_case_id, expected_error_patterns)| CaseMetadata {
                    case_id: (*case_id).to_string(),
                    upstream_case_id: (*upstream_case_id).to_string(),
                    expected_verdict: "error".to_string(),
                    min_obligations: 0,
                    expected_error_patterns: expected_error_patterns
                        .iter()
                        .map(|pattern| (*pattern).to_string())
                        .collect(),
                },
            );

    verified.chain(counterexamples).chain(errors).collect()
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
            entry["upstream_path"].as_str() == Some("source/rust_verify_test/tests/float.rs")
        })
        .expect("Verus manifest should contain float.rs row");

    row["expected_cases"]
        .as_array()
        .expect("float manifest row should contain expected_cases")
        .iter()
        .map(|case| CaseMetadata {
            case_id: case["case_id"]
                .as_str()
                .expect("manifest case should contain case_id")
                .to_string(),
            upstream_case_id: case
                .get("upstream_case_id")
                .and_then(serde_json::Value::as_str)
                .unwrap_or("")
                .to_string(),
            expected_verdict: case["expected_verdict"]
                .as_str()
                .expect("manifest case should contain expected_verdict")
                .to_string(),
            min_obligations: case["min_obligations"]
                .as_u64()
                .expect("manifest case should contain min_obligations")
                .try_into()
                .expect("min_obligations should fit usize"),
            expected_error_patterns: case["expected_error_patterns"]
                .as_array()
                .map(|patterns| {
                    patterns
                        .iter()
                        .map(|pattern| {
                            pattern
                                .as_str()
                                .expect("expected_error_patterns entries should be strings")
                                .to_string()
                        })
                        .collect()
                })
                .unwrap_or_default(),
        })
        .collect()
}

#[test]
fn float_rs_port_file_is_rust_syntax() {
    let source = std::fs::read_to_string(float_port_path()).expect("float port should be readable");
    syn::parse_file(&source).expect("float port should parse as ordinary Rust syntax");
}

#[test]
fn float_rs_pinned_upstream_case_shapes_are_present() {
    let path = pinned_upstream_float_path();
    if !path.exists() {
        eprintln!(
            "skipping pinned upstream float.rs shape check; missing {}",
            path.display()
        );
        return;
    }

    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", path.display()));
    for expected in [
        "#[test] f32_basics",
        "#[test] int_to_f64_cast",
        "#[test] int_to_f32_cast",
        "#[test] f64_to_int_cast",
        "#[test] f32_to_int_cast",
        "#[test] float_to_float_cast",
        "#[test] cast_nondeterministic_fail",
        "#[test] cast_same_float_identity",
        "#[test] cast_usize_to_f64_unsupported",
        "#[test] cast_f64_to_isize_unsupported",
        "#[test] cast_int_to_f16_unsupported",
        "#[test] cast_f16_to_int_unsupported",
        "#[test] cast_f16_to_f64_unsupported",
        "#[test] f32_ieee",
        "assert(p0 == p1)",
        "x + x <= 10.0f32",
        "x + y == y + x",
        "4f32 as u8 == 4u8",
        "4f32 == 5f64 as f32",
        "f32_to_bits(-0.0f32)",
    ] {
        assert!(
            source.contains(expected),
            "pinned upstream float.rs should still contain {expected}"
        );
    }
}

#[test]
fn float_rs_expected_case_metadata_is_exact() {
    let source = std::fs::read_to_string(float_port_path()).expect("float port should be readable");
    let file = syn::parse_file(&source).expect("float port should parse as ordinary Rust syntax");
    assert!(
        source.contains("pub const FLOAT_RS_EXPECTED_CASES")
            && source.contains("pub fn float_rs_expected_cases")
            && source.contains("pub const FLOAT_RS_EXPECTED_ERROR_PATTERNS")
            && source.contains("pub fn float_rs_expected_error_patterns"),
        "float port should expose expected-case metadata helpers"
    );
    assert_eq!(metadata_entries(&file), expected_metadata());
}

#[test]
fn float_rs_expected_case_metadata_matches_manifest() {
    let source = std::fs::read_to_string(float_port_path()).expect("float port should be readable");
    let file = syn::parse_file(&source).expect("float port should parse as ordinary Rust syntax");
    assert_eq!(
        metadata_entries(&file),
        manifest_expected_metadata(),
        "float manifest expected_cases should match port metadata exactly"
    );
}

#[test]
fn float_rs_verified_subset_verifies_from_file() {
    let path = float_port_path();
    let path = path.to_str().expect("float port path should be UTF-8");

    for (case, upstream_case) in VERIFIED_CASES {
        let result = verify_case(path, case, upstream_case);
        assert!(
            matches!(result, VerifyResult::Verified),
            "{case} ({upstream_case}) should verify, got: {result:?}"
        );
    }
}

#[test]
fn float_rs_stable_false_target_cast_counterexamples_from_file() {
    let path = float_port_path();
    let path = path.to_str().expect("float port path should be UTF-8");

    for (case, upstream_case) in COUNTEREXAMPLE_CASES {
        let result = verify_case(path, case, upstream_case);
        eprintln!("{case} ({upstream_case}) => {result:?}");
        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "{case} ({upstream_case}) should produce Counterexample, got: {result:?}"
        );
    }
}

#[test]
fn float_rs_unsupported_float_boundaries_fail_closed_from_file() {
    let path = float_port_path();
    let path = path.to_str().expect("float port path should be UTF-8");

    for (case, upstream_case, expected_fragments) in FAIL_CLOSED_CASES {
        expect_error_contains_any(path, case, upstream_case, expected_fragments);
    }
}
