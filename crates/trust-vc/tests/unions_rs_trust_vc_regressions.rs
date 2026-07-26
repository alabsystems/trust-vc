// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Executable guards for the first upstream unions.rs TrustVc scout.
//!
//! These tests intentionally keep `source/rust_verify_test/tests/unions.rs` as
//! an unsupported gap. They pin only stable tagged-surrogate executable
//! behavior, one inactive-field counterexample, and fail-closed native
//! union/Verus helper boundaries. Solver `Unknown` outcomes are not accepted as
//! evidence.

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

fn unions_port_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/ported/unions.rs")
}

fn verus_manifest_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/verus-tests.json")
}

fn pinned_upstream_unions_path() -> PathBuf {
    common::pinned_verus_test_path("unions.rs")
}

fn verify_case(path: &str, case: &str, upstream_case: &str) -> VerifyResult {
    verify_function_from_file(path, case)
        .unwrap_or_else(|err| panic!("{case} ({upstream_case}) should extract: {err}"))
}

fn expect_fail_closed_error_contains_any(
    path: &str,
    case: &str,
    upstream_case: &str,
    expected_fragments: &[&str],
) {
    let message = match verify_function_from_file(path, case) {
        Err(err) => err.to_string(),
        Ok(VerifyResult::Error { message }) => message,
        Ok(VerifyResult::Unknown { reason, .. }) => {
            panic!("{case} ({upstream_case}) returned solver Unknown, which is not stable evidence: {reason}")
        }
        Ok(other) => {
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
        "unions_tagged_x_basic_verified",
        "union_basic::test_ok x-active field-read surrogate",
    ),
    (
        "unions_type_alias_x_constructor_verified",
        "union_basic::test_type_alias x-active constructor surrogate",
    ),
    (
        "unions_generic_tagged_x_verified",
        "union_generics::test_ok generic x-active surrogate",
    ),
];

const COUNTEREXAMPLE_CASES: &[(&str, &str)] = &[(
    "unions_inactive_y_counterexample",
    "union_basic::test_fail wrong y-field read surrogate",
)];

const FAIL_CLOSED_CASES: &[(&str, &str, &[&str])] = &[
    (
        "unions_native_field_read_currently_blocked",
        "union_basic::test_ok native union field-read boundary",
        &["unsafe block", "unknown type", "unsupported"],
    ),
    (
        "unions_native_pattern_currently_blocked",
        "union_pattern::test_fail native union pattern boundary",
        &[
            "unsafe block",
            "using a union",
            "unsupported",
            "unresolved variable `x`",
        ],
    ),
    (
        "unions_get_union_field_currently_blocked",
        "get_union_field_bad_field_name Verus builtin boundary",
        &["string literals are not yet supported", "get_union_field"],
    ),
    (
        "unions_is_variant_currently_blocked",
        "union_basic::test_ok is_variant builtin boundary",
        &["string literals are not yet supported", "is_variant"],
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
        .unwrap_or_else(|| panic!("unions port should define {const_name}"));

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
    let array = referenced_array_const(file, "UNIONS_RS_EXPECTED_ERROR_PATTERNS");
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
    let array = referenced_array_const(file, "UNIONS_RS_EXPECTED_CASES");
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
            "duplicate unions metadata for {case_id}"
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
            entry["upstream_path"].as_str() == Some("source/rust_verify_test/tests/unions.rs")
        })
        .expect("Verus manifest should contain unions.rs row");

    row["expected_cases"]
        .as_array()
        .expect("unions.rs row should contain expected_cases")
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
fn unions_rs_port_file_is_rust_syntax() {
    let source =
        std::fs::read_to_string(unions_port_path()).expect("unions port should be readable");
    syn::parse_file(&source).expect("unions port should parse as ordinary Rust syntax");
}

#[test]
fn unions_rs_pinned_upstream_case_shapes_are_present() {
    let path = pinned_upstream_unions_path();
    if !path.exists() {
        eprintln!(
            "skipping pinned upstream unions.rs shape check; missing {}",
            path.display()
        );
        return;
    }

    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", path.display()));
    for expected in [
        "#[test] union_basic",
        "#[test] union_pattern",
        "#[test] union_mut_assign",
        "#[test] union_mut_ref",
        "#[test] get_union_field_non_union",
        "#[test] get_union_field_bad_field_name",
        "#[test] get_union_field_bad_field_type",
        "#[test] union_generics",
        "#[test] union_proof_mode",
        "#[test] union_field_access_in_spec_func",
        "#[test] visibility",
        "#[test] visibility2",
    ] {
        assert!(
            source.contains(expected),
            "pinned upstream unions.rs should still contain {expected}"
        );
    }
}

#[test]
fn unions_rs_expected_case_metadata_is_exact() {
    let source =
        std::fs::read_to_string(unions_port_path()).expect("unions port should be readable");
    let file = syn::parse_file(&source).expect("unions port should parse as ordinary Rust");
    assert_eq!(metadata_entries(&file), manifest_expected_metadata());
}

#[test]
fn unions_rs_expected_case_metadata_matches_manifest() {
    let source =
        std::fs::read_to_string(unions_port_path()).expect("unions port should be readable");
    let file = syn::parse_file(&source).expect("unions port should parse as ordinary Rust");
    assert_eq!(metadata_entries(&file), manifest_expected_metadata());
}

#[test]
fn unions_rs_verified_subset_verifies_from_file() {
    let path = unions_port_path();
    let path = path.to_str().expect("unions port path should be UTF-8");

    for (case, upstream_case) in VERIFIED_CASES {
        let result = verify_case(path, case, upstream_case);
        assert!(
            matches!(result, VerifyResult::Verified),
            "{case} ({upstream_case}) should verify, got: {result:?}"
        );
    }
}

#[test]
fn unions_rs_inactive_field_assertion_is_rejected_from_file() {
    let path = unions_port_path();
    let path = path.to_str().expect("unions port path should be UTF-8");

    for (case, upstream_case) in COUNTEREXAMPLE_CASES {
        let result = verify_case(path, case, upstream_case);
        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "{case} ({upstream_case}) should produce a counterexample, got: {result:?}"
        );
    }
}

#[test]
fn unions_rs_native_union_boundaries_fail_closed_from_file() {
    let path = unions_port_path();
    let path = path.to_str().expect("unions port path should be UTF-8");

    for (case, upstream_case, expected_fragments) in FAIL_CLOSED_CASES {
        expect_fail_closed_error_contains_any(path, case, upstream_case, expected_fragments);
    }
}
