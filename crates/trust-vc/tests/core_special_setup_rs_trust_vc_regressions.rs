// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Executable guards for the first upstream core_special_setup.rs TrustVc scout.
//!
//! These tests intentionally keep
//! `source/rust_verify_test/tests/core_special_setup.rs` as an unsupported gap.
//! They pin only stable TrustVc behavior available today: collection equality
//! precondition witnesses, a fixed borrowed-array view/index witness, a false
//! Seq index counterexample, and a fail-closed raw pointer cast-expression
//! boundary.

mod common;

use std::{
    collections::{BTreeMap, BTreeSet},
    path::{Path, PathBuf},
};
use trust_vc_core::{verify_function_from_file, VerifyResult};

fn core_special_setup_port_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/ported/core_special_setup.rs")
}

fn verus_manifest_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/verus-tests.json")
}

fn pinned_upstream_core_special_setup_path() -> PathBuf {
    common::pinned_verus_test_path("core_special_setup.rs")
}

fn verify_case(path: &str, case: &str, upstream_case: &str) -> VerifyResult {
    verify_function_from_file(path, case)
        .unwrap_or_else(|err| panic!("{case} ({upstream_case}) should extract: {err}"))
}

fn expect_fail_closed(path: &str, case: &str, upstream_case: &str, expected_terms: &[&str]) {
    let message = match verify_function_from_file(path, case) {
        Err(err) => err.to_string(),
        Ok(VerifyResult::Error { message }) => message,
        Ok(other) => {
            panic!("{case} ({upstream_case}) should fail closed with Error, got: {other:?}")
        }
    };

    assert!(
        expected_terms.iter().any(|term| message.contains(term)),
        "{case} ({upstream_case}) should report one of {expected_terms:?}, got: {message}"
    );
}

const VERIFIED_CASES: &[(&str, &str)] = &[
    (
        "core_special_setup_seq_equality_verified",
        "test_is_core::test_seqs",
    ),
    (
        "core_special_setup_set_equality_verified",
        "test_is_core::test_sets",
    ),
    (
        "core_special_setup_multiset_equality_verified",
        "test_is_core::test_multisets",
    ),
    (
        "core_special_setup_slice_view_index_verified",
        "test_is_core::test_slice_index fixed-view subset",
    ),
];

const COUNTEREXAMPLE_CASES: &[(&str, &str)] = &[(
    "core_special_setup_seq_wrong_index_counterexample",
    "test_is_core collection equality false-adjacent assertion",
)];

const FAIL_CLOSED_CASES: &[(&str, &str, &[&str])] = &[(
    "core_special_setup_raw_pointer_cast_currently_blocked",
    "test_is_core::test_ptr_stuff raw pointer cast-expression boundary",
    &["unsupported", "*mut", "cast"],
)];

const EXPECTED_CASES: &[(&str, &str, &str, usize)] = &[
    (
        "core_special_setup_seq_equality_verified",
        "test_is_core",
        "verified",
        1,
    ),
    (
        "core_special_setup_set_equality_verified",
        "test_is_core",
        "verified",
        1,
    ),
    (
        "core_special_setup_multiset_equality_verified",
        "test_is_core",
        "verified",
        1,
    ),
    (
        "core_special_setup_slice_view_index_verified",
        "test_is_core",
        "verified",
        2,
    ),
    (
        "core_special_setup_seq_wrong_index_counterexample",
        "test_is_core",
        "counterexample",
        1,
    ),
    (
        "core_special_setup_raw_pointer_cast_currently_blocked",
        "test_is_core",
        "error",
        0,
    ),
];

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
        .unwrap_or_else(|| panic!("core_special_setup port should define {const_name}"));

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
    let array = referenced_array_const(file, "CORE_SPECIAL_SETUP_RS_FAIL_CLOSED_ERROR_PATTERNS");
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
    let array = referenced_array_const(file, "CORE_SPECIAL_SETUP_RS_EXPECTED_CASES");
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
            "duplicate core_special_setup metadata for {case_id}"
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
    let mut error_patterns = BTreeMap::from([(
        "core_special_setup_raw_pointer_cast_currently_blocked",
        vec![
            "unsupported".to_string(),
            "*mut".to_string(),
            "cast".to_string(),
        ],
    )]);

    EXPECTED_CASES
        .iter()
        .map(
            |(case_id, upstream_case_id, expected_verdict, min_obligations)| CaseMetadata {
                case_id: (*case_id).to_string(),
                upstream_case_id: (*upstream_case_id).to_string(),
                expected_verdict: (*expected_verdict).to_string(),
                min_obligations: *min_obligations,
                expected_error_patterns: error_patterns.remove(case_id).unwrap_or_default(),
            },
        )
        .collect()
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
            entry["upstream_path"].as_str()
                == Some("source/rust_verify_test/tests/core_special_setup.rs")
        })
        .expect("Verus manifest should contain core_special_setup.rs row");

    row["expected_cases"]
        .as_array()
        .expect("core_special_setup.rs row should contain expected_cases")
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
fn core_special_setup_rs_port_file_is_rust_syntax() {
    let source = std::fs::read_to_string(core_special_setup_port_path())
        .expect("core_special_setup port should be readable");
    syn::parse_file(&source).expect("core_special_setup port should parse as ordinary Rust syntax");
}

#[test]
fn core_special_setup_rs_pinned_upstream_case_shapes_are_present() {
    let path = pinned_upstream_core_special_setup_path();
    if !path.exists() {
        eprintln!(
            "skipping pinned upstream core_special_setup.rs shape check; missing {}",
            path.display()
        );
        return;
    }

    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", path.display()));
    for expected in [
        "--is-core",
        "no-auto-import-verus_builtin",
        "assert_seqs_equal!",
        "assert_sets_equal!",
        "assert_multisets_equal!",
        "fn test_slice_index",
        "fn test_ptr_stuff",
    ] {
        assert!(
            source.contains(expected),
            "pinned upstream core_special_setup.rs should still contain {expected}"
        );
    }
}

#[test]
fn core_special_setup_rs_expected_case_metadata_is_exact() {
    let source = std::fs::read_to_string(core_special_setup_port_path())
        .expect("core_special_setup port should be readable");
    let file = syn::parse_file(&source)
        .expect("core_special_setup port should parse as ordinary Rust syntax");
    assert_eq!(metadata_entries(&file), expected_metadata());
    assert!(
        source.contains("core_special_setup_rs_fail_closed_error_patterns"),
        "core_special_setup port should export fail-closed error-pattern metadata"
    );
}

#[test]
fn core_special_setup_rs_expected_case_metadata_matches_manifest() {
    let source = std::fs::read_to_string(core_special_setup_port_path())
        .expect("core_special_setup port should be readable");
    let file = syn::parse_file(&source)
        .expect("core_special_setup port should parse as ordinary Rust syntax");
    assert_eq!(metadata_entries(&file), manifest_expected_metadata());
}

#[test]
fn core_special_setup_rs_verified_subset_verifies_from_file() {
    let path = core_special_setup_port_path();
    let path = path
        .to_str()
        .expect("core_special_setup port path should be UTF-8");

    for (case, upstream_case) in VERIFIED_CASES {
        let result = verify_case(path, case, upstream_case);
        assert!(
            matches!(result, VerifyResult::Verified),
            "{case} ({upstream_case}) should verify, got: {result:?}"
        );
    }
}

#[test]
fn core_special_setup_rs_counterexample_subset_is_rejected_from_file() {
    let path = core_special_setup_port_path();
    let path = path
        .to_str()
        .expect("core_special_setup port path should be UTF-8");

    for (case, upstream_case) in COUNTEREXAMPLE_CASES {
        let result = verify_case(path, case, upstream_case);
        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "{case} ({upstream_case}) should produce a counterexample, got: {result:?}"
        );
    }
}

#[test]
fn core_special_setup_rs_raw_pointer_cast_fails_closed_from_file() {
    let path = core_special_setup_port_path();
    let path = path
        .to_str()
        .expect("core_special_setup port path should be UTF-8");

    for (case, upstream_case, expected_terms) in FAIL_CLOSED_CASES {
        expect_fail_closed(path, case, upstream_case, expected_terms);
    }
}
