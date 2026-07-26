// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Executable guards for the current upstream lifetime.rs TrustVc scout slice.
//!
//! These tests intentionally keep `source/rust_verify_test/tests/lifetime.rs`
//! unsupported-gap in manifest evidence. They pin only the Rust-valid TrustVc
//! subset in the ported file, stable counterexamples, upstream source-shape
//! anchors, and fail-closed unsupported mutable-reference boundaries.

mod common;

use std::{
    collections::{BTreeMap, BTreeSet},
    path::{Path, PathBuf},
};
use trust_vc_core::{
    extract_verification_conditions_with_file_context, verify_function_from_file, VerifyResult,
};

fn lifetime_port_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/ported/lifetime.rs")
}

fn verus_manifest_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/verus-tests.json")
}

fn pinned_upstream_lifetime_path() -> PathBuf {
    common::pinned_verus_test_path("lifetime.rs")
}

fn verify_port_case(case: &str, upstream_case: &str) -> (VerifyResult, usize) {
    let path = lifetime_port_path();
    let path_str = path.to_str().expect("lifetime port path should be UTF-8");

    let result = verify_function_from_file(path_str, case)
        .unwrap_or_else(|err| panic!("{case} ({upstream_case}) should extract: {err}"));

    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|err| panic!("{} should be readable: {err}", path.display()));
    let file = syn::parse_file(&source)
        .unwrap_or_else(|err| panic!("{} should parse as Rust syntax: {err}", path.display()));
    let func = file
        .items
        .iter()
        .find_map(|item| match item {
            syn::Item::Fn(func) if func.sig.ident == case => Some(func),
            _ => None,
        })
        .unwrap_or_else(|| {
            panic!(
                "{case} ({upstream_case}) should exist in {}",
                path.display()
            )
        });
    let vc = extract_verification_conditions_with_file_context(&file, func)
        .unwrap_or_else(|err| panic!("{case} ({upstream_case}) should extract VCs: {err}"));

    (result, vc.obligations().len())
}

fn expect_fail_closed_error_contains(
    path: &str,
    case: &str,
    upstream_case: &str,
    expected_fragments: &[&str],
) {
    let message = match verify_function_from_file(path, case) {
        Err(err) => err.to_string(),
        Ok(VerifyResult::Error { message }) => message,
        Ok(VerifyResult::Unknown { reason, .. }) => {
            panic!(
                "{case} ({upstream_case}) returned solver Unknown, which is not stable evidence: {reason}"
            )
        }
        Ok(other) => {
            panic!("{case} ({upstream_case}) should fail closed with Error, got: {other:?}")
        }
    };

    for expected_fragment in expected_fragments {
        assert!(
            message.contains(expected_fragment),
            "{case} ({upstream_case}) error should contain {expected_fragment:?}, got: {message}"
        );
    }
}

const VERIFIED_CASES: &[(&str, &str, usize)] = &[
    ("lifetime_consume_once", "consume_once", 1),
    ("lifetime_consume_fields_ok", "consume_fields_ok", 1),
    (
        "lifetime_borrow_two_distinct_locals_ok",
        "borrow_local_ok",
        1,
    ),
    ("lifetime_sequential_mutable_borrows_ok", "", 1),
    (
        "lifetime_return_ref_named_identity",
        "return_wrong_lifetime1",
        1,
    ),
    (
        "lifetime_return_ref_named_identity_caller",
        "return_wrong_lifetime1",
        1,
    ),
    ("lifetime_shared_ref_read_verified", "", 1),
    ("lifetime_copy_payload_reuse_ok", "lifetime_copy_succeed", 1),
    ("lifetime_mutable_reference_scalar_write_verified", "", 1),
    (
        "lifetime_mutable_reference_write_currently_blocked",
        "tracked_borrow_mut_assignment",
        1,
    ),
    (
        "lifetime_compound_mutable_reference_assignment_verified",
        "",
        4,
    ),
];

const COUNTEREXAMPLE_CASES: &[(&str, &str, usize)] = &[
    ("lifetime_false_assert_counterexample", "two_phase", 1),
    ("lifetime_assign_twice_false_tail_counterexample", "", 1),
    (
        "lifetime_mutable_reference_scalar_write_false_tail_counterexample",
        "",
        1,
    ),
];

const FAIL_CLOSED_CASES: &[(&str, &str, &[&str])] = &[(
    "lifetime_ref_holder_named_identity_currently_blocked",
    "",
    &["field 'value'", "specification context"],
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
        .unwrap_or_else(|| panic!("lifetime port should define {const_name}"));

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
    let array = referenced_array_const(file, "LIFETIME_RS_FAIL_CLOSED_ERROR_PATTERNS");
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
    let array = referenced_array_const(file, "LIFETIME_RS_EXPECTED_CASES");
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
            "duplicate lifetime metadata for {case_id}"
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
    let mut expected_by_case = BTreeMap::new();

    for (case_id, upstream_case_id, min_obligations) in VERIFIED_CASES {
        expected_by_case.insert(
            *case_id,
            CaseMetadata {
                case_id: (*case_id).to_string(),
                upstream_case_id: (*upstream_case_id).to_string(),
                expected_verdict: "verified".to_string(),
                min_obligations: *min_obligations,
                expected_error_patterns: Vec::new(),
            },
        );
    }
    for (case_id, upstream_case_id, min_obligations) in COUNTEREXAMPLE_CASES {
        expected_by_case.insert(
            *case_id,
            CaseMetadata {
                case_id: (*case_id).to_string(),
                upstream_case_id: (*upstream_case_id).to_string(),
                expected_verdict: "counterexample".to_string(),
                min_obligations: *min_obligations,
                expected_error_patterns: Vec::new(),
            },
        );
    }
    for (case_id, upstream_case_id, expected_fragments) in FAIL_CLOSED_CASES {
        expected_by_case.insert(
            *case_id,
            CaseMetadata {
                case_id: (*case_id).to_string(),
                upstream_case_id: (*upstream_case_id).to_string(),
                expected_verdict: "error".to_string(),
                min_obligations: 0,
                expected_error_patterns: expected_fragments
                    .iter()
                    .map(|fragment| (*fragment).to_string())
                    .collect(),
            },
        );
    }

    [
        "lifetime_consume_once",
        "lifetime_consume_fields_ok",
        "lifetime_borrow_two_distinct_locals_ok",
        "lifetime_sequential_mutable_borrows_ok",
        "lifetime_return_ref_named_identity",
        "lifetime_return_ref_named_identity_caller",
        "lifetime_shared_ref_read_verified",
        "lifetime_ref_holder_named_identity_currently_blocked",
        "lifetime_copy_payload_reuse_ok",
        "lifetime_mutable_reference_scalar_write_verified",
        "lifetime_mutable_reference_write_currently_blocked",
        "lifetime_false_assert_counterexample",
        "lifetime_assign_twice_false_tail_counterexample",
        "lifetime_mutable_reference_scalar_write_false_tail_counterexample",
        "lifetime_compound_mutable_reference_assignment_verified",
    ]
    .into_iter()
    .map(|case_id| {
        expected_by_case
            .remove(case_id)
            .unwrap_or_else(|| panic!("missing expected metadata for {case_id}"))
    })
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
            entry["upstream_path"].as_str() == Some("source/rust_verify_test/tests/lifetime.rs")
        })
        .expect("Verus manifest should contain lifetime.rs row");

    row["expected_cases"]
        .as_array()
        .expect("lifetime.rs row should contain expected_cases")
        .iter()
        .map(|entry| CaseMetadata {
            case_id: entry["case_id"]
                .as_str()
                .expect("case_id should be a string")
                .to_string(),
            upstream_case_id: entry
                .get("upstream_case_id")
                .and_then(serde_json::Value::as_str)
                .unwrap_or("")
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
fn lifetime_rs_port_file_is_rust_syntax() {
    let source =
        std::fs::read_to_string(lifetime_port_path()).expect("lifetime port should be readable");
    syn::parse_file(&source).expect("lifetime port should parse as ordinary Rust syntax");
}

#[test]
fn lifetime_rs_pinned_upstream_case_shapes_are_present() {
    let path = pinned_upstream_lifetime_path();
    if !path.exists() {
        eprintln!(
            "skipping pinned upstream lifetime.rs shape check; missing {}",
            path.display()
        );
        return;
    }

    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", path.display()));
    for expected in [
        "#[test] consume_once",
        "#[test] consume_twice",
        "#[test] consume_fields_ok",
        "#[test] borrow_local_ok",
        "#[test] borrow_tracked_twice_ok",
        "#[test] return_wrong_lifetime1",
        "#[test] return_wrong_lifetime2",
        "#[test] lifetime_bounds_exec",
        "#[test] lifetime_copy_succeed",
        "#[test] lifetime_copy_fail",
        "#[test] tracked_borrow_mut_assignment",
        "#[test] tracked_borrow_mut_assignment_fail",
        "#[test] lifetime_multiple_anonymous_names",
        "#[test] regression_issue1083",
        "#[test] two_phase",
        "#[test] two_phase_with_overloaded_compound_assignment_operator",
        "#[test] regression_issue959",
        "#[test] regression_issue1296",
        "#[test] derefs_lifetime",
        "#[test] lifetime_cfg_delete_nodes_due_to_tracked_never_ok",
    ] {
        assert!(
            source.contains(expected),
            "pinned upstream lifetime.rs should still contain {expected}"
        );
    }
}

#[test]
fn lifetime_rs_expected_case_metadata_is_exact() {
    let source =
        std::fs::read_to_string(lifetime_port_path()).expect("lifetime port should be readable");
    let file =
        syn::parse_file(&source).expect("lifetime port should parse as ordinary Rust syntax");
    assert_eq!(metadata_entries(&file), expected_metadata());
    assert!(
        source.contains("lifetime_rs_expected_cases")
            && source.contains("lifetime_rs_fail_closed_error_patterns"),
        "lifetime port should export expected-case and error-pattern metadata"
    );
}

#[test]
fn lifetime_rs_expected_case_metadata_matches_manifest() {
    let source =
        std::fs::read_to_string(lifetime_port_path()).expect("lifetime port should be readable");
    let file =
        syn::parse_file(&source).expect("lifetime port should parse as ordinary Rust syntax");
    assert_eq!(metadata_entries(&file), manifest_expected_metadata());
}

#[test]
fn lifetime_rs_verified_subset_verifies_from_file() {
    for (case, upstream_case, min_obligations) in VERIFIED_CASES {
        let (result, obligations) = verify_port_case(case, upstream_case);
        assert!(
            obligations >= *min_obligations,
            "{case} ({upstream_case}) should collect at least {min_obligations} obligation(s), got {obligations}"
        );
        assert!(
            matches!(result, VerifyResult::Verified),
            "{case} ({upstream_case}) should verify, got: {result:?}"
        );
    }
}

#[test]
fn lifetime_rs_counterexample_subset_is_rejected_from_file() {
    for (case, upstream_case, min_obligations) in COUNTEREXAMPLE_CASES {
        let (result, obligations) = verify_port_case(case, upstream_case);
        assert!(
            obligations >= *min_obligations,
            "{case} ({upstream_case}) should collect at least {min_obligations} obligation(s), got {obligations}"
        );
        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "{case} ({upstream_case}) should be rejected, got: {result:?}"
        );
    }
}

#[test]
fn lifetime_rs_mutable_reference_boundaries_fail_closed_from_file() {
    let path = lifetime_port_path();
    let path = path.to_str().expect("lifetime port path should be UTF-8");

    for (case, upstream_case, expected_fragments) in FAIL_CLOSED_CASES {
        expect_fail_closed_error_contains(path, case, upstream_case, expected_fragments);
    }
}
