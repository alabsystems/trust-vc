// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Executable guards for the first upstream spec_derive.rs TrustVc scout slice.
//!
//! These tests intentionally keep `source/rust_verify_test/tests/spec_derive.rs`
//! classified as an unsupported gap. They prove only manual TrustVc projections
//! corresponding to a small `make_spec_type`/`self_view` subset, reject one
//! false generated-spec projection, and pin a HashMap field-view boundary as
//! fail-closed while macro generation and diagnostics remain unsupported.

mod common;

use std::{
    collections::BTreeMap,
    path::{Path, PathBuf},
};
use trust_vc_core::{verify_function_from_file, VerifyResult};

#[path = "../../../evals/verus/ported/spec_derive.rs"]
mod spec_derive_port;

fn spec_derive_port_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/ported/spec_derive.rs")
}

fn verus_manifest_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/verus-tests.json")
}

fn pinned_upstream_spec_derive_path() -> PathBuf {
    common::pinned_verus_test_path("spec_derive.rs")
}

fn verify_case(path: &str, case: &str, upstream_case: &str) -> VerifyResult {
    verify_function_from_file(path, case)
        .unwrap_or_else(|err| panic!("{case} ({upstream_case}) should extract: {err}"))
}

fn expect_error_contains(path: &str, case: &str, upstream_case: &str, expected_terms: &[&str]) {
    let message = match verify_function_from_file(path, case) {
        Err(err) => err.to_string(),
        Ok(VerifyResult::Error { message }) => message,
        Ok(result) => {
            panic!("{case} ({upstream_case}) should fail closed with Error, got: {result:?}")
        }
    };

    assert!(
        expected_terms.iter().any(|term| message.contains(term)),
        "{case} ({upstream_case}) error should contain one of {expected_terms:?}, got: {message}"
    );
}

const VERIFIED_CASES: &[(&str, &str)] = &[
    (
        "make_spec_type_struct_manual_projection_verified",
        "test_basic_struct_make_spec_type",
    ),
    (
        "make_spec_type_exclude_field_manual_projection_verified",
        "test_complex_struct_with_exclude_and_lifetimes",
    ),
    (
        "self_view_copy_manual_identity_verified",
        "test_self_view_copy_works",
    ),
];

const COUNTEREXAMPLE_CASES: &[(&str, &str)] = &[(
    "make_spec_type_struct_wrong_projection_counterexample",
    "test_basic_struct_make_spec_type_false_adjacent_projection",
)];

#[derive(Debug, Eq, PartialEq)]
struct CaseMetadata {
    case_id: String,
    upstream_case_id: String,
    expected_verdict: String,
    min_obligations: usize,
    expected_error_patterns: Vec<String>,
}

fn expected_metadata() -> Vec<CaseMetadata> {
    let mut error_patterns = spec_derive_port::spec_derive_rs_fail_closed_error_patterns()
        .iter()
        .map(|(case_id, patterns)| {
            (
                (*case_id).to_string(),
                patterns
                    .iter()
                    .map(|pattern| (*pattern).to_string())
                    .collect::<Vec<_>>(),
            )
        })
        .collect::<BTreeMap<_, _>>();

    let entries = spec_derive_port::spec_derive_rs_expected_cases()
        .iter()
        .map(
            |(case_id, upstream_case_id, expected_verdict, min_obligations)| {
                let expected_error_patterns = error_patterns.remove(*case_id).unwrap_or_default();
                CaseMetadata {
                    case_id: (*case_id).to_string(),
                    upstream_case_id: (*upstream_case_id).to_string(),
                    expected_verdict: (*expected_verdict).to_string(),
                    min_obligations: *min_obligations,
                    expected_error_patterns,
                }
            },
        )
        .collect::<Vec<_>>();

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
            entry["upstream_path"].as_str() == Some("source/rust_verify_test/tests/spec_derive.rs")
        })
        .expect("Verus manifest should contain spec_derive.rs row");

    row["expected_cases"]
        .as_array()
        .expect("spec_derive.rs row should contain expected_cases")
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
fn spec_derive_rs_port_file_is_rust_syntax() {
    let source = std::fs::read_to_string(spec_derive_port_path())
        .expect("spec_derive port should be readable");
    syn::parse_file(&source).expect("spec_derive port should parse as ordinary Rust syntax");
}

#[test]
fn spec_derive_rs_runtime_manual_subset_executes() {
    spec_derive_port::test_make_spec_type_manual_projection_runtime();
}

#[test]
fn spec_derive_rs_pinned_upstream_case_shapes_are_present() {
    let path = pinned_upstream_spec_derive_path();
    if !path.exists() {
        eprintln!(
            "skipping pinned upstream spec_derive.rs shape check; missing {}",
            path.display()
        );
        return;
    }

    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", path.display()));
    for expected in [
        "test_union_not_supported",
        "test_generic_type_params_not_supported",
        "test_basic_struct_make_spec_type",
        "test_complex_struct_with_exclude_and_lifetimes",
        "test_enum_make_spec_type_comprehensive",
        "test_self_view_copy_works",
        "test_self_view_enum_comprehensive",
        "test_self_view_struct_comprehensive",
    ] {
        assert!(
            source.contains(expected),
            "pinned upstream spec_derive.rs should still contain {expected}"
        );
    }
}

#[test]
fn spec_derive_rs_expected_case_metadata_is_exact() {
    assert_eq!(
        spec_derive_port::spec_derive_rs_expected_cases(),
        &[
            (
                "make_spec_type_struct_manual_projection_verified",
                "test_basic_struct_make_spec_type",
                "verified",
                4,
            ),
            (
                "make_spec_type_exclude_field_manual_projection_verified",
                "test_complex_struct_with_exclude_and_lifetimes",
                "verified",
                2,
            ),
            (
                "self_view_copy_manual_identity_verified",
                "test_self_view_copy_works",
                "verified",
                2,
            ),
            (
                "make_spec_type_struct_wrong_projection_counterexample",
                "test_basic_struct_make_spec_type_false_adjacent_projection",
                "counterexample",
                1,
            ),
            (
                "make_spec_type_hash_map_field_view_fails_closed_error",
                "test_complex_struct_with_exclude_and_lifetimes",
                "error",
                0,
            ),
        ]
    );
    assert_eq!(
        spec_derive_port::spec_derive_rs_fail_closed_error_patterns(),
        &[(
            "make_spec_type_hash_map_field_view_fails_closed_error",
            &["HashMap", "view"][..],
        )]
    );
}

#[test]
fn spec_derive_rs_expected_case_metadata_matches_manifest() {
    assert_eq!(expected_metadata(), manifest_expected_metadata());
}

#[test]
fn spec_derive_rs_verified_subset_verifies_from_file() {
    let path = spec_derive_port_path();
    let path = path
        .to_str()
        .expect("spec_derive port path should be UTF-8");

    for (case, upstream_case) in VERIFIED_CASES {
        let result = verify_case(path, case, upstream_case);
        assert!(
            matches!(result, VerifyResult::Verified),
            "{case} ({upstream_case}) should verify, got: {result:?}"
        );
    }
}

#[test]
fn spec_derive_rs_counterexample_subset_is_rejected_from_file() {
    let path = spec_derive_port_path();
    let path = path
        .to_str()
        .expect("spec_derive port path should be UTF-8");

    for (case, upstream_case) in COUNTEREXAMPLE_CASES {
        let result = verify_case(path, case, upstream_case);
        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "{case} ({upstream_case}) should be rejected, got: {result:?}"
        );
    }
}

#[test]
fn spec_derive_rs_hash_map_field_view_fails_closed_from_file() {
    let path = spec_derive_port_path();
    let path = path
        .to_str()
        .expect("spec_derive port path should be UTF-8");

    expect_error_contains(
        path,
        "make_spec_type_hash_map_field_view_fails_closed_error",
        "test_complex_struct_with_exclude_and_lifetimes",
        &["contains_key() not supported", "dom tracking"],
    );
}
