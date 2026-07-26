// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Executable guards for the first upstream user_defined_type_invariants.rs
//! TrustVc scout slice.
//!
//! These tests intentionally keep
//! `source/rust_verify_test/tests/user_defined_type_invariants.rs` classified as
//! an unsupported gap. They pin only manual Rust-valid invariant assertions that
//! TrustVc can execute today, plus false adjacent assertions that must be
//! rejected with stable counterexamples.

mod common;

use std::path::{Path, PathBuf};
use trust_vc_core::{verify_function_from_file, VerifyResult};

#[path = "../../../evals/verus/ported/user_defined_type_invariants.rs"]
mod user_defined_type_invariants_port;

fn user_defined_type_invariants_port_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../evals/verus/ported/user_defined_type_invariants.rs")
}

fn verus_manifest_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/verus-tests.json")
}

fn pinned_upstream_user_defined_type_invariants_path() -> PathBuf {
    common::pinned_verus_test_path("user_defined_type_invariants.rs")
}

fn verify_case(path: &str, case: &str, upstream_case: &str) -> VerifyResult {
    verify_function_from_file(path, case)
        .unwrap_or_else(|err| panic!("{case} ({upstream_case}) should extract: {err}"))
}

const VERIFIED_CASES: &[(&str, &str)] = &[
    (
        "type_inv_ctor_manual_invariant_verified",
        "test_ctors::test_exec1",
    ),
    (
        "type_inv_field_assignment_preserves_verified",
        "test_mut_ref_whole_ok",
    ),
    (
        "type_inv_nested_assignment_preserves_verified",
        "test_normal_var_nested",
    ),
    (
        "type_inv_equal_fields_manual_verified",
        "test_with_generics",
    ),
];

const COUNTEREXAMPLE_CASES: &[(&str, &str)] = &[
    ("type_inv_ctor_bad_value_counterexample", "test_ctors"),
    (
        "type_inv_equal_fields_bad_counterexample",
        "test_with_generics",
    ),
];

#[derive(Debug, Eq, PartialEq)]
struct CaseMetadata {
    case_id: String,
    upstream_case_id: String,
    expected_verdict: String,
    min_obligations: usize,
}

fn expected_metadata() -> Vec<CaseMetadata> {
    user_defined_type_invariants_port::user_defined_type_invariants_rs_expected_cases()
        .iter()
        .map(
            |(case_id, upstream_case_id, expected_verdict, min_obligations)| CaseMetadata {
                case_id: (*case_id).to_string(),
                upstream_case_id: (*upstream_case_id).to_string(),
                expected_verdict: (*expected_verdict).to_string(),
                min_obligations: *min_obligations,
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
                == Some("source/rust_verify_test/tests/user_defined_type_invariants.rs")
        })
        .expect("Verus manifest should contain user_defined_type_invariants.rs row");

    row["expected_cases"]
        .as_array()
        .expect("user_defined_type_invariants.rs row should contain expected_cases")
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
        })
        .collect()
}

#[test]
fn user_defined_type_invariants_rs_port_file_is_rust_syntax() {
    let source = std::fs::read_to_string(user_defined_type_invariants_port_path())
        .expect("user_defined_type_invariants port should be readable");
    syn::parse_file(&source)
        .expect("user_defined_type_invariants port should parse as ordinary Rust syntax");
}

#[test]
fn user_defined_type_invariants_rs_runtime_manual_subset_executes() {
    user_defined_type_invariants_port::test_ctor_runtime_manual_invariant_subset();
    user_defined_type_invariants_port::test_nested_runtime_manual_invariant_subset();
}

#[test]
fn user_defined_type_invariants_rs_pinned_upstream_case_shapes_are_present() {
    let path = pinned_upstream_user_defined_type_invariants_path();
    if !path.exists() {
        eprintln!(
            "skipping pinned upstream user_defined_type_invariants.rs shape check; missing {}",
            path.display()
        );
        return;
    }

    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", path.display()));
    for expected in [
        "#[test] type_inv_conflict",
        "#[test] type_inv_lifetime_bounds",
        "#[test] test_ctors",
        "#[test] test_mut_ref_whole_ok",
        "#[test] test_normal_var_nested",
        "#[test] test_with_generics",
        "#[test] get_assumption",
        "#[test] test_enum",
        "#[test] type_inv_const_params",
        "#[test] mut_ref_not_supported",
    ] {
        assert!(
            source.contains(expected),
            "pinned upstream user_defined_type_invariants.rs should still contain {expected}"
        );
    }
}

#[test]
fn user_defined_type_invariants_rs_expected_case_metadata_is_exact() {
    assert_eq!(
        user_defined_type_invariants_port::user_defined_type_invariants_rs_expected_cases(),
        &[
            (
                "type_inv_ctor_manual_invariant_verified",
                "test_ctors",
                "verified",
                2,
            ),
            (
                "type_inv_field_assignment_preserves_verified",
                "test_mut_ref_whole_ok",
                "verified",
                2,
            ),
            (
                "type_inv_nested_assignment_preserves_verified",
                "test_normal_var_nested",
                "verified",
                2,
            ),
            (
                "type_inv_equal_fields_manual_verified",
                "test_with_generics",
                "verified",
                1,
            ),
            (
                "type_inv_ctor_bad_value_counterexample",
                "test_ctors",
                "counterexample",
                1,
            ),
            (
                "type_inv_equal_fields_bad_counterexample",
                "test_with_generics",
                "counterexample",
                1,
            ),
        ]
    );
}

#[test]
fn user_defined_type_invariants_rs_expected_case_metadata_matches_manifest() {
    assert_eq!(expected_metadata(), manifest_expected_metadata());
}

#[test]
fn user_defined_type_invariants_rs_verified_subset_verifies_from_file() {
    let path = user_defined_type_invariants_port_path();
    let path = path
        .to_str()
        .expect("user_defined_type_invariants port path should be UTF-8");

    for (case, upstream_case) in VERIFIED_CASES {
        let result = verify_case(path, case, upstream_case);
        assert!(
            matches!(result, VerifyResult::Verified),
            "{case} ({upstream_case}) should verify, got: {result:?}"
        );
    }
}

#[test]
fn user_defined_type_invariants_rs_counterexample_subset_is_rejected_from_file() {
    let path = user_defined_type_invariants_port_path();
    let path = path
        .to_str()
        .expect("user_defined_type_invariants port path should be UTF-8");

    for (case, upstream_case) in COUNTEREXAMPLE_CASES {
        let result = verify_case(path, case, upstream_case);
        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "{case} ({upstream_case}) should produce a counterexample, got: {result:?}"
        );
    }
}
