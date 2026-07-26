// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Executable guards for the first upstream std.rs TrustVc scout.
//!
//! This keeps `source/rust_verify_test/tests/std.rs` as an unsupported gap.
//! The tests pin only stable verified cases, stable counterexamples, and
//! fail-closed error boundaries. Solver `Unknown` is rejected as evidence.

mod common;

use std::{
    collections::BTreeMap,
    path::{Path, PathBuf},
};
use trust_vc_core::{verify_function_from_file, VerifyResult};

#[path = "../../../evals/verus/ported/std.rs"]
mod std_port;

fn std_port_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/ported/std.rs")
}

fn verus_manifest_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/verus-tests.json")
}

fn pinned_upstream_std_path() -> PathBuf {
    common::pinned_verus_test_path("std.rs")
}

fn verify_case(path: &str, case: &str, upstream_case: &str) -> VerifyResult {
    verify_function_from_file(path, case)
        .unwrap_or_else(|err| panic!("{case} ({upstream_case}) should extract: {err}"))
}

fn expect_error_contains_any(
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
        "unsigned_wrapping_mul_constants_verified",
        "unsigned_wrapping_mul",
    ),
    (
        "signed_wrapping_mul_prefix_constants_verified",
        "signed_wrapping_mul",
    ),
    ("index_vec_in_bounds_copy_verified", "index_vec_in_bounds"),
    ("vec_macro_literal_view_verified", "vec_macro"),
];

const COUNTEREXAMPLE_CASES: &[(&str, &str)] = &[
    (
        "unsigned_wrapping_mul_wrong_value_counterexample",
        "unsigned_wrapping_mul",
    ),
    (
        "signed_wrapping_mul_false_tail_counterexample",
        "signed_wrapping_mul",
    ),
];

const FAIL_CLOSED_CASES: &[(&str, &str, &[&str])] = &[
    (
        "box_new_deref_currently_blocked",
        "box_new",
        &["Box", "deref", "unknown", "unsupported", "opaque"],
    ),
    (
        "rc_arc_clone_deref_currently_blocked",
        "rc_arc",
        &[
            "Rc",
            "Arc",
            "deref",
            "unknown",
            "unsupported",
            "opaque",
            "unresolved variable",
        ],
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

fn metadata_entries() -> Vec<CaseMetadata> {
    let mut error_patterns = std_port::std_rs_fail_closed_error_patterns()
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

    let entries = std_port::std_rs_expected_cases()
        .iter()
        .map(
            |(case_id, upstream_case_id, expected_verdict, min_obligations)| CaseMetadata {
                case_id: (*case_id).to_string(),
                upstream_case_id: (*upstream_case_id).to_string(),
                expected_verdict: (*expected_verdict).to_string(),
                min_obligations: *min_obligations,
                expected_error_patterns: error_patterns.remove(*case_id).unwrap_or_default(),
            },
        )
        .collect();

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
            entry["upstream_path"].as_str() == Some("source/rust_verify_test/tests/std.rs")
        })
        .expect("Verus manifest should contain std.rs row");

    row["expected_cases"]
        .as_array()
        .expect("std.rs row should contain expected_cases")
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
fn std_rs_port_file_is_rust_syntax() {
    let source = std::fs::read_to_string(std_port_path()).expect("std port should be readable");
    syn::parse_file(&source).expect("std port should parse as ordinary Rust syntax");
}

#[test]
fn std_rs_pinned_upstream_case_shapes_are_present() {
    let path = pinned_upstream_std_path();
    if !path.exists() {
        eprintln!(
            "skipping pinned upstream std.rs shape check; missing {}",
            path.display()
        );
        return;
    }

    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", path.display()));
    for expected in [
        "#[test] rc_arc",
        "#[test] ref_clone",
        "#[test] box_new",
        "#[test] index_vec_in_bounds",
        "#[test] unsigned_wrapping_mul",
        "#[test] signed_wrapping_mul",
        "#[test] question_mark_option",
        "#[test] question_mark_result",
        "#[test] clone_for_std_types",
        "#[test] vec_macro",
        "#[test] phantom_data_is_unit",
        "#[test] manually_drop",
    ] {
        assert!(
            source.contains(expected),
            "pinned upstream std.rs should still contain {expected}"
        );
    }
}

#[test]
fn std_rs_expected_case_metadata_is_exact() {
    assert_eq!(
        std_port::std_rs_fail_closed_error_patterns(),
        &[
            (
                "box_new_deref_currently_blocked",
                &["Box", "deref", "unsupported"][..],
            ),
            (
                "rc_arc_clone_deref_currently_blocked",
                &["unresolved variable", "Rc", "Arc"][..],
            ),
        ]
    );
    assert_eq!(metadata_entries(), manifest_expected_metadata());
    assert_eq!(
        std_port::std_rs_expected_cases(),
        &[
            (
                "unsigned_wrapping_mul_constants_verified",
                "unsigned_wrapping_mul",
                "verified",
                3,
            ),
            (
                "signed_wrapping_mul_prefix_constants_verified",
                "signed_wrapping_mul",
                "verified",
                5,
            ),
            (
                "unsigned_wrapping_mul_wrong_value_counterexample",
                "unsigned_wrapping_mul",
                "counterexample",
                1,
            ),
            (
                "signed_wrapping_mul_false_tail_counterexample",
                "signed_wrapping_mul",
                "counterexample",
                1,
            ),
            (
                "vec_macro_literal_view_verified",
                "vec_macro",
                "verified",
                4,
            ),
            (
                "index_vec_in_bounds_copy_verified",
                "index_vec_in_bounds",
                "verified",
                1,
            ),
            ("box_new_deref_currently_blocked", "box_new", "error", 0),
            ("rc_arc_clone_deref_currently_blocked", "rc_arc", "error", 0,),
        ]
    );
}

#[test]
fn std_rs_runtime_std_operations_execute() {
    std_port::rc_arc_runtime_clone_deref();
    std_port::ref_clone_runtime_alias();
    std_port::box_new_runtime_deref();
    std_port::vec_macro_runtime_literal();
    assert_eq!(
        std_port::question_mark_option_runtime_none_short_circuits(),
        None
    );
    assert_eq!(
        std_port::question_mark_result_runtime_err_short_circuits(),
        Err(false)
    );
    std_port::manually_drop_runtime_clone_into_inner();
}

#[test]
fn std_rs_verified_subset_verifies_from_file() {
    let path = std_port_path();
    let path = path.to_str().expect("std port path should be UTF-8");

    for (case, upstream_case) in VERIFIED_CASES {
        let result = verify_case(path, case, upstream_case);
        assert!(
            matches!(result, VerifyResult::Verified),
            "{case} ({upstream_case}) should verify, got: {result:?}"
        );
    }
}

#[test]
fn std_rs_counterexample_subset_is_rejected_from_file() {
    let path = std_port_path();
    let path = path.to_str().expect("std port path should be UTF-8");

    for (case, upstream_case) in COUNTEREXAMPLE_CASES {
        let result = verify_case(path, case, upstream_case);
        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "{case} ({upstream_case}) should be rejected, got: {result:?}"
        );
    }
}

#[test]
fn std_rs_unsupported_std_boundaries_fail_closed_from_file() {
    let path = std_port_path();
    let path = path.to_str().expect("std port path should be UTF-8");

    for (case, upstream_case, expected_fragments) in FAIL_CLOSED_CASES {
        expect_error_contains_any(path, case, upstream_case, expected_fragments);
    }
}
