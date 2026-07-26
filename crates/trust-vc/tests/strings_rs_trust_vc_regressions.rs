// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Executable guards for the current upstream strings.rs partial port.
//!
//! This does not claim full Verus string parity. It records exact std runtime
//! behavior for a small string slice, verifies upstream char literal cases,
//! probes the current `String::view()` length/equality surface, and keeps
//! direct `String::len()` fail-closed in the default TrustVc configuration.

mod common;

use std::{
    collections::{BTreeMap, BTreeSet},
    path::{Path, PathBuf},
};
use trust_vc_core::{verify_function_from_file, VerifyResult};

#[path = "../../../evals/verus/ported/strings.rs"]
mod strings_port;

fn strings_port_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/ported/strings.rs")
}

fn verus_manifest_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/verus-tests.json")
}

fn pinned_upstream_strings_path() -> PathBuf {
    common::pinned_verus_test_path("strings.rs")
}

#[derive(Debug, Eq, PartialEq)]
struct CaseMetadata {
    case_id: String,
    upstream_case_id: String,
    expected_verdict: String,
    min_obligations: usize,
    expected_error_patterns: Vec<String>,
}

fn metadata_entries() -> Vec<CaseMetadata> {
    let mut error_patterns: BTreeMap<String, Vec<String>> =
        strings_port::strings_rs_expected_error_patterns()
            .iter()
            .map(|(case_id, patterns)| {
                (
                    (*case_id).to_string(),
                    patterns
                        .iter()
                        .map(|pattern| (*pattern).to_string())
                        .collect(),
                )
            })
            .collect();
    let mut seen = BTreeSet::new();
    let mut entries = Vec::new();

    for (case_id, upstream_case_id, expected_verdict, min_obligations) in
        strings_port::strings_rs_expected_cases()
    {
        assert!(
            seen.insert((*case_id).to_string()),
            "duplicate strings metadata for {case_id}"
        );
        entries.push(CaseMetadata {
            case_id: (*case_id).to_string(),
            upstream_case_id: (*upstream_case_id).to_string(),
            expected_verdict: (*expected_verdict).to_string(),
            min_obligations: *min_obligations,
            expected_error_patterns: error_patterns.remove(*case_id).unwrap_or_default(),
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
            entry["upstream_path"].as_str() == Some("source/rust_verify_test/tests/strings.rs")
        })
        .expect("Verus manifest should contain strings.rs row");

    row["expected_cases"]
        .as_array()
        .expect("strings.rs row should contain expected_cases")
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

fn assert_panics(f: impl FnOnce() + std::panic::UnwindSafe, label: &str) {
    let previous_hook = std::panic::take_hook();
    std::panic::set_hook(Box::new(|_| {}));
    let result = std::panic::catch_unwind(f);
    std::panic::set_hook(previous_hook);
    assert!(result.is_err(), "{label} should panic at runtime");
}

fn assert_verify_verified(case: &str) {
    let path = strings_port_path();
    let path = path.to_str().expect("strings port path should be UTF-8");
    let result = verify_function_from_file(path, case)
        .unwrap_or_else(|err| panic!("{case} should extract from strings.rs: {err}"));
    assert!(
        matches!(result, VerifyResult::Verified),
        "{case} should verify, got {result:?}"
    );
}

fn assert_verify_counterexample(case: &str) {
    let path = strings_port_path();
    let path = path.to_str().expect("strings port path should be UTF-8");
    let result = verify_function_from_file(path, case)
        .unwrap_or_else(|err| panic!("{case} should extract from strings.rs: {err}"));
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "{case} should be rejected, got {result:?}"
    );
}

fn assert_verify_not_verified(case: &str) {
    let path = strings_port_path();
    let path = path.to_str().expect("strings port path should be UTF-8");
    let result = verify_function_from_file(path, case)
        .unwrap_or_else(|err| panic!("{case} should extract from strings.rs: {err}"));
    assert!(
        !matches!(result, VerifyResult::Verified),
        "{case} should not verify until String::view() refutation is precise, got {result:?}"
    );
}

fn assert_verify_error_contains(case: &str, expected_fragments: &[&str]) {
    let path = strings_port_path();
    let path = path.to_str().expect("strings port path should be UTF-8");
    let message = match verify_function_from_file(path, case) {
        Err(err) => err.to_string(),
        Ok(VerifyResult::Error { message }) => message,
        Ok(other) => panic!("{case} should fail closed with an error, got {other:?}"),
    };

    for fragment in expected_fragments {
        assert!(
            message.contains(fragment),
            "{case} error should contain {fragment:?}, got: {message}"
        );
    }
}

#[test]
fn strings_rs_runtime_std_string_subset_executes() {
    strings_port::test_passes_len_runtime_std_str();
    strings_port::test_pass_is_ascii_runtime_std_str();
    strings_port::test_append_1_runtime_std_string_push_str();
    strings_port::test_str_and_string_eq_runtime_std_subset();
}

#[test]
fn strings_rs_runtime_wrong_string_witnesses_panic() {
    assert_panics(
        strings_port::test_fails_len_runtime_wrong_counterexample,
        "wrong str len witness",
    );
    assert_panics(
        strings_port::test_fails_is_ascii_runtime_wrong_counterexample,
        "wrong str is_ascii witness",
    );
    assert_panics(
        strings_port::test_fails_string_eq_runtime_wrong_counterexample,
        "wrong String equality witness",
    );
}

#[test]
fn strings_rs_pinned_upstream_case_shapes_are_present() {
    let path = pinned_upstream_strings_path();
    if !path.exists() {
        eprintln!(
            "skipping pinned upstream strings.rs shape check; missing {}",
            path.display()
        );
        return;
    }

    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", path.display()));
    assert!(
        source.contains("#[test] test_char_passes"),
        "pinned upstream source should still contain test_char_passes"
    );
    assert!(
        source.contains("#[test] test_char_fails"),
        "pinned upstream source should still contain test_char_fails"
    );
    assert!(
        source.contains("#[test] test_passes_len"),
        "pinned upstream source should still contain test_passes_len"
    );
    assert!(
        source.contains("#[test] test_fails_len"),
        "pinned upstream source should still contain test_fails_len"
    );
    assert!(
        source.contains("#[test] test_string_1_pass"),
        "pinned upstream source should still contain test_string_1_pass"
    );
    assert!(
        source.contains("#[test] test_string_1_fail"),
        "pinned upstream source should still contain test_string_1_fail"
    );
    assert!(
        source.contains("#[test] test_strlit_neq"),
        "pinned upstream source should still contain test_strlit_neq"
    );
}

#[test]
fn strings_rs_expected_case_metadata_is_exact() {
    assert_eq!(metadata_entries(), manifest_expected_metadata());
}

#[test]
fn strings_rs_expected_case_metadata_matches_manifest() {
    assert_eq!(metadata_entries(), manifest_expected_metadata());
}

#[test]
fn strings_rs_verified_subset_verifies_from_file() {
    for case in [
        "test_char_passes_ascii_literal_verified",
        "string_view_len_reflexive_verified",
        "string_view_equality_reflexive_verified",
        "str_literal_equality_verified",
    ] {
        assert_verify_verified(case);
    }
}

#[test]
fn strings_rs_counterexample_subset_is_rejected_from_file() {
    assert_verify_counterexample("test_char_fails_ascii_literal_counterexample");
}

#[test]
fn strings_rs_false_string_view_cases_do_not_verify_from_file() {
    assert_verify_not_verified("string_view_len_inconsistent_currently_unknown");
    assert_verify_not_verified("string_view_len_irreflexive_currently_unknown");
    assert_verify_not_verified("string_view_equality_irreflexive_currently_unknown");
}

#[test]
fn strings_rs_unsupported_string_operations_fail_closed_from_file() {
    // Direct `String::len()` (no `view()`) still fails closed by design. Literal
    // string equality is now VERIFIED (see `strings_rs_verified_subset_verifies_from_file`).
    assert_verify_error_contains(
        "string_direct_len_fail_closed_error",
        &["len on 'String'", "view()"],
    );
}
