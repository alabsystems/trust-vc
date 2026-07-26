// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Executable and fail-closed guards for upstream vec.rs.
//!
//! This replacement scout intentionally does not prove full Verus Vec parity.
//! It keeps exact runtime Vec behavior for a push/view prefix and the active
//! mutation case, checks the pinned upstream case inventory when available, and
//! verifies local actual `Vec<T>::view()` empty/push/insert prefixes while
//! keeping broader `Vec<T>::view()` and `Vec<Tree>` child/decreases surfaces fail-closed
//! instead of relying on standalone Seq-model witnesses.

mod common;

use std::path::{Path, PathBuf};
use trust_vc_core::{verify_function_from_file, VerifyResult};

#[path = "../../../evals/verus/ported/vec.rs"]
mod vec_port;

fn vec_port_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/ported/vec.rs")
}

fn verus_manifest_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/verus-tests.json")
}

fn pinned_upstream_vec_path() -> PathBuf {
    common::pinned_verus_test_path("vec.rs")
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
    vec_port::vec_rs_expected_cases()
        .iter()
        .map(
            |(case_id, upstream_case_id, expected_verdict, min_obligations)| CaseMetadata {
                case_id: (*case_id).to_string(),
                upstream_case_id: (*upstream_case_id).to_string(),
                expected_verdict: (*expected_verdict).to_string(),
                min_obligations: *min_obligations,
                expected_error_patterns: Vec::new(),
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
            entry["upstream_path"].as_str() == Some("source/rust_verify_test/tests/vec.rs")
        })
        .expect("Verus manifest should contain vec.rs row");

    row["expected_cases"]
        .as_array()
        .expect("vec.rs row should contain expected_cases")
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

fn active_upstream_cases(source: &str) -> Vec<String> {
    source
        .lines()
        .filter_map(|line| {
            let trimmed = line.trim();
            let rest = trimmed.strip_prefix("#[test] ")?;
            rest.split_whitespace().next().map(str::to_string)
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

fn assert_verify_fails_closed(case: &str, expected_terms: &[&str]) {
    let path = vec_port_path();
    let path = path.to_str().expect("port path should be UTF-8");

    match verify_function_from_file(path, case) {
        Err(err) => {
            let message = err.to_string();
            assert!(
                expected_terms.iter().any(|term| message.contains(term)),
                "{case} fail-closed error should identify one of {expected_terms:?}, got: {message}"
            );
        }
        Ok(VerifyResult::Verified) => {
            panic!("{case} must not verify until actual Vec parity lands");
        }
        Ok(VerifyResult::Counterexample { .. }) => {}
        Ok(VerifyResult::Unknown { reason, .. }) => {
            assert!(
                expected_terms.iter().any(|term| reason.contains(term)),
                "{case} fail-closed unknown should identify one of {expected_terms:?}, got: {reason}"
            );
        }
        Ok(VerifyResult::Error { message }) => {
            assert!(
                expected_terms.iter().any(|term| message.contains(term)),
                "{case} fail-closed verifier error should identify one of {expected_terms:?}, got: {message}"
            );
        }
        Ok(other) => {
            panic!("{case} returned an unexpected verifier result: {other:?}");
        }
    }
}

fn assert_verify_verified(case: &str) {
    let path = vec_port_path();
    let path = path.to_str().expect("port path should be UTF-8");
    match verify_function_from_file(path, case) {
        Ok(VerifyResult::Verified) => {}
        other => panic!("{case} should verify, got: {other:?}"),
    }
}

#[test]
fn vec_rs_expected_case_metadata_matches_manifest() {
    assert_eq!(metadata_entries(), manifest_expected_metadata());
}

#[test]
fn vec_rs_runtime_mutation_prefix_executes_exact_std_vec_behavior() {
    vec_port::test_vec_new_runtime_empty();
    vec_port::test_vec_push_runtime_view_prefix();
    vec_port::test_vec_into_iter_runtime_mutation_prefix();
    vec_port::test_vec_insert_remove_runtime_slice();
    vec_port::test_vec_swap_remove_tail_runtime_slice();
}

#[test]
fn vec_rs_runtime_wrong_value_counterexample_panics() {
    assert_panics(
        vec_port::test_vec_into_iter_runtime_wrong_value_counterexample,
        "wrong Vec value witness",
    );
    assert_panics(
        vec_port::test_vec_insert_remove_runtime_wrong_value_counterexample,
        "wrong Vec insert/remove witness",
    );
    assert_panics(
        vec_port::test_vec_swap_remove_tail_runtime_wrong_value_counterexample,
        "wrong Vec swap_remove tail witness",
    );
}

#[test]
fn vec_rs_pinned_upstream_active_case_inventory_matches_port() {
    let path = pinned_upstream_vec_path();
    if !path.exists() {
        eprintln!(
            "skipping pinned upstream vec.rs inventory check; missing {}",
            path.display()
        );
        return;
    }

    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", path.display()));
    assert!(
        source.contains("assert(v1@ == seq![3u32, 4u32])"),
        "pinned upstream source should contain the Vec view assertion shape"
    );
    assert!(
        source.contains("decreases *tree"),
        "pinned upstream source should contain the Vec<Tree> decreases case"
    );

    let cases = active_upstream_cases(&source);
    let expected_cases: Vec<String> = vec_port::upstream_vec_rs_active_cases()
        .iter()
        .map(|case| case.to_string())
        .collect();
    assert_eq!(
        cases, expected_cases,
        "ported Vec case inventory must match active upstream harness cases"
    );
}

#[test]
fn vec_rs_port_no_longer_uses_seq_model_witness_functions() {
    let source = std::fs::read_to_string(vec_port_path()).expect("vec port should be readable");
    assert!(
        !source.contains("_seq_view_model_"),
        "Vec replacement port should not keep standalone Seq-model witness functions"
    );
    assert!(
        !source.contains("Seq::<"),
        "Vec replacement port should use actual Vec view probes, not direct Seq::<T> models"
    );
}

#[test]
fn vec_rs_actual_push_view_prefix_verifies_from_file() {
    assert_verify_verified("test_vec_push_view_exact_verified");
}

#[test]
fn vec_rs_actual_empty_view_prefix_verifies_from_file() {
    assert_verify_verified("test_vec_new_empty_view_len_verified");
}

#[test]
fn vec_rs_actual_insert_view_prefix_verifies_from_file() {
    for case in [
        "test_vec_insert_middle_view_verified",
        "test_vec_insert_front_view_verified",
        "test_vec_insert_end_view_verified",
    ] {
        assert_verify_verified(case);
    }
}

#[test]
fn vec_rs_actual_append_view_len_prefix_verifies_from_file() {
    assert_verify_verified("test_vec_append_view_len_prefix_verified");
}

#[test]
fn vec_rs_actual_remove_middle_view_prefix_verifies_from_file() {
    assert_verify_verified("test_vec_remove_middle_view_prefix_verified");
}

#[test]
fn vec_rs_actual_swap_remove_tail_view_prefix_verifies_from_file() {
    assert_verify_verified("test_vec_swap_remove_tail_view_prefix_verified");
}

#[test]
fn vec_rs_actual_insert_view_negative_cases_fail_closed_from_file() {
    assert_verify_fails_closed(
        "test_vec_insert_out_of_bounds_currently_rejected",
        &[
            "Seq::subrange",
            "requires end <= len",
            "overflow",
            "Counterexample",
        ],
    );
    assert_verify_fails_closed(
        "test_vec_insert_wrong_shift_counterexample",
        &["Counterexample", "Unknown", "index", "assertion"],
    );
    assert_verify_fails_closed(
        "test_vec_insert_mut_ref_alias_currently_rejected",
        &["Vec::insert receiver", "borrowed", "alias"],
    );
}

#[test]
fn vec_rs_actual_vec_view_surface_fails_closed_from_file() {
    assert_verify_fails_closed(
        "test_vec_into_iter_trust_vc_view_surface_currently_blocked",
        &[
            "Vec",
            "view",
            "Opaque",
            "unknown variable",
            "unresolved variable",
        ],
    );
}

#[test]
fn vec_rs_vec_tree_decreases_surface_fails_closed_from_file() {
    assert_verify_fails_closed(
        "test_vec_dec_vec_children_decreases_currently_blocked",
        &[
            "Vec",
            "children",
            "Tree",
            "len",
            "Opaque",
            "unknown variable",
            "unresolved variable",
        ],
    );
}
