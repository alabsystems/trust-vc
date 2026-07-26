// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Executable guards for the first upstream open_invariant.rs TrustVc scout
//! slice.
//!
//! These tests intentionally keep
//! `source/rust_verify_test/tests/open_invariant.rs` classified as an
//! unsupported gap. They pin only Rust-valid predicate and namespace-mask model
//! cases, stable false adjacent counterexamples, and fail-closed boundaries for
//! direct invariant macro extraction.

mod common;

use std::path::{Path, PathBuf};
use trust_vc_core::{
    extract_verification_conditions_with_file_context, verify_function_from_file, VerifyResult,
};

#[path = "../../../evals/verus/ported/open_invariant.rs"]
mod open_invariant_port;

fn open_invariant_port_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/ported/open_invariant.rs")
}

fn verus_manifest_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/verus-tests.json")
}

fn pinned_upstream_open_invariant_path() -> PathBuf {
    common::pinned_verus_test_path("open_invariant.rs")
}

fn verify_case(path: &str, case: &str, upstream_case: &str) -> VerifyResult {
    match verify_function_from_file(path, case)
        .unwrap_or_else(|err| panic!("{case} ({upstream_case}) should extract: {err}"))
    {
        VerifyResult::Unknown { reason, .. } => {
            panic!("{case} ({upstream_case}) returned solver Unknown, which is not stable evidence: {reason}")
        }
        result => result,
    }
}

fn expect_error_contains(path: &str, case: &str, upstream_case: &str, expected_terms: &[&str]) {
    let message = match verify_function_from_file(path, case) {
        Err(err) => err.to_string(),
        Ok(VerifyResult::Error { message }) => message,
        Ok(VerifyResult::Unknown { reason, .. }) => {
            panic!("{case} ({upstream_case}) returned solver Unknown, which is not stable evidence: {reason}")
        }
        Ok(result) => {
            panic!("{case} ({upstream_case}) should fail closed with Error, got: {result:?}")
        }
    };

    for expected_term in expected_terms {
        assert!(
            message.contains(expected_term),
            "{case} ({upstream_case}) error should contain {expected_term:?}, got: {message}"
        );
    }
}

fn assert_panics(f: impl FnOnce() + std::panic::UnwindSafe, label: &str) {
    let previous_hook = std::panic::take_hook();
    std::panic::set_hook(Box::new(|_| {}));
    let result = std::panic::catch_unwind(f);
    std::panic::set_hook(previous_hook);
    assert!(result.is_err(), "{label} should panic at runtime");
}

fn expected_case_inventory() -> Vec<open_invariant_port::OpenInvariantExpectedCase> {
    VERIFIED_CASES
        .iter()
        .map(|(case, upstream_case, min_obligations)| {
            (*case, *upstream_case, "verified", *min_obligations)
        })
        .chain(
            COUNTEREXAMPLE_CASES
                .iter()
                .map(|(case, upstream_case, min_obligations)| {
                    (*case, *upstream_case, "counterexample", *min_obligations)
                }),
        )
        .chain(
            FAIL_CLOSED_CASES
                .iter()
                .map(|(case, upstream_case, _)| (*case, *upstream_case, "error", 0)),
        )
        .collect()
}

fn expected_error_pattern_inventory(
) -> Vec<open_invariant_port::OpenInvariantFailClosedErrorPatterns> {
    FAIL_CLOSED_CASES
        .iter()
        .map(|(case, _, expected_patterns)| (*case, *expected_patterns))
        .collect()
}

#[derive(Debug, Eq, PartialEq)]
struct CaseMetadata {
    case_id: String,
    upstream_case_id: String,
    expected_verdict: String,
    min_obligations: usize,
}

fn case_metadata_as_owned(
    cases: &[open_invariant_port::OpenInvariantExpectedCase],
) -> Vec<CaseMetadata> {
    cases
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

fn error_patterns_as_owned(
    patterns: &[open_invariant_port::OpenInvariantFailClosedErrorPatterns],
) -> Vec<(String, Vec<String>)> {
    patterns
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
        .collect()
}

fn manifest_row() -> serde_json::Value {
    let source =
        std::fs::read_to_string(verus_manifest_path()).expect("Verus manifest should be readable");
    let manifest: serde_json::Value =
        serde_json::from_str(&source).expect("Verus manifest should parse as JSON");
    manifest["entries"]
        .as_array()
        .expect("Verus manifest should contain entries")
        .iter()
        .find(|entry| {
            entry["upstream_path"].as_str()
                == Some("source/rust_verify_test/tests/open_invariant.rs")
        })
        .expect("Verus manifest should contain open_invariant.rs row")
        .clone()
}

fn manifest_expected_case_metadata() -> Vec<CaseMetadata> {
    manifest_row()["expected_cases"]
        .as_array()
        .expect("open_invariant manifest row should contain expected_cases")
        .iter()
        .map(|case| CaseMetadata {
            case_id: case["case_id"]
                .as_str()
                .expect("manifest case should contain case_id")
                .to_string(),
            upstream_case_id: case["upstream_case_id"]
                .as_str()
                .expect("manifest case should contain upstream_case_id")
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
        })
        .collect()
}

fn manifest_fail_closed_error_pattern_metadata() -> Vec<(String, Vec<String>)> {
    manifest_row()["expected_cases"]
        .as_array()
        .expect("open_invariant manifest row should contain expected_cases")
        .iter()
        .filter_map(|case| {
            let patterns = case["expected_error_patterns"].as_array()?;
            Some((
                case["case_id"]
                    .as_str()
                    .expect("manifest case should contain case_id")
                    .to_string(),
                patterns
                    .iter()
                    .map(|pattern| {
                        pattern
                            .as_str()
                            .expect("expected_error_patterns entries should be strings")
                            .to_string()
                    })
                    .collect(),
            ))
        })
        .collect()
}

const VERIFIED_CASES: &[(&str, &str, usize)] = &[
    (
        "open_invariant_identity_close_verified",
        "basic_usage2_local",
        1,
    ),
    (
        "open_invariant_restore_required_value_verified",
        "basic_usage/basic_usage_local",
        2,
    ),
    (
        "open_invariant_nested_distinct_namespaces_verified",
        "nested_good/nested_good_local",
        4,
    ),
    (
        "opens_invariants_concrete_subset_verified",
        "opens_invariants_concrete positive subset",
        2,
    ),
    (
        "open_invariant_u8_type_bound_verified",
        "inv_typ_invariants",
        1,
    ),
    (
        "opens_invariants_empty_callee_mask_verified",
        "full_call_empty/full_call_empty_local",
        2,
    ),
    (
        "opens_invariants_symbolic_equal_mask_verified",
        "opens_invariants_concrete symbolic2_caller",
        1,
    ),
    (
        "opens_invariants_set_disjoint_mask_verified",
        "opens_invariants_set",
        3,
    ),
    (
        "open_invariant_single_credit_use_verified",
        "open_inv_in_proof/open_inv_in_proof_local",
        2,
    ),
];

const COUNTEREXAMPLE_CASES: &[(&str, &str, usize)] = &[
    (
        "open_invariant_close_wrong_value_counterexample",
        "inv_fail/inv_fail_local",
        1,
    ),
    (
        "open_invariant_nested_same_namespace_counterexample",
        "nested_failure/nested_failure_local",
        1,
    ),
    (
        "opens_invariants_missing_namespace_counterexample",
        "opens_invariants_concrete failing subset",
        1,
    ),
    (
        "opens_invariants_any_callee_inside_open_counterexample",
        "open_call_full/open_call_full_local",
        1,
    ),
    (
        "opens_invariants_none_mask_open_counterexample",
        "empty_open/empty_open_local",
        1,
    ),
    (
        "opens_invariants_symbolic_mismatch_counterexample",
        "opens_invariants_concrete symbolic_caller",
        1,
    ),
    (
        "open_invariant_spend_credit_twice_counterexample",
        "spend_credit_twice/spend_credit_twice_local",
        1,
    ),
    (
        "open_invariant_create_credit_from_false_counterexample",
        "create_credit_in_proof/create_credit_in_proof_local",
        1,
    ),
    (
        "open_invariant_early_exit_counterexample",
        "return_early/break_early/continue_early",
        1,
    ),
    (
        "local_invariant_into_inner_alias_counterexample",
        "inv_lifetime/local_invariant_non_termination_into_inner_issue1102",
        1,
    ),
    (
        "switching_inv_to_different_const_counterexample",
        "switching_inv_to_a_different_const_should_still_use_original_const",
        1,
    ),
];

const FAIL_CLOSED_CASES: &[(&str, &str, &[&str])] = &[
    (
        "open_local_invariant_macro_boundary_fail_closed",
        "basic_usage_local direct macro boundary",
        &["Unsupported open_local_invariant!()", "unsupported macros"],
    ),
    (
        "open_atomic_invariant_macro_boundary_fail_closed",
        "basic_usage direct macro boundary",
        &["unsupported expression `macro`"],
    ),
    (
        "open_atomic_invariant_in_proof_macro_boundary_fail_closed",
        "open_inv_in_proof/open_inv_in_proof_local direct macro boundary",
        &["unsupported expression `macro`"],
    ),
    (
        "open_local_invariant_in_proof_macro_boundary_fail_closed",
        "opens_invariants_trait_method_impl3 direct macro boundary",
        &["unsupported expression `macro`"],
    ),
    (
        "tracked_open_invariant_credit_borrow_boundary_fail_closed",
        "OpenInvariantCredit tracked borrow boundary",
        &["borrow"],
    ),
    (
        "local_invariant_constant_boundary_fail_closed",
        "LocalInvariant::constant invariant-state boundary",
        &["constant"],
    ),
    (
        "local_invariant_into_inner_boundary_fail_closed",
        "inv_lifetime into_inner boundary",
        &["into_inner"],
    ),
];

#[test]
fn open_invariant_rs_port_file_is_rust_syntax() {
    let source = std::fs::read_to_string(open_invariant_port_path())
        .expect("open_invariant port should be readable");
    syn::parse_file(&source).expect("open_invariant port should parse as ordinary Rust syntax");
}

#[test]
fn open_invariant_rs_runtime_model_subset_executes() {
    open_invariant_port::test_open_invariant_runtime_model_subset();
}

#[test]
fn open_invariant_rs_runtime_wrong_close_witness_panics() {
    assert_panics(
        open_invariant_port::test_open_invariant_runtime_wrong_close_witness,
        "wrong invariant close witness",
    );
}

#[test]
fn open_invariant_rs_pinned_upstream_case_shapes_are_present() {
    let path = pinned_upstream_open_invariant_path();
    if !path.exists() {
        eprintln!(
            "skipping pinned upstream open_invariant.rs shape check; missing {}",
            path.display()
        );
        return;
    }

    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", path.display()));
    for expected in [
        "basic_usage basic_usage_local",
        "basic_usage2 basic_usage2_local",
        "inv_fail inv_fail_local",
        "nested_failure nested_failure_local",
        "nested_good nested_good_local",
        "full_call_empty full_call_empty_local",
        "open_call_full open_call_full_local",
        "empty_open empty_open_local",
        "open_inv_in_spec open_inv_in_spec_local",
        "inv_header_in_spec inv_header_in_spec_local",
        "open_inv_in_proof open_inv_in_proof_local",
        "inv_exec inv_exec_local",
        "inv_cannot_be_spec inv_cannot_be_spec_local",
        "spend_credit_twice spend_credit_twice_local",
        "create_credit_in_proof create_credit_in_proof_local",
        "#[test] exec_code_in_inv_block",
        "inv_lifetime inv_lifetime_local",
        "return_early return_early_local",
        "return_early_nested return_early_nested_local",
        "break_early break_early_local",
        "continue_early continue_early_local",
        "return_early_proof return_early_proof_local",
        "break_early_proof break_early_proof_local",
        "continue_early_proof continue_early_proof_local",
        "#[test] mixup1",
        "#[test] mixup2",
        "#[test] nest_local_loop_local",
        "#[test] never_terminate_in_invariant",
        "basic_usage",
        "basic_usage_local",
        "inv_fail",
        "nested_failure",
        "nested_good",
        "open_atomic_invariant!",
        "open_local_invariant!",
        "open_atomic_invariant_in_proof!",
        "open_local_invariant_in_proof!",
        "OpenInvariantCredit",
        "opens_invariants_concrete",
        "opens_invariants_old_fail",
        "opens_invariants_wrong_type",
        "opens_invariants_private_fn",
        "opens_invariants_mode",
        "opens_invariants_trait_method_impl",
        "opens_invariants_trait_method_impl2",
        "opens_invariants_trait_method_impl3",
        "opens_invariants_trait_method_impl4",
        "opens_invariants_trait_method_impl5",
        "local_invariant_non_termination_into_inner_issue1102",
        "inv_typ_invariants",
        "switching_inv_to_a_different_const_should_still_use_original_const",
        "traits_in_sig_issue1304",
        "opens_invariants_set",
        "opens_invariants_set_fails",
    ] {
        assert!(
            source.contains(expected),
            "pinned upstream open_invariant.rs should still contain {expected}"
        );
    }
}

#[test]
fn open_invariant_rs_expected_case_metadata_is_exact() {
    let expected_cases = expected_case_inventory();
    assert_eq!(
        open_invariant_port::open_invariant_rs_expected_cases(),
        expected_cases.as_slice()
    );

    let expected_error_patterns = expected_error_pattern_inventory();
    assert_eq!(
        open_invariant_port::open_invariant_rs_fail_closed_error_patterns(),
        expected_error_patterns.as_slice()
    );

    for (case, upstream_case, status, _) in open_invariant_port::open_invariant_rs_expected_cases()
    {
        assert!(
            matches!(*status, "verified" | "counterexample" | "error"),
            "{case} ({upstream_case}) should use an explicit non-Unknown status, got {status}"
        );
        assert_ne!(
            *status, "unknown",
            "{case} ({upstream_case}) must not treat solver Unknown as replacement evidence"
        );

        let has_error_patterns =
            open_invariant_port::open_invariant_rs_fail_closed_error_patterns()
                .iter()
                .any(|(pattern_case, patterns)| pattern_case == case && !patterns.is_empty());
        if *status == "error" {
            assert!(
                has_error_patterns,
                "{case} ({upstream_case}) should carry precise fail-closed error fragments"
            );
        } else {
            assert!(
                !has_error_patterns,
                "{case} ({upstream_case}) should not carry error fragments for {status} evidence"
            );
        }
    }
}

#[test]
fn open_invariant_rs_expected_case_metadata_matches_manifest() {
    assert_eq!(
        manifest_expected_case_metadata(),
        case_metadata_as_owned(open_invariant_port::open_invariant_rs_expected_cases()),
        "open_invariant manifest should match the port evidence/fail-closed inventory exactly"
    );
    assert_eq!(
        manifest_fail_closed_error_pattern_metadata(),
        error_patterns_as_owned(open_invariant_port::open_invariant_rs_fail_closed_error_patterns()),
        "open_invariant manifest expected_error_patterns should match focused fail-closed guards exactly"
    );
}

#[test]
fn open_invariant_rs_non_error_subset_collects_expected_obligations() {
    let path = open_invariant_port_path();
    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|err| panic!("open_invariant port should read: {err}"));
    let file = syn::parse_file(&source)
        .unwrap_or_else(|err| panic!("open_invariant port should parse: {err}"));

    for (case, upstream_case, min_obligations) in
        VERIFIED_CASES.iter().chain(COUNTEREXAMPLE_CASES.iter())
    {
        let function = file
            .items
            .iter()
            .find_map(|item| match item {
                syn::Item::Fn(function) if function.sig.ident == *case => Some(function),
                _ => None,
            })
            .unwrap_or_else(|| {
                panic!("{case} ({upstream_case}) should exist in open_invariant port")
            });
        let vc = extract_verification_conditions_with_file_context(&file, function)
            .unwrap_or_else(|err| panic!("{case} ({upstream_case}) should extract: {err}"));

        assert!(
            vc.obligations().len() >= *min_obligations,
            "{case} ({upstream_case}) should collect at least {min_obligations} obligation(s), got {}",
            vc.obligations().len()
        );
    }
}

#[test]
fn open_invariant_rs_verified_subset_verifies_from_file() {
    let path = open_invariant_port_path();
    let path = path
        .to_str()
        .expect("open_invariant port path should be UTF-8");

    for (case, upstream_case, _) in VERIFIED_CASES {
        let result = verify_case(path, case, upstream_case);
        assert!(
            matches!(result, VerifyResult::Verified),
            "{case} ({upstream_case}) should verify, got: {result:?}"
        );
    }
}

#[test]
fn open_invariant_rs_counterexample_subset_is_rejected_from_file() {
    let path = open_invariant_port_path();
    let path = path
        .to_str()
        .expect("open_invariant port path should be UTF-8");

    for (case, upstream_case, _) in COUNTEREXAMPLE_CASES {
        let result = verify_case(path, case, upstream_case);
        eprintln!("{case} ({upstream_case}) => {result:?}");
        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "{case} ({upstream_case}) should produce a counterexample, got: {result:?}"
        );
    }
}

#[test]
fn open_invariant_rs_direct_macro_boundaries_fail_closed_from_file() {
    let path = open_invariant_port_path();
    let path = path
        .to_str()
        .expect("open_invariant port path should be UTF-8");

    for (case, upstream_case, expected_terms) in FAIL_CLOSED_CASES {
        expect_error_contains(path, case, upstream_case, expected_terms);
    }
}
