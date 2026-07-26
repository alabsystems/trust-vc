// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Executable guards for the first upstream mutable_params.rs TrustVc scout.
//!
//! These tests intentionally do not claim full Verus mutable-parameter parity.
//! They pin direct mutable-parameter behavior, an explicit return-statement
//! variant, direct conditional-mutation witnesses, and the repeated
//! `loop_isolation(false)` direct cases. Closure contracts, loop-return,
//! invariant, unwind, decreases, and recommends surfaces stay out of accepted
//! replacement evidence. Solver `Unknown` and the remaining currently verifying
//! semantic gap are pinned only as rejected blockers.

mod common;

use std::path::{Path, PathBuf};
use trust_vc_core::{
    extract_verification_conditions_with_file_context, verify_function_from_file, VerifyResult,
};

fn mutable_params_port_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/ported/mutable_params.rs")
}

fn mutable_params_upstream_path() -> PathBuf {
    common::pinned_verus_test_path("mutable_params.rs")
}

fn verus_manifest_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/verus-tests.json")
}

fn verify_case(path: &str, case: &str, upstream_case: &str) -> VerifyResult {
    verify_function_from_file(path, case)
        .unwrap_or_else(|err| panic!("{case} ({upstream_case}) should extract: {err}"))
}

fn fail_closed_message(path: &str, case: &str, upstream_case: &str) -> String {
    match verify_function_from_file(path, case) {
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
    }
}

fn literal_string(expr: &syn::Expr) -> String {
    match expr {
        syn::Expr::Lit(syn::ExprLit {
            lit: syn::Lit::Str(lit),
            ..
        }) => lit.value(),
        _ => panic!("expected string literal in metadata"),
    }
}

fn literal_usize(expr: &syn::Expr) -> usize {
    match expr {
        syn::Expr::Lit(syn::ExprLit {
            lit: syn::Lit::Int(lit),
            ..
        }) => lit
            .base10_parse::<usize>()
            .unwrap_or_else(|err| panic!("expected usize literal in metadata: {err}")),
        _ => panic!("expected usize literal in metadata"),
    }
}

fn parse_expected_case_metadata(source: &str) -> Vec<(String, String, String, usize)> {
    let file = syn::parse_file(source).expect("mutable_params port should parse as Rust syntax");
    let const_item = file
        .items
        .iter()
        .find_map(|item| match item {
            syn::Item::Const(item) if item.ident == "MUTABLE_PARAMS_RS_EXPECTED_CASES" => {
                Some(item)
            }
            _ => None,
        })
        .expect("mutable_params port should define MUTABLE_PARAMS_RS_EXPECTED_CASES");

    let syn::Expr::Reference(reference) = const_item.expr.as_ref() else {
        panic!("MUTABLE_PARAMS_RS_EXPECTED_CASES should be a referenced array");
    };
    let syn::Expr::Array(array) = reference.expr.as_ref() else {
        panic!("MUTABLE_PARAMS_RS_EXPECTED_CASES should reference an array");
    };

    array
        .elems
        .iter()
        .map(|entry| {
            let syn::Expr::Tuple(tuple) = entry else {
                panic!("expected tuple metadata entry");
            };
            assert_eq!(
                tuple.elems.len(),
                4,
                "metadata entries should have case, upstream case, status, and min obligations"
            );
            (
                literal_string(&tuple.elems[0]),
                literal_string(&tuple.elems[1]),
                literal_string(&tuple.elems[2]),
                literal_usize(&tuple.elems[3]),
            )
        })
        .collect()
}

fn expected_case(case: &str) -> (&'static str, &'static str, usize) {
    EXPECTED_CASE_METADATA
        .iter()
        .find_map(|(candidate, upstream_case, status, min_obligations)| {
            (*candidate == case).then_some((*upstream_case, *status, *min_obligations))
        })
        .unwrap_or_else(|| panic!("{case} should be present in expected metadata"))
}

fn accepted_manifest_metadata() -> Vec<(String, String, String, usize)> {
    EXPECTED_CASE_METADATA
        .iter()
        .filter(|(_, _, status, _)| matches!(*status, "verified" | "counterexample" | "error"))
        .map(|(case, upstream_case, status, min_obligations)| {
            (
                (*case).to_string(),
                (*upstream_case).to_string(),
                (*status).to_string(),
                *min_obligations,
            )
        })
        .collect()
}

fn fail_closed_error_patterns_as_owned() -> Vec<(String, Vec<String>)> {
    FAIL_CLOSED_CASES
        .iter()
        .map(|(case, _, patterns)| {
            (
                (*case).to_string(),
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
                == Some("source/rust_verify_test/tests/mutable_params.rs")
        })
        .expect("Verus manifest should contain mutable_params.rs row")
        .clone()
}

fn manifest_expected_case_metadata() -> Vec<(String, String, String, usize)> {
    manifest_row()["expected_cases"]
        .as_array()
        .expect("mutable_params manifest row should contain expected_cases")
        .iter()
        .map(|case| {
            (
                case["case_id"]
                    .as_str()
                    .expect("manifest case should contain case_id")
                    .to_string(),
                case["upstream_case_id"]
                    .as_str()
                    .expect("manifest case should contain upstream_case_id")
                    .to_string(),
                case["expected_verdict"]
                    .as_str()
                    .expect("manifest case should contain expected_verdict")
                    .to_string(),
                case["min_obligations"]
                    .as_u64()
                    .expect("manifest case should contain min_obligations")
                    .try_into()
                    .expect("min_obligations should fit usize"),
            )
        })
        .collect()
}

fn manifest_fail_closed_error_pattern_metadata() -> Vec<(String, Vec<String>)> {
    manifest_row()["expected_cases"]
        .as_array()
        .expect("mutable_params manifest row should contain expected_cases")
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

const EXPECTED_CASE_METADATA: &[(&str, &str, &str, usize)] = &[
    (
        "mutable_param_return_original_verified",
        "mut_param_with_loops::test",
        "verified",
        1,
    ),
    (
        "mutable_param_explicit_return_original_verified",
        "mut_param_with_loops::test explicit Rust return",
        "verified",
        1,
    ),
    (
        "mutable_param_iso_false_return_original_verified",
        "mut_param_with_loops_iso_false::test",
        "verified",
        1,
    ),
    (
        "mutable_param_conditional_snapshot_original_verified",
        "mutation_conditional_cases direct conditional snapshot subset",
        "verified",
        1,
    ),
    (
        "mutable_param_return_mutated_counterexample",
        "mut_param_with_loops::test_fails",
        "counterexample",
        1,
    ),
    (
        "mutable_param_iso_false_return_mutated_counterexample",
        "mut_param_with_loops_iso_false::test_fails",
        "counterexample",
        1,
    ),
    (
        "mutable_param_preloop_assignment_return_current_counterexample",
        "mut_param_with_loops::test_loop_fails2 direct pre-loop assignment subset",
        "counterexample",
        1,
    ),
    (
        "mutable_param_loop_return_currently_errors",
        "mut_param_with_loops::test_loop",
        "error",
        0,
    ),
    (
        "mutable_param_loop_snapshot_then_mutation_return_currently_errors",
        "mut_param_with_loops::test_loop_fails0",
        "error",
        0,
    ),
    (
        "mutable_param_loop_return_mutated_currently_errors",
        "mut_param_with_loops::test_loop_fails",
        "error",
        0,
    ),
    (
        "mutable_param_loop_preloop_mutation_return_currently_errors",
        "mut_param_with_loops::test_loop_fails2",
        "error",
        0,
    ),
    (
        "mutable_param_loop_conditional_mutation_return_currently_errors",
        "mut_param_with_loops::test_loop_fails3",
        "error",
        0,
    ),
    (
        "mutable_param_iso_false_loop_return_currently_errors",
        "mut_param_with_loops_iso_false::test_loop",
        "error",
        0,
    ),
    (
        "mutable_param_closure_application_currently_errors",
        "mut_param_on_closure_with_loops::test",
        "error",
        0,
    ),
    (
        "mutable_param_closure_mutated_application_currently_errors",
        "mut_param_on_closure_with_loops::test_fails",
        "error",
        0,
    ),
    (
        "mutable_param_iso_false_closure_application_currently_errors",
        "mut_param_on_closure_with_loops_iso_false::test",
        "error",
        0,
    ),
    (
        "mutable_param_open_atomic_invariant_boundary_currently_errors",
        "no_confusion_invariants_spec::open",
        "error",
        0,
    ),
    (
        "mutable_param_unwind_panic_boundary_currently_errors",
        "no_confusion_unwind_spec::open",
        "error",
        0,
    ),
    (
        "mutable_param_decreases_clause_currently_verifies_blocker",
        "no_confusion_decreases_clause::test",
        "verified-blocker",
        0,
    ),
    (
        "mutable_param_conditional_mutated_return_counterexample",
        "mutation_conditional_cases::test5 direct conditional mutation subset",
        "counterexample",
        1,
    ),
    (
        "mutable_param_nested_mutation_before_return_counterexample",
        "mutation_nested_loop direct nested mutation subset",
        "counterexample",
        1,
    ),
    // Re-pinned 2026-07-04 (was "unknown"): the ensures names a spec fn whose
    // body is literally `false`, so the postcondition is unsatisfiable and the
    // engine now refutes it (Counterexample postcondition, x = 0) instead of
    // returning solver Unknown — engine got stronger, no pin weakened. Kept as
    // a non-manifest "counterexample-blocker" status (recommends semantics are
    // still not modeled, so this stays out of replacement evidence; manifest
    // untouched by design this stage).
    (
        "mutable_param_ensures_recommends_currently_unknown",
        "no_confusion_ensures_recommend_check::test_ens",
        "counterexample-blocker",
        1,
    ),
];

const FAIL_CLOSED_CASES: &[(&str, &str, &[&str])] = &[
    (
        "mutable_param_loop_return_currently_errors",
        "mut_param_with_loops::test_loop",
        &[
            "nested explicit return in tail expression",
            "loop explicit return path",
        ],
    ),
    (
        "mutable_param_loop_snapshot_then_mutation_return_currently_errors",
        "mut_param_with_loops::test_loop_fails0",
        &[
            "nested explicit return in tail expression",
            "loop explicit return path",
        ],
    ),
    (
        "mutable_param_loop_return_mutated_currently_errors",
        "mut_param_with_loops::test_loop_fails",
        &[
            "nested explicit return in tail expression",
            "loop explicit return path",
        ],
    ),
    (
        "mutable_param_loop_preloop_mutation_return_currently_errors",
        "mut_param_with_loops::test_loop_fails2",
        &[
            "nested explicit return in tail expression",
            "loop explicit return path",
        ],
    ),
    (
        "mutable_param_loop_conditional_mutation_return_currently_errors",
        "mut_param_with_loops::test_loop_fails3",
        &[
            "nested explicit return in tail expression",
            "loop explicit return path",
        ],
    ),
    (
        "mutable_param_iso_false_loop_return_currently_errors",
        "mut_param_with_loops_iso_false::test_loop",
        &[
            "nested explicit return in tail expression",
            "loop explicit return path",
        ],
    ),
    (
        "mutable_param_closure_application_currently_errors",
        "mut_param_on_closure_with_loops::test",
        &["unknown return type", "standalone closure", "closure"],
    ),
    (
        "mutable_param_closure_mutated_application_currently_errors",
        "mut_param_on_closure_with_loops::test_fails",
        &["unknown return type", "standalone closure", "closure"],
    ),
    (
        "mutable_param_iso_false_closure_application_currently_errors",
        "mut_param_on_closure_with_loops_iso_false::test",
        &["unknown return type", "standalone closure", "closure"],
    ),
    (
        "mutable_param_open_atomic_invariant_boundary_currently_errors",
        "no_confusion_invariants_spec::open",
        &["unsupported macro", "open_atomic_invariant", "macro"],
    ),
    (
        "mutable_param_unwind_panic_boundary_currently_errors",
        "no_confusion_unwind_spec::open",
        &["unsupported macro", "panic", "macro"],
    ),
];

// Re-pinned 2026-07-04: previously an Unknown blocker (fragments
// "__call_recommends_mutable_params_rec_0_0" / "quantifier" / "unknown");
// the engine now genuinely refutes the unsatisfiable postcondition
// (spec fn body is `false`). Still not replacement evidence.
const COUNTEREXAMPLE_BLOCKER_CASES: &[(&str, &str, &str)] = &[(
    "mutable_param_ensures_recommends_currently_unknown",
    "no_confusion_ensures_recommend_check::test_ens",
    "postcondition",
)];

#[test]
fn mutable_params_rs_port_file_is_rust_syntax() {
    let source = std::fs::read_to_string(mutable_params_port_path())
        .expect("mutable_params port should be readable");
    syn::parse_file(&source).expect("mutable_params port should parse as ordinary Rust syntax");
}

#[test]
fn mutable_params_rs_pinned_upstream_case_shapes_are_present() {
    let path = mutable_params_upstream_path();
    if !path.exists() {
        eprintln!(
            "skipping pinned upstream mutable_params.rs shape check; missing {}",
            path.display()
        );
        return;
    }

    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", path.display()));

    for expected in [
        "#[test] mut_param_with_loops",
        "#[test] mut_param_with_loops_iso_false",
        "#[test] mut_param_on_closure_with_loops",
        "#[test] mut_param_on_closure_with_loops_iso_false",
        "#[test] no_confusion_invariants_spec",
        "#[test] no_confusion_unwind_spec",
        "#[test] no_confusion_ensures_recommend_check",
        "#[test] no_confusion_ensures_recommend_check_closure",
        "#[test] no_confusion_decreases_clause",
        "#[test] mutation_conditional_cases",
        "#[test] mutation_nested_loop",
        "fn test(mut x: u64) -> (y: u64)",
        "fn test_loop(mut x: u64) -> (y: u64)",
        "fn test_loop_fails0(mut x: u64) -> (y: u64)",
        "fn test_loop_fails(mut x: u64) -> (y: u64)",
        "fn test_loop_fails2(mut x: u64) -> (y: u64)",
        "fn test_loop_fails3(mut x: u64) -> (y: u64)",
        "fn test1(mut x: u64) -> (y: u64)",
        "fn test8(mut x: u64) -> (y: u64)",
        "ensures rec(x)",
        "open_atomic_invariant!",
        "no_unwind when x != 1",
        "decreases x",
    ] {
        assert!(
            source.contains(expected),
            "upstream mutable_params.rs should contain {expected}"
        );
    }
}

#[test]
fn mutable_params_rs_expected_case_metadata_is_exact() {
    let source = std::fs::read_to_string(mutable_params_port_path())
        .expect("mutable_params port should be readable");
    assert!(
        source.contains("mutable_params_rs_expected_cases"),
        "mutable_params port should expose its expected-case helper"
    );

    let actual = parse_expected_case_metadata(&source);
    let expected = EXPECTED_CASE_METADATA
        .iter()
        .map(|(case, upstream_case, status, min_obligations)| {
            (
                (*case).to_string(),
                (*upstream_case).to_string(),
                (*status).to_string(),
                *min_obligations,
            )
        })
        .collect::<Vec<_>>();
    assert_eq!(
        actual, expected,
        "mutable_params port metadata should exactly match the regression inventory"
    );

    for allowed_status in [
        "verified",
        "counterexample",
        "error",
        "counterexample-blocker",
        "verified-blocker",
    ] {
        assert!(
            EXPECTED_CASE_METADATA
                .iter()
                .any(|(_, _, status, _)| *status == allowed_status),
            "metadata should include at least one {allowed_status} case"
        );
    }
}

#[test]
fn mutable_params_rs_expected_case_metadata_matches_manifest_evidence_subset() {
    assert_eq!(
        manifest_expected_case_metadata(),
        accepted_manifest_metadata(),
        "mutable_params manifest should match the port evidence/fail-closed subset exactly"
    );
    assert_eq!(
        manifest_fail_closed_error_pattern_metadata(),
        fail_closed_error_patterns_as_owned(),
        "mutable_params manifest expected_error_patterns should match focused fail-closed guards exactly"
    );
}

#[test]
fn mutable_params_rs_verified_subset_verifies_from_file() {
    let path = mutable_params_port_path();
    let path = path
        .to_str()
        .expect("mutable_params port path should be UTF-8");

    for (case, upstream_case, status, _) in EXPECTED_CASE_METADATA
        .iter()
        .filter(|(_, _, status, _)| *status == "verified")
    {
        let result = verify_case(path, case, upstream_case);
        assert!(
            matches!(result, VerifyResult::Verified),
            "{case} ({upstream_case}) should verify, got: {result:?}"
        );
        assert_eq!(*status, "verified");
    }
}

#[test]
fn mutable_params_rs_extracting_subset_collects_min_obligations() {
    let path = mutable_params_port_path();
    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|err| panic!("mutable_params port should read: {err}"));
    let file = syn::parse_file(&source)
        .unwrap_or_else(|err| panic!("mutable_params port should parse: {err}"));

    for (case, upstream_case, status, min_obligations) in EXPECTED_CASE_METADATA
        .iter()
        .filter(|(_, _, status, _)| *status != "error")
    {
        let function = file
            .items
            .iter()
            .find_map(|item| match item {
                syn::Item::Fn(function) if function.sig.ident == *case => Some(function),
                _ => None,
            })
            .unwrap_or_else(|| {
                panic!("{case} ({upstream_case}) should exist in mutable_params port")
            });
        let vc = extract_verification_conditions_with_file_context(&file, function)
            .unwrap_or_else(|err| panic!("{case} ({upstream_case}) should extract: {err}"));

        assert!(
            vc.obligations().len() >= *min_obligations,
            "{case} ({upstream_case}) should collect at least {min_obligations} obligation(s), got {}",
            vc.obligations().len()
        );
        assert!(
            *status == "verified"
                || *status == "counterexample"
                || *status == "counterexample-blocker"
                || *status == "verified-blocker"
        );
    }
}

#[test]
fn mutable_params_rs_counterexample_subset_is_rejected_from_file() {
    let path = mutable_params_port_path();
    let path = path
        .to_str()
        .expect("mutable_params port path should be UTF-8");

    for (case, upstream_case, status, _) in EXPECTED_CASE_METADATA
        .iter()
        .filter(|(_, _, status, _)| *status == "counterexample")
    {
        let result = verify_case(path, case, upstream_case);
        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "{case} ({upstream_case}) should be rejected, got: {result:?}"
        );
        assert_eq!(*status, "counterexample");
    }
}

#[test]
fn mutable_params_rs_unknown_surfaces_are_rejected_as_replacement_evidence() {
    let path = mutable_params_port_path();
    let path = path
        .to_str()
        .expect("mutable_params port path should be UTF-8");

    for (case, upstream_case, expected_obligation) in COUNTEREXAMPLE_BLOCKER_CASES {
        let (_, status, _) = expected_case(case);
        assert_eq!(
            status, "counterexample-blocker",
            "{case} ({upstream_case}) should be marked as a non-evidence counterexample blocker"
        );
        match verify_function_from_file(path, case) {
            Ok(VerifyResult::Counterexample {
                obligation_name, ..
            }) => {
                assert_eq!(
                    &obligation_name, expected_obligation,
                    "{case} ({upstream_case}) should refute {expected_obligation}, got: {obligation_name}"
                );
            }
            other => {
                panic!(
                    "{case} ({upstream_case}) should be genuinely refuted (Counterexample), got: {other:?}"
                )
            }
        }
    }
}

#[test]
fn mutable_params_rs_verified_blockers_are_rejected_as_replacement_evidence() {
    let path = mutable_params_port_path();
    let path = path
        .to_str()
        .expect("mutable_params port path should be UTF-8");

    for (case, upstream_case, status, _) in EXPECTED_CASE_METADATA
        .iter()
        .filter(|(_, _, status, _)| *status == "verified-blocker")
    {
        let result = verify_case(path, case, upstream_case);
        assert!(
            matches!(result, VerifyResult::Verified),
            "{case} ({upstream_case}) currently verifies and must remain a blocker until TrustVc rejects or models the upstream semantic shape, got: {result:?}"
        );
        assert_eq!(*status, "verified-blocker");
    }
}

#[test]
fn mutable_params_rs_unsupported_surfaces_fail_closed_from_file() {
    let path = mutable_params_port_path();
    let path = path
        .to_str()
        .expect("mutable_params port path should be UTF-8");

    let metadata_error_cases = EXPECTED_CASE_METADATA
        .iter()
        .filter_map(|(case, _, status, _)| (*status == "error").then_some(*case))
        .collect::<Vec<_>>();
    let fragment_error_cases = FAIL_CLOSED_CASES
        .iter()
        .map(|(case, _, _)| *case)
        .collect::<Vec<_>>();
    assert_eq!(
        fragment_error_cases, metadata_error_cases,
        "every metadata error case should have exact fail-closed fragments"
    );

    for (case, upstream_case, expected_fragments) in FAIL_CLOSED_CASES {
        let (_, status, _) = expected_case(case);
        assert_eq!(status, "error");
        let message = fail_closed_message(path, case, upstream_case);
        assert!(
            expected_fragments
                .iter()
                .any(|expected_fragment| message.contains(expected_fragment)),
            "{case} ({upstream_case}) error should contain one of {expected_fragments:?}, got: {message}"
        );
    }
}
