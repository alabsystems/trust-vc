// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Executable guards for the first upstream mut_refs_old.rs TrustVc scout.
//!
//! These tests intentionally keep
//! `source/rust_verify_test/tests/mut_refs_old.rs` as an unsupported gap. They
//! pin only stable Rust-valid TrustVc behavior: scalar `&mut` parameter writes,
//! manual snapshot-before-write surrogates, direct current-state writes,
//! return-contract current-state subsets, stale-value counterexamples, and
//! fail-closed old/final/history mutable-reference snapshot boundaries. Solver
//! `Unknown` outcomes are not accepted as evidence here.

mod common;

use std::path::{Path, PathBuf};
use trust_vc_core::{
    extract_verification_conditions_with_file_context, verify_function_from_file, VerifyResult,
};

fn mut_refs_old_port_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/ported/mut_refs_old.rs")
}

fn pinned_upstream_mut_refs_old_path() -> PathBuf {
    common::pinned_verus_test_path("mut_refs_old.rs")
}

fn verus_manifest_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/verus-tests.json")
}

fn port_file() -> syn::File {
    let source =
        std::fs::read_to_string(mut_refs_old_port_path()).expect("mut_refs_old port is readable");
    syn::parse_file(&source).expect("mut_refs_old port parses as ordinary Rust syntax")
}

fn port_function<'a>(file: &'a syn::File, case: &str, upstream_case: &str) -> &'a syn::ItemFn {
    file.items
        .iter()
        .find_map(|item| match item {
            syn::Item::Fn(function) if function.sig.ident == case => Some(function),
            _ => None,
        })
        .unwrap_or_else(|| panic!("{case} ({upstream_case}) should exist in mut_refs_old port"))
}

fn verify_case(path: &Path, case: &str, upstream_case: &str) -> (VerifyResult, usize) {
    let path_str = path
        .to_str()
        .expect("mut_refs_old port path should be UTF-8");
    let result = verify_function_from_file(path_str, case)
        .unwrap_or_else(|err| panic!("{case} ({upstream_case}) should extract: {err}"));

    let file = port_file();
    let function = port_function(&file, case, upstream_case);
    let vc = extract_verification_conditions_with_file_context(&file, function)
        .unwrap_or_else(|err| panic!("{case} ({upstream_case}) should extract VCs: {err}"));

    (result, vc.obligations().len())
}

fn expect_fail_closed(path: &str, case: &str, upstream_case: &str, expected_terms: &[&str]) {
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
        expected_terms.iter().any(|term| message.contains(term)),
        "{case} ({upstream_case}) should report one of {expected_terms:?}, got: {message}"
    );
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

fn parse_expected_case_metadata(file: &syn::File) -> Vec<(String, String, String, usize)> {
    let const_item = file
        .items
        .iter()
        .find_map(|item| match item {
            syn::Item::Const(item) if item.ident == "MUT_REFS_OLD_RS_EXPECTED_CASES" => Some(item),
            _ => None,
        })
        .expect("mut_refs_old port should define MUT_REFS_OLD_RS_EXPECTED_CASES");

    let syn::Expr::Reference(reference) = const_item.expr.as_ref() else {
        panic!("MUT_REFS_OLD_RS_EXPECTED_CASES should be a referenced array");
    };
    let syn::Expr::Array(array) = reference.expr.as_ref() else {
        panic!("MUT_REFS_OLD_RS_EXPECTED_CASES should reference an array");
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

fn expected_fail_closed_error_pattern_metadata() -> Vec<(String, Vec<String>)> {
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
            entry["upstream_path"].as_str() == Some("source/rust_verify_test/tests/mut_refs_old.rs")
        })
        .expect("Verus manifest should contain mut_refs_old.rs row")
        .clone()
}

fn manifest_expected_case_metadata() -> Vec<(String, String, String, usize)> {
    manifest_row()["expected_cases"]
        .as_array()
        .expect("mut_refs_old manifest row should contain expected_cases")
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
        .expect("mut_refs_old manifest row should contain expected_cases")
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
        "mut_refs_old_param_current_update_verified",
        "old_in_body::test scalar &mut parameter current-state subset",
        "verified",
        2,
    ),
    (
        "mut_refs_old_param_snapshot_before_update_verified",
        "old_in_body::test scalar &mut parameter manual old snapshot subset",
        "verified",
        2,
    ),
    (
        "mut_refs_old_local_current_update_verified",
        "old_in_body::test current-state subset",
        "verified",
        2,
    ),
    (
        "mut_refs_old_local_snapshot_before_update_verified",
        "old_in_body::test manual old snapshot subset",
        "verified",
        2,
    ),
    (
        "mut_refs_old_field_current_update_verified",
        "old_in_body::test_field direct-field current-state subset",
        "verified",
        2,
    ),
    (
        "mut_refs_old_field_snapshot_before_update_verified",
        "old_in_body::test_field manual tuple-field old snapshot subset",
        "verified",
        2,
    ),
    (
        "mut_refs_old_returns_current_contract_verified",
        "mutable_param_used_in_returns current-state return-contract subset",
        "verified",
        1,
    ),
    (
        "mut_refs_old_stale_current_value_counterexample",
        "old_in_body::test_fail stale current-value assertion",
        "counterexample",
        1,
    ),
    (
        "mut_refs_old_snapshot_wrong_after_update_counterexample",
        "old_in_body::test_fail stale manual old-snapshot assertion",
        "counterexample",
        1,
    ),
    (
        "mut_refs_old_field_assert_false_counterexample",
        "old_in_body::test_field_fail explicit false assertion",
        "counterexample",
        1,
    ),
    (
        "mut_refs_old_returns_old_contract_currently_blocked",
        "mutable_param_used_in_returns old mutable-reference return contract",
        "error",
        0,
    ),
    (
        "mut_refs_old_local_old_snapshot_currently_blocked",
        "old_in_body::test old(x) snapshot boundary",
        "error",
        0,
    ),
    (
        "mut_refs_old_local_final_snapshot_currently_blocked",
        "postcondition_old_fin_tuple_ok final(value) snapshot boundary",
        "error",
        0,
    ),
    (
        "mut_refs_old_final_mut_ref_snapshot_currently_blocked",
        "postcondition_old_fin_tuple_ok *final(x) mutable-reference boundary",
        "error",
        0,
    ),
    (
        "mut_refs_old_tuple_field_old_snapshot_currently_blocked",
        "old_in_body::test_field tuple projection old(x.0) boundary",
        "error",
        0,
    ),
    (
        "mut_refs_old_nested_current_history_currently_blocked",
        "nested_mut_refs mut_ref_current history boundary",
        "error",
        0,
    ),
    (
        "mut_refs_old_nested_future_history_currently_blocked",
        "nested_mut_refs mut_ref_future history boundary",
        "error",
        0,
    ),
    (
        "mut_refs_old_spec_fn_old_snapshot_currently_blocked",
        "old_in_spec_fn old(x) spec-function boundary",
        "error",
        0,
    ),
    (
        "mut_refs_old_closure_old_snapshot_currently_blocked",
        "old_in_closure_body old(x) closure boundary",
        "error",
        0,
    ),
];

const VERIFIED_CASES: &[(&str, &str, usize)] = &[
    (
        "mut_refs_old_param_current_update_verified",
        "old_in_body::test scalar &mut parameter current-state subset",
        2,
    ),
    (
        "mut_refs_old_param_snapshot_before_update_verified",
        "old_in_body::test scalar &mut parameter manual old snapshot subset",
        2,
    ),
    (
        "mut_refs_old_local_current_update_verified",
        "old_in_body::test current-state subset",
        2,
    ),
    (
        "mut_refs_old_local_snapshot_before_update_verified",
        "old_in_body::test manual old snapshot subset",
        2,
    ),
    (
        "mut_refs_old_field_current_update_verified",
        "old_in_body::test_field direct-field current-state subset",
        2,
    ),
    (
        "mut_refs_old_field_snapshot_before_update_verified",
        "old_in_body::test_field manual tuple-field old snapshot subset",
        2,
    ),
    (
        "mut_refs_old_returns_current_contract_verified",
        "mutable_param_used_in_returns current-state return-contract subset",
        1,
    ),
];

const COUNTEREXAMPLE_CASES: &[(&str, &str, usize)] = &[
    (
        "mut_refs_old_stale_current_value_counterexample",
        "old_in_body::test_fail stale current-value assertion",
        1,
    ),
    (
        "mut_refs_old_snapshot_wrong_after_update_counterexample",
        "old_in_body::test_fail stale manual old-snapshot assertion",
        1,
    ),
    (
        "mut_refs_old_field_assert_false_counterexample",
        "old_in_body::test_field_fail explicit false assertion",
        1,
    ),
];

const FAIL_CLOSED_CASES: &[(&str, &str, &[&str])] = &[
    (
        "mut_refs_old_returns_old_contract_currently_blocked",
        "mutable_param_used_in_returns old mutable-reference return contract",
        &["unsupported expression `macro`", "old!", "macro"],
    ),
    (
        "mut_refs_old_local_old_snapshot_currently_blocked",
        "old_in_body::test old(x) snapshot boundary",
        &[
            "Unsupported old-state expression `old(...)`",
            "old-state",
            "old",
        ],
    ),
    (
        "mut_refs_old_local_final_snapshot_currently_blocked",
        "postcondition_old_fin_tuple_ok final(value) snapshot boundary",
        &[
            "Failed to parse assert!() expression",
            "expected an expression",
            "final",
        ],
    ),
    (
        "mut_refs_old_final_mut_ref_snapshot_currently_blocked",
        "postcondition_old_fin_tuple_ok *final(x) mutable-reference boundary",
        &[
            "Failed to parse assert!() expression",
            "expected an expression",
            "final",
        ],
    ),
    (
        "mut_refs_old_tuple_field_old_snapshot_currently_blocked",
        "old_in_body::test_field tuple projection old(x.0) boundary",
        &[
            "assignment through a dereferenced reference is unsupported",
            "Unsupported old-state expression `old(...)`",
            "old-state",
        ],
    ),
    (
        "mut_refs_old_nested_current_history_currently_blocked",
        "nested_mut_refs mut_ref_current history boundary",
        &["mut_ref_current", "unknown return type for function"],
    ),
    (
        "mut_refs_old_nested_future_history_currently_blocked",
        "nested_mut_refs mut_ref_future history boundary",
        &["mut_ref_future", "unknown return type for function"],
    ),
    (
        "mut_refs_old_spec_fn_old_snapshot_currently_blocked",
        "old_in_spec_fn old(x) spec-function boundary",
        &[
            "Unsupported old-state expression `old(...)`",
            "old-state",
            "old",
        ],
    ),
    (
        "mut_refs_old_closure_old_snapshot_currently_blocked",
        "old_in_closure_body old(x) closure boundary",
        &[
            "Unsupported old-state expression `old(...)`",
            "old",
            "unknown return type for function",
            "standalone closure",
        ],
    ),
];

#[test]
fn mut_refs_old_rs_port_file_is_rust_syntax() {
    let source =
        std::fs::read_to_string(mut_refs_old_port_path()).expect("mut_refs_old port is readable");
    syn::parse_file(&source).expect("mut_refs_old port parses as ordinary Rust syntax");
}

#[test]
fn mut_refs_old_rs_pinned_upstream_case_shapes_are_present() {
    let path = pinned_upstream_mut_refs_old_path();
    if !path.exists() {
        eprintln!(
            "skipping pinned upstream mut_refs_old.rs shape check; missing {}",
            path.display()
        );
        return;
    }

    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", path.display()));

    for expected in [
        "#[test] old_in_body",
        "#[test] old_in_closure_body",
        "#[test] old_in_spec_fn",
        "#[test] old_in_spec_fn_sig",
        "#[test] old_of_local",
        "#[test] postcondition_missing_old",
        "#[test] postcondition_missing_old_for_return_is_ok",
        "#[test] postcondition_old_fin_tuple_ok",
        "#[test] postcondition_old_fin_tuple_ok_2",
        "#[test] old_containing_fin",
        "#[test] fin_containing_old",
        "#[test] nested_mut_refs",
        "#[test] test_assert_by",
        "#[test] test_assert_forall",
        "#[test] test_assert_nonlinear",
        "#[test] old_in_closure_referring_to_outer_param",
        "#[test] mutable_param_used_in_opens_invariants",
        "#[test] mutable_param_used_in_decreases",
        "#[test] mutable_param_used_in_returns",
        "#[test] mutable_param_used_in_unwind_spec",
        "assert(*old(x) == 0);",
        "ensures *final(x.1) == *old(x.1) + 1",
        "mut_ref_current(mut_ref_current(x))",
        "mut_ref_future(mut_ref_future(x))",
        "returns *old(x)",
        "no_unwind when *x != 0",
    ] {
        assert!(
            source.contains(expected),
            "pinned upstream mut_refs_old.rs should still contain {expected}"
        );
    }
}

#[test]
fn mut_refs_old_rs_expected_case_metadata_is_exact() {
    let file = port_file();
    let actual = parse_expected_case_metadata(&file);
    let expected: Vec<_> = EXPECTED_CASE_METADATA
        .iter()
        .map(|(case, upstream_case, status, min_obligations)| {
            (
                (*case).to_string(),
                (*upstream_case).to_string(),
                (*status).to_string(),
                *min_obligations,
            )
        })
        .collect();

    assert_eq!(
        actual, expected,
        "mut_refs_old port metadata should exactly match the regression inventory"
    );
}

#[test]
fn mut_refs_old_rs_expected_case_metadata_matches_manifest() {
    let file = port_file();
    assert_eq!(
        parse_expected_case_metadata(&file),
        manifest_expected_case_metadata(),
        "mut_refs_old port metadata should match the manifest inventory exactly"
    );
    assert_eq!(
        expected_fail_closed_error_pattern_metadata(),
        manifest_fail_closed_error_pattern_metadata(),
        "mut_refs_old fail-closed metadata should match manifest expected_error_patterns exactly"
    );
}

#[test]
fn mut_refs_old_rs_verified_subset_verifies_from_file() {
    let path = mut_refs_old_port_path();

    for (case, upstream_case, min_obligations) in VERIFIED_CASES {
        let (result, obligations) = verify_case(&path, case, upstream_case);
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
fn mut_refs_old_rs_stale_current_value_is_rejected_from_file() {
    let path = mut_refs_old_port_path();

    for (case, upstream_case, min_obligations) in COUNTEREXAMPLE_CASES {
        let (result, obligations) = verify_case(&path, case, upstream_case);
        assert!(
            obligations >= *min_obligations,
            "{case} ({upstream_case}) should collect at least {min_obligations} obligation(s), got {obligations}"
        );
        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "{case} ({upstream_case}) should produce a counterexample, got: {result:?}"
        );
    }
}

#[test]
fn mut_refs_old_rs_snapshot_boundaries_fail_closed_from_file() {
    let path = mut_refs_old_port_path();
    let path = path.to_str().expect("mut_refs_old port path is UTF-8");

    for (case, upstream_case, expected_terms) in FAIL_CLOSED_CASES {
        expect_fail_closed(path, case, upstream_case, expected_terms);
    }
}
