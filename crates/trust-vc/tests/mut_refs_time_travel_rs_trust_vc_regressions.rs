// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Executable guards for the first upstream mut_refs_time_travel.rs TrustVc scout.
//!
//! These tests intentionally keep
//! `source/rust_verify_test/tests/mut_refs_time_travel.rs` as an unsupported
//! gap. They pin only stable source-extraction behavior: direct local
//! and parameter mutable-reference current-state writes, snapshot-before-write
//! analogues, field-sensitive borrowed-field writes including auto-dereferenced
//! mutable-reference receivers, concrete stale-snapshot counterexamples, and
//! fail-closed boundaries for explicit dereference receiver projections,
//! Verus-only time-travel, and old-state helpers. Solver `Unknown` is not
//! accepted as evidence here.

mod common;

use std::collections::BTreeSet;
use std::path::{Path, PathBuf};
use trust_vc_core::{verify_function_from_file, VerifyResult};

type ExpectedCase = (&'static str, &'static str, &'static str, usize);

fn mut_refs_time_travel_port_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/ported/mut_refs_time_travel.rs")
}

fn pinned_upstream_mut_refs_time_travel_path() -> PathBuf {
    common::pinned_verus_test_path("mut_refs_time_travel.rs")
}

fn verus_manifest_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/verus-tests.json")
}

fn port_source_and_ast() -> (String, syn::File) {
    let source = std::fs::read_to_string(mut_refs_time_travel_port_path())
        .expect("mut_refs_time_travel port should be readable");
    let ast = syn::parse_file(&source)
        .expect("mut_refs_time_travel port should parse as ordinary Rust syntax");
    (source, ast)
}

fn verify_case(path: &str, case: &str, upstream_case: &str) -> VerifyResult {
    verify_function_from_file(path, case)
        .unwrap_or_else(|err| panic!("{case} ({upstream_case}) should extract: {err}"))
}

fn expect_fail_closed_error_contains_any(
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

fn literal_string(expr: &syn::Expr) -> String {
    match expr {
        syn::Expr::Lit(syn::ExprLit {
            lit: syn::Lit::Str(lit),
            ..
        }) => lit.value(),
        _ => panic!("expected string literal in mut_refs_time_travel metadata"),
    }
}

fn literal_usize(expr: &syn::Expr) -> usize {
    match expr {
        syn::Expr::Lit(syn::ExprLit {
            lit: syn::Lit::Int(lit),
            ..
        }) => lit
            .base10_parse()
            .expect("metadata min_obligations should parse"),
        _ => panic!("expected integer literal in mut_refs_time_travel metadata"),
    }
}

fn parse_expected_case_metadata(file: &syn::File) -> Vec<(String, String, String, usize)> {
    let const_item = file
        .items
        .iter()
        .find_map(|item| match item {
            syn::Item::Const(item) if item.ident == "MUT_REFS_TIME_TRAVEL_RS_EXPECTED_CASES" => {
                Some(item)
            }
            _ => None,
        })
        .expect("mut_refs_time_travel port should define MUT_REFS_TIME_TRAVEL_RS_EXPECTED_CASES");

    let syn::Expr::Reference(reference) = const_item.expr.as_ref() else {
        panic!("MUT_REFS_TIME_TRAVEL_RS_EXPECTED_CASES should be a referenced array literal");
    };
    let syn::Expr::Array(array) = reference.expr.as_ref() else {
        panic!("MUT_REFS_TIME_TRAVEL_RS_EXPECTED_CASES should reference an array literal");
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

fn expected_cases_as_owned(cases: &[ExpectedCase]) -> Vec<(String, String, String, usize)> {
    cases
        .iter()
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
                == Some("source/rust_verify_test/tests/mut_refs_time_travel.rs")
        })
        .expect("Verus manifest should contain mut_refs_time_travel.rs row")
        .clone()
}

fn manifest_expected_case_metadata() -> Vec<(String, String, String, usize)> {
    manifest_row()["expected_cases"]
        .as_array()
        .expect("mut_refs_time_travel manifest row should contain expected_cases")
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
        .expect("mut_refs_time_travel manifest row should contain expected_cases")
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

fn assert_unique_case_ids(cases: &[ExpectedCase]) {
    let mut seen = BTreeSet::new();
    for (case, _, _, _) in cases {
        assert!(seen.insert(*case), "duplicate expected case id {case}");
    }
}

const EXPECTED_CASE_METADATA: &[ExpectedCase] = &[
    (
        "mut_refs_time_travel_local_post_write_verified",
        "test_basic_fails post-write executable subset",
        "verified",
        2,
    ),
    (
        "mut_refs_time_travel_snapshot_before_write_verified",
        "test_ok_with_after_borrow executable snapshot subset",
        "verified",
        2,
    ),
    (
        "mut_refs_time_travel_param_current_update_verified",
        "param_old_use_ok executable current-state subset",
        "verified",
        2,
    ),
    (
        "mut_refs_time_travel_field_borrow_write_verified",
        "borrow_field_and_use_different_field field-borrow write subset",
        "verified",
        2,
    ),
    (
        "mut_refs_time_travel_field_snapshot_before_write_verified",
        "borrow_field_and_use_different_field2 different-field snapshot subset",
        "verified",
        3,
    ),
    (
        "mut_refs_time_travel_deref_different_field_current_verified",
        "borrow_field_and_use_different_field_with_deref current-state subset",
        "verified",
        2,
    ),
    (
        "mut_refs_time_travel_deref_different_field_snapshot_verified",
        "borrow_field_and_use_different_field_with_deref2 snapshot subset",
        "verified",
        3,
    ),
    (
        "mut_refs_time_travel_explicit_deref_different_field_current_currently_blocked",
        "borrow_field_and_use_different_field_with_explicit_deref current-state subset",
        "error",
        0,
    ),
    (
        "mut_refs_time_travel_explicit_deref_different_field_snapshot_currently_blocked",
        "borrow_field_and_use_different_field_with_explicit_deref2 snapshot subset",
        "error",
        0,
    ),
    (
        "mut_refs_time_travel_stale_snapshot_after_write_counterexample",
        "test_ok_with_after_borrow stale snapshot analogue",
        "counterexample",
        1,
    ),
    (
        "mut_refs_time_travel_after_borrow_currently_blocked",
        "test_ok_with_after_borrow after_borrow boundary",
        "error",
        0,
    ),
    (
        "mut_refs_time_travel_has_resolved_currently_blocked",
        "test_ok_with_has_resolved has_resolved boundary",
        "error",
        0,
    ),
    (
        "mut_refs_time_travel_old_mut_ref_snapshot_currently_blocked",
        "cant_cheat_prophecy_with_assign_in_old old(x_ref) boundary",
        "error",
        0,
    ),
    // AUDITED FLIP 2026-07-09: slice B: entry-rendered old() over an unconstrained param refutes (probed: value = 1)
    (
        "mut_refs_time_travel_param_old_snapshot_currently_blocked",
        "param_old_use_ok old(x) parameter snapshot boundary",
        "counterexample",
        1,
    ),
];

const VERIFIED_CASES: &[(&str, &str)] = &[
    (
        "mut_refs_time_travel_local_post_write_verified",
        "test_basic_fails post-write executable subset",
    ),
    (
        "mut_refs_time_travel_snapshot_before_write_verified",
        "test_ok_with_after_borrow executable snapshot subset",
    ),
    (
        "mut_refs_time_travel_param_current_update_verified",
        "param_old_use_ok executable current-state subset",
    ),
    (
        "mut_refs_time_travel_field_borrow_write_verified",
        "borrow_field_and_use_different_field field-borrow write subset",
    ),
    (
        "mut_refs_time_travel_field_snapshot_before_write_verified",
        "borrow_field_and_use_different_field2 different-field snapshot subset",
    ),
    (
        "mut_refs_time_travel_deref_different_field_current_verified",
        "borrow_field_and_use_different_field_with_deref current-state subset",
    ),
    (
        "mut_refs_time_travel_deref_different_field_snapshot_verified",
        "borrow_field_and_use_different_field_with_deref2 snapshot subset",
    ),
];

const COUNTEREXAMPLE_CASES: &[(&str, &str)] = &[(
    "mut_refs_time_travel_stale_snapshot_after_write_counterexample",
    "test_ok_with_after_borrow stale snapshot analogue",
)];

const FAIL_CLOSED_CASES: &[(&str, &str, &[&str])] = &[
    (
        "mut_refs_time_travel_explicit_deref_different_field_current_currently_blocked",
        "borrow_field_and_use_different_field_with_explicit_deref current-state subset",
        &[
            "assignment through a dereferenced reference is unsupported",
            "dereferenced reference",
        ],
    ),
    (
        "mut_refs_time_travel_explicit_deref_different_field_snapshot_currently_blocked",
        "borrow_field_and_use_different_field_with_explicit_deref2 snapshot subset",
        &[
            "assignment through a dereferenced reference is unsupported",
            "dereferenced reference",
        ],
    ),
    (
        "mut_refs_time_travel_after_borrow_currently_blocked",
        "test_ok_with_after_borrow after_borrow boundary",
        &["after_borrow", "unknown return type for function"],
    ),
    (
        "mut_refs_time_travel_has_resolved_currently_blocked",
        "test_ok_with_has_resolved has_resolved boundary",
        &["has_resolved", "unknown return type for function"],
    ),
    (
        "mut_refs_time_travel_old_mut_ref_snapshot_currently_blocked",
        "cant_cheat_prophecy_with_assign_in_old old(x_ref) boundary",
        &["Unsupported old-state expression `old(...)`", "old"],
    ),
    // mut_refs_time_travel_param_old_snapshot_currently_blocked removed 2026-07-09: audited slice-B flip (see expected-cases table).
];

#[test]
fn mut_refs_time_travel_rs_port_file_is_rust_syntax() {
    let _ = port_source_and_ast();
}

#[test]
fn mut_refs_time_travel_rs_pinned_upstream_case_shapes_are_present() {
    let path = pinned_upstream_mut_refs_time_travel_path();
    if !path.exists() {
        eprintln!(
            "skipping pinned upstream mut_refs_time_travel.rs shape check; missing {}",
            path.display()
        );
        return;
    }

    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", path.display()));
    for expected in [
        "#[test] test_basic_fails",
        "#[test] test_ok_with_after_borrow",
        "#[test] test_ok_with_has_resolved",
        "#[test] borrow_field_and_use_different_field",
        "#[test] borrow_field_and_use_different_field2",
        "#[test] borrow_field_and_use_different_field_with_deref",
        "#[test] borrow_field_and_use_different_field_with_deref2",
        "#[test] borrow_field_and_use_different_field_with_explicit_deref",
        "#[test] borrow_field_and_use_different_field_with_explicit_deref2",
        "#[test] param",
        "#[test] two_phase4",
        "#[test] misc_borrows_and_reborrows",
        "assert_spec_borrowed",
        "after_borrow(x)",
        "has_resolved(x)",
        "param_ok",
    ] {
        assert!(
            source.contains(expected),
            "pinned upstream mut_refs_time_travel.rs should still contain {expected}"
        );
    }
}

#[test]
fn mut_refs_time_travel_rs_expected_case_metadata_is_exact() {
    assert_unique_case_ids(EXPECTED_CASE_METADATA);

    let (source, ast) = port_source_and_ast();
    for expected in [
        "MUT_REFS_TIME_TRAVEL_RS_EXPECTED_CASES",
        "mut_refs_time_travel_rs_expected_cases",
        "\"mut_refs_time_travel_local_post_write_verified\"",
        "\"mut_refs_time_travel_snapshot_before_write_verified\"",
        "\"mut_refs_time_travel_param_current_update_verified\"",
        "\"mut_refs_time_travel_field_borrow_write_verified\"",
        "\"mut_refs_time_travel_field_snapshot_before_write_verified\"",
        "\"mut_refs_time_travel_deref_different_field_current_verified\"",
        "\"mut_refs_time_travel_deref_different_field_snapshot_verified\"",
        "\"mut_refs_time_travel_explicit_deref_different_field_current_currently_blocked\"",
        "\"mut_refs_time_travel_explicit_deref_different_field_snapshot_currently_blocked\"",
        "\"mut_refs_time_travel_stale_snapshot_after_write_counterexample\"",
        "\"mut_refs_time_travel_after_borrow_currently_blocked\"",
        "\"mut_refs_time_travel_has_resolved_currently_blocked\"",
        "\"mut_refs_time_travel_old_mut_ref_snapshot_currently_blocked\"",
        "\"mut_refs_time_travel_param_old_snapshot_currently_blocked\"",
    ] {
        assert!(
            source.contains(expected),
            "mut_refs_time_travel port metadata should contain {expected}"
        );
    }

    assert_eq!(
        parse_expected_case_metadata(&ast),
        expected_cases_as_owned(EXPECTED_CASE_METADATA),
        "mut_refs_time_travel port metadata should exactly match the regression inventory"
    );
}

#[test]
fn mut_refs_time_travel_rs_expected_case_metadata_matches_manifest() {
    let (_source, ast) = port_source_and_ast();
    assert_eq!(
        parse_expected_case_metadata(&ast),
        manifest_expected_case_metadata(),
        "mut_refs_time_travel port metadata should match the manifest inventory exactly"
    );
    assert_eq!(
        fail_closed_error_patterns_as_owned(),
        manifest_fail_closed_error_pattern_metadata(),
        "mut_refs_time_travel fail-closed metadata should match manifest expected_error_patterns exactly"
    );
}

#[test]
fn mut_refs_time_travel_rs_verified_subset_verifies_from_file() {
    let path = mut_refs_time_travel_port_path();
    let path = path
        .to_str()
        .expect("mut_refs_time_travel port path should be UTF-8");

    for (case, upstream_case) in VERIFIED_CASES {
        let result = verify_case(path, case, upstream_case);
        assert!(
            matches!(result, VerifyResult::Verified),
            "{case} ({upstream_case}) should verify, got: {result:?}"
        );
    }
}

#[test]
fn mut_refs_time_travel_rs_stale_snapshot_is_rejected_from_file() {
    let path = mut_refs_time_travel_port_path();
    let path = path
        .to_str()
        .expect("mut_refs_time_travel port path should be UTF-8");

    for (case, upstream_case) in COUNTEREXAMPLE_CASES {
        let result = verify_case(path, case, upstream_case);
        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "{case} ({upstream_case}) should produce a counterexample, got: {result:?}"
        );
    }
}

#[test]
fn mut_refs_time_travel_rs_time_travel_boundaries_fail_closed_from_file() {
    let path = mut_refs_time_travel_port_path();
    let path = path
        .to_str()
        .expect("mut_refs_time_travel port path should be UTF-8");

    for (case, upstream_case, expected_fragments) in FAIL_CLOSED_CASES {
        expect_fail_closed_error_contains_any(path, case, upstream_case, expected_fragments);
    }
}
