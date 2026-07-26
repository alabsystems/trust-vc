// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Executable guards for the first upstream mut_refs_temporaries.rs TrustVc scout.
//!
//! These tests intentionally keep
//! `source/rust_verify_test/tests/mut_refs_temporaries.rs` as an unsupported
//! gap. They pin only stable Rust-valid TrustVc evidence: value temporary
//! behavior for assignment and assignment-op, concrete counterexamples for
//! wrong value-temporary assertions, a verified direct mutable-reference
//! temporary write plus stale-writeback counterexample, a verified shared-borrow
//! value-tuple preservation witness, and fail-closed value-field-read,
//! mutable-reference shared-borrow, assignment-op through mutable references,
//! helper-returned mutable-reference, block-temporary, tuple-projected
//! mutable-reference temporary, and resolution boundaries.
//! Solver `Unknown` outcomes are not accepted as evidence here.

mod common;

use std::collections::BTreeSet;
use std::path::{Path, PathBuf};
use trust_vc_core::{verify_function_from_file, VerifyResult};

type ExpectedCase = (&'static str, &'static str, &'static str, usize);

fn mut_refs_temporaries_port_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/ported/mut_refs_temporaries.rs")
}

fn pinned_upstream_mut_refs_temporaries_path() -> PathBuf {
    common::pinned_verus_test_path("mut_refs_temporaries.rs")
}

fn verus_manifest_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/verus-tests.json")
}

fn port_source_and_ast() -> (String, syn::File) {
    let source = std::fs::read_to_string(mut_refs_temporaries_port_path())
        .expect("mut_refs_temporaries port should be readable");
    let ast = syn::parse_file(&source)
        .expect("mut_refs_temporaries port should parse as ordinary Rust syntax");
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
        _ => panic!("expected string literal in mut_refs_temporaries metadata"),
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
        _ => panic!("expected integer literal in mut_refs_temporaries metadata"),
    }
}

fn parse_expected_case_metadata(file: &syn::File) -> Vec<(String, String, String, usize)> {
    let const_item = file
        .items
        .iter()
        .find_map(|item| match item {
            syn::Item::Const(item) if item.ident == "MUT_REFS_TEMPORARIES_RS_EXPECTED_CASES" => {
                Some(item)
            }
            _ => None,
        })
        .expect("mut_refs_temporaries port should define MUT_REFS_TEMPORARIES_RS_EXPECTED_CASES");

    let syn::Expr::Reference(reference) = const_item.expr.as_ref() else {
        panic!("MUT_REFS_TEMPORARIES_RS_EXPECTED_CASES should be a referenced array literal");
    };
    let syn::Expr::Array(array) = reference.expr.as_ref() else {
        panic!("MUT_REFS_TEMPORARIES_RS_EXPECTED_CASES should reference an array literal");
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
                == Some("source/rust_verify_test/tests/mut_refs_temporaries.rs")
        })
        .expect("Verus manifest should contain mut_refs_temporaries.rs row")
        .clone()
}

fn manifest_expected_case_metadata() -> Vec<(String, String, String, usize)> {
    manifest_row()["expected_cases"]
        .as_array()
        .expect("mut_refs_temporaries manifest row should contain expected_cases")
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
        .expect("mut_refs_temporaries manifest row should contain expected_cases")
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
        "mut_refs_temporaries_tuple_value_assignment_verified",
        "temporary_place_in_assign::test3 value tuple temporary",
        "verified",
        2,
    ),
    (
        "mut_refs_temporaries_tuple_value_assign_op_verified",
        "temporary_place_in_assign_op::test3 value tuple temporary",
        "verified",
        2,
    ),
    (
        "mut_refs_temporaries_tuple_value_wrong_source_counterexample",
        "temporary_place_in_assign::test3 wrong source-local assertion",
        "counterexample",
        1,
    ),
    (
        "mut_refs_temporaries_tuple_value_assign_op_wrong_source_counterexample",
        "temporary_place_in_assign_op::test3 wrong source-local assertion",
        "counterexample",
        1,
    ),
    (
        "mut_refs_temporaries_tuple_value_field_read_currently_blocked",
        "temporary_place_in_let_stmt value tuple field-read boundary",
        "error",
        0,
    ),
    (
        "mut_refs_temporaries_direct_mut_borrow_assignment_verified",
        "temporary_place_in_assign::test2 direct temporary mutable-reference write",
        "verified",
        2,
    ),
    (
        "mut_refs_temporaries_direct_mut_borrow_stale_source_counterexample",
        "temporary_place_in_assign::test2 stale source-local assertion",
        "counterexample",
        1,
    ),
    (
        "mut_refs_temporaries_direct_mut_borrow_assign_op_currently_blocked",
        "temporary_place_in_assign_op::test2 direct temporary mutable-reference assignment-op",
        "error",
        0,
    ),
    (
        "mut_refs_temporaries_helper_returned_mut_borrow_assignment_currently_blocked",
        "temporary_place_in_assign::test1 helper-returned temporary mutable-reference write",
        "error",
        0,
    ),
    (
        "mut_refs_temporaries_tuple_mut_borrow_assignment_currently_blocked",
        "temporary_place_in_assign::test4 tuple-projected temporary mutable-reference write",
        "error",
        0,
    ),
    (
        "mut_refs_temporaries_shared_direct_mut_borrow_currently_blocked",
        "temporary_place_in_shared_borrow::test2 shared borrow of direct temporary mutable reference",
        "error",
        0,
    ),
    (
        "mut_refs_temporaries_shared_tuple_value_borrow_sources_verified",
        "temporary_place_in_shared_borrow::test3 shared borrow of value tuple temporary",
        "verified",
        2,
    ),
    (
        "mut_refs_temporaries_block_value_side_effect_currently_blocked",
        "temporary_place_unused::test5 block temporary side-effect boundary",
        "error",
        0,
    ),
    (
        "mut_refs_temporaries_block_mut_borrow_assignment_currently_blocked",
        "temporary_place_in_assign::test7 block temporary mutable-reference write",
        "error",
        0,
    ),
    (
        "mut_refs_temporaries_has_resolved_boundary_currently_blocked",
        "temporary_place_in_let_stmt::test2 has_resolved resolution predicate",
        "error",
        0,
    ),
];

const VERIFIED_CASES: &[(&str, &str)] = &[
    (
        "mut_refs_temporaries_tuple_value_assignment_verified",
        "temporary_place_in_assign::test3 value tuple temporary",
    ),
    (
        "mut_refs_temporaries_tuple_value_assign_op_verified",
        "temporary_place_in_assign_op::test3 value tuple temporary",
    ),
    (
        "mut_refs_temporaries_direct_mut_borrow_assignment_verified",
        "temporary_place_in_assign::test2 direct temporary mutable-reference write",
    ),
    (
        "mut_refs_temporaries_shared_tuple_value_borrow_sources_verified",
        "temporary_place_in_shared_borrow::test3 shared borrow of value tuple temporary",
    ),
];

const COUNTEREXAMPLE_CASES: &[(&str, &str)] = &[
    (
        "mut_refs_temporaries_tuple_value_wrong_source_counterexample",
        "temporary_place_in_assign::test3 wrong source-local assertion",
    ),
    (
        "mut_refs_temporaries_tuple_value_assign_op_wrong_source_counterexample",
        "temporary_place_in_assign_op::test3 wrong source-local assertion",
    ),
    (
        "mut_refs_temporaries_direct_mut_borrow_stale_source_counterexample",
        "temporary_place_in_assign::test2 stale source-local assertion",
    ),
];

const FAIL_CLOSED_CASES: &[(&str, &str, &[&str])] = &[
    (
        "mut_refs_temporaries_tuple_value_field_read_currently_blocked",
        "temporary_place_in_let_stmt value tuple field-read boundary",
        &["unresolved variable `a`", "Failed to lower obligation"],
    ),
    (
        "mut_refs_temporaries_direct_mut_borrow_assign_op_currently_blocked",
        "temporary_place_in_assign_op::test2 direct temporary mutable-reference assignment-op",
        &[
            "assignment through a dereferenced reference is unsupported",
            "dereferenced reference",
        ],
    ),
    (
        "mut_refs_temporaries_helper_returned_mut_borrow_assignment_currently_blocked",
        "temporary_place_in_assign::test1 helper-returned temporary mutable-reference write",
        &[
            "assignment through a dereferenced reference is unsupported",
            "dereferenced reference",
        ],
    ),
    (
        "mut_refs_temporaries_tuple_mut_borrow_assignment_currently_blocked",
        "temporary_place_in_assign::test4 tuple-projected temporary mutable-reference write",
        &[
            "assignment through a dereferenced reference is unsupported",
            "dereferenced reference",
        ],
    ),
    (
        "mut_refs_temporaries_shared_direct_mut_borrow_currently_blocked",
        "temporary_place_in_shared_borrow::test2 shared borrow of direct temporary mutable reference",
        &["unresolved variable `a`", "Failed to lower obligation"],
    ),
    (
        "mut_refs_temporaries_block_value_side_effect_currently_blocked",
        "temporary_place_unused::test5 block temporary side-effect boundary",
        &["unresolved variable `y`", "Failed to lower obligation"],
    ),
    (
        "mut_refs_temporaries_block_mut_borrow_assignment_currently_blocked",
        "temporary_place_in_assign::test7 block temporary mutable-reference write",
        &[
            "assignment through a dereferenced reference is unsupported",
            "dereferenced reference",
        ],
    ),
    (
        "mut_refs_temporaries_has_resolved_boundary_currently_blocked",
        "temporary_place_in_let_stmt::test2 has_resolved resolution predicate",
        &["has_resolved", "unknown return type"],
    ),
];

#[test]
fn mut_refs_temporaries_rs_port_file_is_rust_syntax() {
    let _ = port_source_and_ast();
}

#[test]
fn mut_refs_temporaries_rs_pinned_upstream_case_shapes_are_present() {
    let path = pinned_upstream_mut_refs_temporaries_path();
    if !path.exists() {
        eprintln!(
            "skipping pinned upstream mut_refs_temporaries.rs shape check; missing {}",
            path.display()
        );
        return;
    }

    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", path.display()));
    for expected in [
        "#[test] temporary_place_in_assign",
        "#[test] temporary_place_in_assign_op",
        "#[test] temporary_place_in_move",
        "#[test] temporary_place_ctor_update_tail",
        "#[test] temporary_place_in_let_stmt",
        "#[test] temporary_place_in_shared_borrow",
        "#[test] temporary_place_in_match",
        "#[test] mut_refs_of_mut_refs",
        "#[test] temporary_place_unused",
        "#[test] assign_eval_ordering_with_temporary",
        "*mut_ref_pairs(&mut a, &mut b).0 = 5;",
        "*(&mut a) += 5;",
        "(a, b).0 += 5;",
        "let shr = &(&mut a);",
        "let shr = &(a, b).0;",
        "has_resolved",
        "mut_ref_current",
        "mut_ref_future",
    ] {
        assert!(
            source.contains(expected),
            "pinned upstream mut_refs_temporaries.rs should still contain {expected}"
        );
    }
}

#[test]
fn mut_refs_temporaries_rs_expected_case_metadata_is_exact() {
    assert_unique_case_ids(EXPECTED_CASE_METADATA);

    let (source, ast) = port_source_and_ast();
    for expected in [
        "MUT_REFS_TEMPORARIES_RS_EXPECTED_CASES",
        "mut_refs_temporaries_rs_expected_cases",
    ] {
        assert!(
            source.contains(expected),
            "mut_refs_temporaries port metadata should contain {expected}"
        );
    }

    assert_eq!(
        parse_expected_case_metadata(&ast),
        expected_cases_as_owned(EXPECTED_CASE_METADATA),
        "mut_refs_temporaries port metadata should exactly match the regression inventory"
    );
}

#[test]
fn mut_refs_temporaries_rs_expected_case_metadata_matches_manifest() {
    let (_source, ast) = port_source_and_ast();
    assert_eq!(
        parse_expected_case_metadata(&ast),
        manifest_expected_case_metadata(),
        "mut_refs_temporaries port metadata should match the manifest inventory exactly"
    );
    assert_eq!(
        fail_closed_error_patterns_as_owned(),
        manifest_fail_closed_error_pattern_metadata(),
        "mut_refs_temporaries fail-closed metadata should match manifest expected_error_patterns exactly"
    );
}

#[test]
fn mut_refs_temporaries_rs_verified_subset_verifies_from_file() {
    let path = mut_refs_temporaries_port_path();
    let path = path
        .to_str()
        .expect("mut_refs_temporaries port path should be UTF-8");

    for (case, upstream_case) in VERIFIED_CASES {
        let result = verify_case(path, case, upstream_case);
        assert!(
            matches!(result, VerifyResult::Verified),
            "{case} ({upstream_case}) should verify, got: {result:?}"
        );
    }
}

#[test]
fn mut_refs_temporaries_rs_stale_temporary_assertions_are_rejected_from_file() {
    let path = mut_refs_temporaries_port_path();
    let path = path
        .to_str()
        .expect("mut_refs_temporaries port path should be UTF-8");

    for (case, upstream_case) in COUNTEREXAMPLE_CASES {
        let result = verify_case(path, case, upstream_case);
        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "{case} ({upstream_case}) should produce a counterexample, got: {result:?}"
        );
    }
}

#[test]
fn mut_refs_temporaries_rs_mut_ref_temporary_boundaries_fail_closed_from_file() {
    let path = mut_refs_temporaries_port_path();
    let path = path
        .to_str()
        .expect("mut_refs_temporaries port path should be UTF-8");

    for (case, upstream_case, expected_fragments) in FAIL_CLOSED_CASES {
        expect_fail_closed_error_contains_any(path, case, upstream_case, expected_fragments);
    }
}
