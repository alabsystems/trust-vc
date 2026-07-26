// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Executable guards for the first upstream mut_refs_slices_arrays.rs TrustVc scout.
//!
//! These tests intentionally keep
//! `source/rust_verify_test/tests/mut_refs_slices_arrays.rs` as an unsupported
//! gap. They pin only stable fixed-array and unsized-slice mutation evidence
//! TrustVc currently verifies, stable stale-value/order counterexamples, standard
//! Rust runtime witnesses for upstream slice/array mutable-reference behavior,
//! and fail-closed boxed-slice, indexed-element mutable-reference, nested
//! tuple-field/index, evaluation-order, ref-mut-pattern, unsizing,
//! has_resolved/final/old, array-of-mut-ref, and slice-helper boundaries.
//! `Unknown` is not accepted as evidence here.

#![allow(clippy::drop_non_drop)]

mod common;

use std::collections::BTreeSet;
use std::path::{Path, PathBuf};
use trust_vc_core::{
    extract_verification_conditions_with_file_context, verify_function_from_file, VerifyResult,
};

type ExpectedCase = (&'static str, &'static str, &'static str, usize);

fn mut_refs_slices_arrays_port_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/ported/mut_refs_slices_arrays.rs")
}

fn pinned_upstream_mut_refs_slices_arrays_path() -> PathBuf {
    common::pinned_verus_test_path("mut_refs_slices_arrays.rs")
}

fn verus_manifest_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/verus-tests.json")
}

fn port_source_and_ast() -> (String, syn::File) {
    let source = std::fs::read_to_string(mut_refs_slices_arrays_port_path())
        .expect("mut_refs_slices_arrays port should be readable");
    let ast = syn::parse_file(&source)
        .expect("mut_refs_slices_arrays port should parse as ordinary Rust syntax");
    (source, ast)
}

fn port_function<'a>(file: &'a syn::File, case: &str, upstream_case: &str) -> &'a syn::ItemFn {
    file.items
        .iter()
        .find_map(|item| match item {
            syn::Item::Fn(func) if func.sig.ident == case => Some(func),
            _ => None,
        })
        .unwrap_or_else(|| {
            panic!("{case} ({upstream_case}) should exist in mut_refs_slices_arrays port")
        })
}

fn assert_not_unknown(case: &str, upstream_case: &str, result: &VerifyResult) {
    if let VerifyResult::Unknown { reason, .. } = result {
        panic!("{case} ({upstream_case}) returned solver Unknown, which is not stable evidence: {reason}");
    }
}

fn verify_case(path: &Path, case: &str, upstream_case: &str) -> (VerifyResult, usize) {
    let path_str = path
        .to_str()
        .expect("mut_refs_slices_arrays port path should be UTF-8");
    let result = verify_function_from_file(path_str, case)
        .unwrap_or_else(|err| panic!("{case} ({upstream_case}) should verify from file: {err}"));
    assert_not_unknown(case, upstream_case, &result);

    let (_source, file) = port_source_and_ast();
    let func = port_function(&file, case, upstream_case);
    let vc = extract_verification_conditions_with_file_context(&file, func)
        .unwrap_or_else(|err| panic!("{case} ({upstream_case}) should extract: {err}"));
    let obligations = vc.obligations().len();
    (result, obligations)
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
        _ => panic!("expected string literal in mut_refs_slices_arrays metadata"),
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
        _ => panic!("expected integer literal in mut_refs_slices_arrays metadata"),
    }
}

fn parse_expected_case_metadata(file: &syn::File) -> Vec<(String, String, String, usize)> {
    let const_item = file
        .items
        .iter()
        .find_map(|item| match item {
            syn::Item::Const(item) if item.ident == "MUT_REFS_SLICES_ARRAYS_RS_EXPECTED_CASES" => {
                Some(item)
            }
            _ => None,
        })
        .expect(
            "mut_refs_slices_arrays port should define MUT_REFS_SLICES_ARRAYS_RS_EXPECTED_CASES",
        );

    let syn::Expr::Reference(reference) = const_item.expr.as_ref() else {
        panic!("MUT_REFS_SLICES_ARRAYS_RS_EXPECTED_CASES should be a referenced array literal");
    };
    let syn::Expr::Array(array) = reference.expr.as_ref() else {
        panic!("MUT_REFS_SLICES_ARRAYS_RS_EXPECTED_CASES should reference an array literal");
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
                == Some("source/rust_verify_test/tests/mut_refs_slices_arrays.rs")
        })
        .expect("Verus manifest should contain mut_refs_slices_arrays.rs row")
        .clone()
}

fn manifest_expected_case_metadata() -> Vec<(String, String, String, usize)> {
    manifest_row()["expected_cases"]
        .as_array()
        .expect("mut_refs_slices_arrays manifest row should contain expected_cases")
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
        .expect("mut_refs_slices_arrays manifest row should contain expected_cases")
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
        "mut_refs_slices_arrays_assign_array_verified",
        "array_basic::test_assign_array",
        3,
    ),
    (
        "mut_refs_slices_arrays_assign_mut_ref_array_verified",
        "array_basic::test_assign_mut_ref_array",
        3,
    ),
    (
        "mut_refs_slices_arrays_assign_slice_mut_ref_verified",
        "slice_basic::test_assign_slice_mut_ref",
        3,
    ),
    (
        "mut_refs_slices_arrays_array_add_assign_verified",
        "control_flow_ordering3::test_assign_op direct fixed-array assignment-op subset",
        3,
    ),
    (
        "mut_refs_slices_arrays_assign_mut_ref_array_add_assign_verified",
        "array_basic direct fixed-array mutable-reference assignment-op subset",
        3,
    ),
    (
        "mut_refs_slices_arrays_assign_slice_mut_ref_add_assign_verified",
        "slice_basic direct mutable-slice assignment-op subset",
        3,
    ),
    (
        "mut_refs_slices_arrays_mut_ref_of_array_index_currently_blocked",
        "array_basic::test_mut_ref_of_array_index",
        1,
    ),
    (
        "mut_refs_slices_arrays_mut_ref_of_slice_index_currently_blocked",
        "slice_basic::test_mut_ref_of_slice_index",
        1,
    ),
    (
        "mut_refs_slices_arrays_mut_ref_unsizing_coercion_currently_blocked",
        "mut_ref_unsizing_coercion::test",
        3,
    ),
    (
        "mut_refs_slices_arrays_nested_fixed_array_read_currently_rejected",
        "control_flow_ordering::test_read_1 non-side-effecting nested read",
        1,
    ),
    (
        "mut_refs_slices_arrays_nested_array_index_assignment_currently_blocked",
        "control_flow_ordering::test_assign_1 non-side-effecting nested indexed assignment target",
        2,
    ),
    (
        "mut_refs_slices_arrays_nested_array_index_add_assign_currently_blocked",
        "control_flow_ordering::test_assign_op_1 non-side-effecting nested indexed assignment-op target",
        2,
    ),
    (
        "mut_refs_slices_arrays_assign_mut_ref_array_nested_currently_blocked",
        "array_basic::test_assign_mut_ref_array_nested",
        6,
    ),
    (
        "mut_refs_slices_arrays_assign_mut_ref_slice_nested_currently_blocked",
        "slice_basic::test_assign_mut_ref_slice_nested",
        6,
    ),
];

const COUNTEREXAMPLE_CASES: &[(&str, &str, usize)] = &[
    (
        "mut_refs_slices_arrays_assign_array_wrong_updated_value_counterexample",
        "array_basic::fail_assign_array stale indexed value assertion",
        1,
    ),
    (
        "mut_refs_slices_arrays_assign_array_false_tail_counterexample",
        "array_basic::fail_assign_array false tail assertion",
        1,
    ),
    (
        "mut_refs_slices_arrays_assign_mut_ref_array_wrong_updated_value_counterexample",
        "array_basic::fail_assign_mut_ref_array stale indexed value assertion",
        1,
    ),
    (
        "mut_refs_slices_arrays_assign_mut_ref_array_false_tail_counterexample",
        "array_basic::fail_assign_mut_ref_array false tail assertion",
        1,
    ),
    (
        "mut_refs_slices_arrays_assign_slice_mut_ref_wrong_updated_value_counterexample",
        "slice_basic::fail_assign_slice_mut_ref stale indexed value assertion",
        1,
    ),
    (
        "mut_refs_slices_arrays_assign_slice_mut_ref_false_tail_counterexample",
        "slice_basic::fail_assign_slice_mut_ref false tail assertion",
        1,
    ),
    (
        "mut_refs_slices_arrays_array_add_assign_wrong_updated_value_counterexample",
        "control_flow_ordering3::fails_assign_op stale assignment-op value assertion",
        1,
    ),
    (
        "mut_refs_slices_arrays_assign_mut_ref_array_add_assign_wrong_value_counterexample",
        "array_basic mutable-reference assignment-op stale value assertion",
        1,
    ),
    (
        "mut_refs_slices_arrays_assign_slice_mut_ref_add_assign_wrong_value_counterexample",
        "slice_basic mutable-slice assignment-op stale value assertion",
        1,
    ),
];

const FAIL_CLOSED_COUNTEREXAMPLE_CASES: &[(&str, &str, usize)] = &[];

const FAIL_CLOSED_CASES: &[(&str, &str, &[&str])] = &[
    (
        "mut_refs_slices_arrays_boxed_slice_assign_currently_blocked",
        "slice_basic::test_assign_slice_box",
        &["Box", "slice", "unsupported", "indexed assignment"],
    ),
    (
        "mut_refs_slices_arrays_control_flow_nested_index_assignment_currently_blocked",
        "control_flow_ordering::test_assign_1",
        &[
            "indexed assignment target is unsupported",
            "directly indexed local array/Seq variables",
        ],
    ),
    (
        "mut_refs_slices_arrays_control_flow_nested_index_read_currently_blocked",
        "control_flow_ordering::test_read_1",
        &["unresolved variable `a`", "side-effectful", "current scope"],
    ),
    (
        "mut_refs_slices_arrays_control_flow_temporary_nested_index_read_currently_blocked",
        "control_flow_ordering::test_read_2",
        &["unresolved variable `a`", "side-effectful", "current scope"],
    ),
    (
        "mut_refs_slices_arrays_rhs_first_direct_assignment_currently_blocked",
        "control_flow_ordering3::test one-dimensional RHS-first assignment ordering",
        &["unresolved variable `a`", "side-effectful", "current scope"],
    ),
    (
        "mut_refs_slices_arrays_rhs_first_direct_assignment_wrong_index_currently_blocked",
        "control_flow_ordering3::fails one-dimensional RHS-first stale-index assertion",
        &["unresolved variable `a`", "side-effectful", "current scope"],
    ),
    (
        "mut_refs_slices_arrays_let_ref_mut_array_index_currently_blocked",
        "array_basic::test_let_decl_pattern_match_mut_ref_of_array_index",
        &[
            "assignment through a dereferenced reference is unsupported",
            "unresolved variable `x_ref`",
            "ref mut",
        ],
    ),
    (
        "mut_refs_slices_arrays_match_mut_ref_array_nested_currently_blocked",
        "array_basic::test_match_mut_ref_array_nested",
        &[
            "assignment through a dereferenced reference is unsupported",
            "unresolved variable `x_ref`",
            "ref mut",
        ],
    ),
    (
        "mut_refs_slices_arrays_match_mut_ref_slice_nested_currently_blocked",
        "slice_basic::test_match_mut_ref_slice_nested",
        &[
            "assignment through a dereferenced reference is unsupported",
            "unresolved variable `x_ref`",
            "ref mut",
        ],
    ),
    (
        "mut_refs_slices_arrays_array_of_mut_refs_currently_blocked",
        "array_of_mut_refs::test_array",
        &[
            "assignment through a dereferenced reference is unsupported",
            "dereferenced reference",
            "unsupported",
        ],
    ),
    (
        "mut_refs_slices_arrays_slice_of_mut_refs_currently_blocked",
        "slice_of_mut_refs::test_slice",
        &[
            "Box",
            "has_resolved",
            "indexed assignment",
            "assignment through a dereferenced reference is unsupported",
        ],
    ),
    (
        "mut_refs_slices_arrays_has_resolved_in_index_expr_currently_blocked",
        "has_resolved_in_idx_expr::test1 has_resolved boundary",
        &["has_resolved", "unknown return type for function"],
    ),
    (
        "mut_refs_slices_arrays_slice_final_len_currently_blocked",
        "mut_ref_to_slice_len_comparison::test final(a) length boundary",
        &[
            "Failed to parse assert!() expression",
            "expected an expression",
            "final",
        ],
    ),
    (
        "mut_refs_slices_arrays_old_indexed_slice_currently_blocked",
        "slice_index_then_field_1::upd old(a) indexed mutable-reference boundary",
        &[
            "Unsupported old-state expression `old(...)`",
            "old-state",
            "old",
        ],
    ),
    (
        "mut_refs_slices_arrays_slice_first_mut_currently_blocked",
        "slices_lib_first_last_mut::test_non_emp_first_mut",
        &[
            "assignment through a dereferenced reference is unsupported",
            "first_mut",
            "unwrap",
            "Vec",
            "unknown return type",
        ],
    ),
    (
        "mut_refs_slices_arrays_slice_last_mut_currently_blocked",
        "slices_lib_first_last_mut::test_non_emp_last_mut",
        &[
            "assignment through a dereferenced reference is unsupported",
            "last_mut",
            "unwrap",
            "Vec",
            "unknown return type",
        ],
    ),
    (
        "mut_refs_slices_arrays_slice_split_at_mut_currently_blocked",
        "slices_lib_split_at::test_split_at_mut",
        &[
            "unresolved variable `a`",
            "unresolved variable `v`",
            "split_at_mut",
            "unknown return type",
            "unsupported",
        ],
    ),
    (
        "mut_refs_slices_arrays_slice_split_at_mut_end_currently_blocked",
        "slices_lib_split_at::test_split_at_mut_end",
        &[
            "unresolved variable `a`",
            "unresolved variable `v`",
            "split_at_mut",
            "unknown return type",
            "unsupported",
        ],
    ),
];

const EXPECTED_CASE_METADATA: &[ExpectedCase] = &[
    (
        "mut_refs_slices_arrays_assign_array_verified",
        "array_basic::test_assign_array",
        "verified",
        3,
    ),
    (
        "mut_refs_slices_arrays_assign_mut_ref_array_verified",
        "array_basic::test_assign_mut_ref_array",
        "verified",
        3,
    ),
    (
        "mut_refs_slices_arrays_assign_slice_mut_ref_verified",
        "slice_basic::test_assign_slice_mut_ref",
        "verified",
        3,
    ),
    (
        "mut_refs_slices_arrays_array_add_assign_verified",
        "control_flow_ordering3::test_assign_op direct fixed-array assignment-op subset",
        "verified",
        3,
    ),
    (
        "mut_refs_slices_arrays_assign_mut_ref_array_add_assign_verified",
        "array_basic direct fixed-array mutable-reference assignment-op subset",
        "verified",
        3,
    ),
    (
        "mut_refs_slices_arrays_assign_slice_mut_ref_add_assign_verified",
        "slice_basic direct mutable-slice assignment-op subset",
        "verified",
        3,
    ),
    (
        "mut_refs_slices_arrays_mut_ref_of_array_index_currently_blocked",
        "array_basic::test_mut_ref_of_array_index",
        "verified",
        1,
    ),
    (
        "mut_refs_slices_arrays_mut_ref_of_slice_index_currently_blocked",
        "slice_basic::test_mut_ref_of_slice_index",
        "verified",
        1,
    ),
    (
        "mut_refs_slices_arrays_mut_ref_unsizing_coercion_currently_blocked",
        "mut_ref_unsizing_coercion::test",
        "verified",
        3,
    ),
    (
        "mut_refs_slices_arrays_assign_array_wrong_updated_value_counterexample",
        "array_basic::fail_assign_array stale indexed value assertion",
        "counterexample",
        1,
    ),
    (
        "mut_refs_slices_arrays_assign_array_false_tail_counterexample",
        "array_basic::fail_assign_array false tail assertion",
        "counterexample",
        1,
    ),
    (
        "mut_refs_slices_arrays_assign_mut_ref_array_wrong_updated_value_counterexample",
        "array_basic::fail_assign_mut_ref_array stale indexed value assertion",
        "counterexample",
        1,
    ),
    (
        "mut_refs_slices_arrays_assign_mut_ref_array_false_tail_counterexample",
        "array_basic::fail_assign_mut_ref_array false tail assertion",
        "counterexample",
        1,
    ),
    (
        "mut_refs_slices_arrays_assign_slice_mut_ref_wrong_updated_value_counterexample",
        "slice_basic::fail_assign_slice_mut_ref stale indexed value assertion",
        "counterexample",
        1,
    ),
    (
        "mut_refs_slices_arrays_assign_slice_mut_ref_false_tail_counterexample",
        "slice_basic::fail_assign_slice_mut_ref false tail assertion",
        "counterexample",
        1,
    ),
    (
        "mut_refs_slices_arrays_array_add_assign_wrong_updated_value_counterexample",
        "control_flow_ordering3::fails_assign_op stale assignment-op value assertion",
        "counterexample",
        1,
    ),
    (
        "mut_refs_slices_arrays_assign_mut_ref_array_add_assign_wrong_value_counterexample",
        "array_basic mutable-reference assignment-op stale value assertion",
        "counterexample",
        1,
    ),
    (
        "mut_refs_slices_arrays_assign_slice_mut_ref_add_assign_wrong_value_counterexample",
        "slice_basic mutable-slice assignment-op stale value assertion",
        "counterexample",
        1,
    ),
    (
        "mut_refs_slices_arrays_nested_fixed_array_read_currently_rejected",
        "control_flow_ordering::test_read_1 non-side-effecting nested read",
        "verified",
        1,
    ),
    (
        "mut_refs_slices_arrays_boxed_slice_assign_currently_blocked",
        "slice_basic::test_assign_slice_box",
        "error",
        0,
    ),
    (
        "mut_refs_slices_arrays_assign_mut_ref_array_nested_currently_blocked",
        "array_basic::test_assign_mut_ref_array_nested",
        "verified",
        6,
    ),
    (
        "mut_refs_slices_arrays_assign_mut_ref_slice_nested_currently_blocked",
        "slice_basic::test_assign_mut_ref_slice_nested",
        "verified",
        6,
    ),
    (
        "mut_refs_slices_arrays_control_flow_nested_index_assignment_currently_blocked",
        "control_flow_ordering::test_assign_1",
        "error",
        0,
    ),
    (
        "mut_refs_slices_arrays_control_flow_nested_index_read_currently_blocked",
        "control_flow_ordering::test_read_1",
        "error",
        0,
    ),
    (
        "mut_refs_slices_arrays_control_flow_temporary_nested_index_read_currently_blocked",
        "control_flow_ordering::test_read_2",
        "error",
        0,
    ),
    (
        "mut_refs_slices_arrays_rhs_first_direct_assignment_currently_blocked",
        "control_flow_ordering3::test one-dimensional RHS-first assignment ordering",
        "error",
        0,
    ),
    (
        "mut_refs_slices_arrays_rhs_first_direct_assignment_wrong_index_currently_blocked",
        "control_flow_ordering3::fails one-dimensional RHS-first stale-index assertion",
        "error",
        0,
    ),
    (
        "mut_refs_slices_arrays_nested_array_index_assignment_currently_blocked",
        "control_flow_ordering::test_assign_1 non-side-effecting nested indexed assignment target",
        "verified",
        2,
    ),
    (
        "mut_refs_slices_arrays_nested_array_index_add_assign_currently_blocked",
        "control_flow_ordering::test_assign_op_1 non-side-effecting nested indexed assignment-op target",
        "verified",
        2,
    ),
    (
        "mut_refs_slices_arrays_let_ref_mut_array_index_currently_blocked",
        "array_basic::test_let_decl_pattern_match_mut_ref_of_array_index",
        "error",
        0,
    ),
    (
        "mut_refs_slices_arrays_match_mut_ref_array_nested_currently_blocked",
        "array_basic::test_match_mut_ref_array_nested",
        "error",
        0,
    ),
    (
        "mut_refs_slices_arrays_match_mut_ref_slice_nested_currently_blocked",
        "slice_basic::test_match_mut_ref_slice_nested",
        "error",
        0,
    ),
    (
        "mut_refs_slices_arrays_array_of_mut_refs_currently_blocked",
        "array_of_mut_refs::test_array",
        "error",
        0,
    ),
    (
        "mut_refs_slices_arrays_slice_of_mut_refs_currently_blocked",
        "slice_of_mut_refs::test_slice",
        "error",
        0,
    ),
    (
        "mut_refs_slices_arrays_has_resolved_in_index_expr_currently_blocked",
        "has_resolved_in_idx_expr::test1 has_resolved boundary",
        "error",
        0,
    ),
    (
        "mut_refs_slices_arrays_slice_final_len_currently_blocked",
        "mut_ref_to_slice_len_comparison::test final(a) length boundary",
        "error",
        0,
    ),
    (
        "mut_refs_slices_arrays_old_indexed_slice_currently_blocked",
        "slice_index_then_field_1::upd old(a) indexed mutable-reference boundary",
        "error",
        0,
    ),
    (
        "mut_refs_slices_arrays_slice_first_mut_currently_blocked",
        "slices_lib_first_last_mut::test_non_emp_first_mut",
        "error",
        0,
    ),
    (
        "mut_refs_slices_arrays_slice_last_mut_currently_blocked",
        "slices_lib_first_last_mut::test_non_emp_last_mut",
        "error",
        0,
    ),
    (
        "mut_refs_slices_arrays_slice_split_at_mut_currently_blocked",
        "slices_lib_split_at::test_split_at_mut",
        "error",
        0,
    ),
    (
        "mut_refs_slices_arrays_slice_split_at_mut_end_currently_blocked",
        "slices_lib_split_at::test_split_at_mut_end",
        "error",
        0,
    ),
];

fn assert_unique_case_ids(cases: &[ExpectedCase]) {
    let mut seen = BTreeSet::new();
    for (case, _, _, _) in cases {
        assert!(seen.insert(*case), "duplicate expected case id {case}");
    }
}

fn runtime_mut_ref_unsizing_coercion() {
    let mut a = [0u64, 1u64, 2u64];
    let a_ref: &mut [u64; 3] = &mut a;
    let a_ref2: &mut [u64] = a_ref;

    a_ref2[1usize] = 19u64;

    assert_eq!(a, [0u64, 19u64, 2u64]);
}

fn runtime_array_of_mut_refs_reassign() {
    let mut a = 0u64;
    let mut b = 1u64;
    let mut c = 2u64;
    let mut d = 3u64;
    let mut x = [&mut a, &mut b, &mut c];

    *x[0usize] = 10u64;
    *x[1usize] = 11u64;
    *x[2usize] = 12u64;
    x[2usize] = &mut d;
    *x[2usize] = 13u64;
    drop(x);

    assert_eq!(a, 10u64);
    assert_eq!(b, 11u64);
    assert_eq!(c, 12u64);
    assert_eq!(d, 13u64);
}

fn runtime_slice_first_last_mut() {
    let mut v = vec![1u64, 2u64, 3u64];
    let first = v
        .as_mut_slice()
        .first_mut()
        .expect("non-empty slice has first_mut");
    *first = 10u64;

    let last = v
        .as_mut_slice()
        .last_mut()
        .expect("non-empty slice has last_mut");
    *last = 30u64;

    assert_eq!(v, vec![10u64, 2u64, 30u64]);
}

fn runtime_slice_empty_first_last_mut() {
    let mut v: Vec<u64> = vec![];

    assert!(v.as_mut_slice().first_mut().is_none());
    assert!(v.as_mut_slice().last_mut().is_none());
    assert!(v.is_empty());
}

fn runtime_slice_split_at_mut() {
    let mut v = vec![1u64, 2u64, 3u64];
    let (left, right) = v.as_mut_slice().split_at_mut(2usize);

    left[1usize] = 20u64;
    right[0usize] = 30u64;

    assert_eq!(v, vec![1u64, 20u64, 30u64]);
}

fn runtime_slice_split_at_mut_end() {
    let mut v = vec![1u64, 2u64, 3u64];
    let (left, right) = v.as_mut_slice().split_at_mut(3usize);

    left[1usize] = 20u64;

    assert_eq!(left, &[1u64, 20u64, 3u64]);
    assert!(right.is_empty());
    assert_eq!(v, vec![1u64, 20u64, 3u64]);
}

fn runtime_slice_index_then_field_updates() {
    let mut pairs = [(0u64, 1u64), (2u64, 3u64), (4u64, 5u64)];
    let s: &mut [(u64, u64)] = &mut pairs;

    s[0usize].0 += 100u64;
    s[0usize].1 += 200u64;
    s[1usize].1 += 200u64;

    assert_eq!(s[0usize], (100u64, 201u64));
    assert_eq!(s[1usize], (2u64, 203u64));
    assert_eq!(s[2usize], (4u64, 5u64));
}

#[test]
fn mut_refs_slices_arrays_rs_port_file_is_rust_syntax() {
    let (_source, _ast) = port_source_and_ast();
}

#[test]
fn mut_refs_slices_arrays_rs_pinned_upstream_case_shapes_are_present() {
    let path = pinned_upstream_mut_refs_slices_arrays_path();
    if !path.exists() {
        eprintln!(
            "skipping pinned upstream mut_refs_slices_arrays.rs shape check; missing {}",
            path.display()
        );
        return;
    }

    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", path.display()));
    for expected in [
        "#[test] slice_basic",
        "#[test] array_basic",
        "#[test] slice_overflow",
        "#[test] array_overflow",
        "#[test] control_flow_ordering",
        "#[test] control_flow_ordering2",
        "#[test] control_flow_ordering3",
        "#[test] control_flow_ordering4",
        "#[test] control_flow_ordering5",
        "#[test] control_flow_ordering6",
        "#[test] array_of_mut_refs",
        "#[test] slice_of_mut_refs",
        "#[test] slices_lib_first_last_mut",
        "#[test] slices_lib_split_at",
        "#[test] slices_assign_resolving_basic",
        "#[test] mut_ref_to_slice_len_comparison",
        "#[test] mut_ref_unsizing_coercion",
        "#[test] slice_index_then_field_1",
        "#[test] has_resolved_in_idx_expr",
        "fn test_assign_slice_box",
        "fn test_assign_mut_ref_array",
        "fn test_assign_mut_ref_array_nested",
        "fn test_assign_mut_ref_slice_nested",
        "fn test_mut_ref_of_array_index",
        "fn test_let_decl_pattern_match_mut_ref_of_array_index",
        "fn test_match_mut_ref_array_nested",
        "fn test_match_mut_ref_slice_nested",
        "fn test_assign_1",
        "fn test_assign_op_1",
        "fn test_read_1",
        "fn test_read_2",
        "fn test_array()",
        "fn test_slice(x: Box<[&mut u64]>)",
        "fn test_non_emp_first_mut()",
        "fn test_non_emp_last_mut()",
        "fn test_split_at_mut()",
        "fn test_split_at_mut_end()",
        "fn test_same_idx_diff_fields",
        "assert(has_resolved(a_ref));",
        "assert(a@.len() == final(a)@.len());",
        "*final(a) == *old(a) + 100",
    ] {
        assert!(
            source.contains(expected),
            "pinned upstream mut_refs_slices_arrays.rs should still contain {expected}"
        );
    }
}

#[test]
fn mut_refs_slices_arrays_rs_expected_case_metadata_is_exact() {
    assert_unique_case_ids(EXPECTED_CASE_METADATA);

    let (source, ast) = port_source_and_ast();
    assert!(
        source.contains("MUT_REFS_SLICES_ARRAYS_RS_EXPECTED_CASES")
            && source.contains("mut_refs_slices_arrays_rs_expected_cases"),
        "mut_refs_slices_arrays port should expose expected-case metadata"
    );

    let actual = parse_expected_case_metadata(&ast);
    assert_eq!(
        actual,
        expected_cases_as_owned(EXPECTED_CASE_METADATA),
        "mut_refs_slices_arrays port metadata should exactly match the regression inventory"
    );
}

#[test]
fn mut_refs_slices_arrays_rs_expected_case_metadata_matches_manifest() {
    let (_source, ast) = port_source_and_ast();
    assert_eq!(
        parse_expected_case_metadata(&ast),
        manifest_expected_case_metadata(),
        "mut_refs_slices_arrays port metadata should match the manifest inventory exactly"
    );
    assert_eq!(
        fail_closed_error_patterns_as_owned(),
        manifest_fail_closed_error_pattern_metadata(),
        "mut_refs_slices_arrays fail-closed metadata should match manifest expected_error_patterns exactly"
    );
}

#[test]
fn mut_refs_slices_arrays_rs_expected_case_statuses_are_stable_evidence() {
    let (_source, ast) = port_source_and_ast();
    let actual = parse_expected_case_metadata(&ast);

    let error_cases: BTreeSet<_> = FAIL_CLOSED_CASES.iter().map(|(case, _, _)| *case).collect();
    let metadata_error_cases: BTreeSet<_> = actual
        .iter()
        .filter_map(|(case, _, status, _)| (status.as_str() == "error").then_some(case.as_str()))
        .collect();
    assert_eq!(
        error_cases, metadata_error_cases,
        "every metadata error case should have a pinned diagnostic fragment"
    );

    for (case, upstream_case, status, min_obligations) in actual {
        match status.as_str() {
            "verified" | "counterexample" => assert!(
                min_obligations > 0,
                "{case} ({upstream_case}) should pin at least one verification obligation"
            ),
            "error" => assert_eq!(
                min_obligations, 0,
                "{case} ({upstream_case}) error metadata should not claim obligations"
            ),
            "Unknown" | "unknown" => {
                panic!("{case} ({upstream_case}) must not inventory Unknown as evidence")
            }
            other => {
                panic!("{case} ({upstream_case}) has unsupported expected-case status {other:?}")
            }
        }
    }
}

#[test]
fn mut_refs_slices_arrays_rs_runtime_witnesses_execute_std_behavior() {
    runtime_mut_ref_unsizing_coercion();
    runtime_array_of_mut_refs_reassign();
    runtime_slice_first_last_mut();
    runtime_slice_empty_first_last_mut();
    runtime_slice_split_at_mut();
    runtime_slice_split_at_mut_end();
    runtime_slice_index_then_field_updates();
}

#[test]
fn mut_refs_slices_arrays_rs_verified_subset_verifies_from_file() {
    let path = mut_refs_slices_arrays_port_path();

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
fn mut_refs_slices_arrays_rs_stale_array_value_is_rejected_from_file() {
    let path = mut_refs_slices_arrays_port_path();

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
fn mut_refs_slices_arrays_rs_unsupported_valid_nested_read_fails_closed_from_file() {
    let path = mut_refs_slices_arrays_port_path();

    for (case, upstream_case, min_obligations) in FAIL_CLOSED_COUNTEREXAMPLE_CASES {
        let (result, obligations) = verify_case(&path, case, upstream_case);
        assert!(
            obligations >= *min_obligations,
            "{case} ({upstream_case}) should collect at least {min_obligations} obligation(s), got {obligations}"
        );
        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "{case} ({upstream_case}) should fail closed as a counterexample until nested fixed-array reads are modeled, got: {result:?}"
        );
    }
}

#[test]
fn mut_refs_slices_arrays_rs_slice_and_index_borrow_boundaries_fail_closed_from_file() {
    let path = mut_refs_slices_arrays_port_path();
    let path = path
        .to_str()
        .expect("mut_refs_slices_arrays port path should be UTF-8");

    for (case, upstream_case, expected_fragments) in FAIL_CLOSED_CASES {
        expect_fail_closed_error_contains_any(path, case, upstream_case, expected_fragments);
    }
}
