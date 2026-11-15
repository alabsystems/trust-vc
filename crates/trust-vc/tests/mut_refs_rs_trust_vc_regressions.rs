// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Executable guards for the first upstream mut_refs.rs TrustVc scout.
//!
//! These tests intentionally keep
//! `source/rust_verify_test/tests/mut_refs.rs` as an unsupported gap. They pin
//! only stable source-extraction behavior: direct local mutable-reference
//! writes, field-borrow writes, copy-after-write reads, nested alias
//! reassignment, conditional local writes, scalar reborrow updates, direct and
//! aliased scalar mutable-reference parameter writes, scalar compound
//! assignment through a local alias, writes through mutable references held in
//! tuple / struct-literal locals (straight-line, branch, and after a move —
//! 2026-09-14), stale-value counterexamples, and fail-closed boundaries for
//! compound assignment through a mutable-reference field projection, alias
//! reassignment in a short-circuit operand or an assignment right-hand side,
//! primitive compound-op evaluation order, and Verus-only
//! old/final/current/future/after_borrow-state and resolvedness helpers. The
//! aggregate-held shapes that stay refused (loop-body / compound holder writes,
//! by-value tuple-of-`&mut` parameters, holder escapes) are pinned by
//! `trust-vc-core`'s `mut_ref_aggregate_holder_capability` harness and the
//! sibling mut_refs_* suites, not by a case of this port.
//! Solver `Unknown` is not accepted as expected-case evidence.

mod common;

use std::{
    collections::{BTreeMap, BTreeSet},
    path::{Path, PathBuf},
};
use trust_vc_core::{
    extract_verification_conditions_with_file_context, verify_function_from_file, VerifyResult,
};

#[derive(Debug, PartialEq, Eq)]
struct CaseMetadata {
    case_id: String,
    upstream_case_id: String,
    status: String,
    min_obligations: usize,
    expected_error_patterns: Vec<String>,
}

fn mut_refs_port_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/ported/mut_refs.rs")
}

fn pinned_upstream_mut_refs_path() -> PathBuf {
    common::pinned_verus_test_path("mut_refs.rs")
}

fn verus_manifest_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/verus-tests.json")
}

fn mut_refs_port_file() -> syn::File {
    let path = mut_refs_port_path();
    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|err| panic!("mut_refs port should read from {}: {err}", path.display()));
    syn::parse_file(&source).expect("mut_refs port should parse as ordinary Rust syntax")
}

fn verify_case(path: &Path, case: &str, upstream_case: &str) -> (VerifyResult, usize) {
    let path_str = path.to_str().expect("mut_refs port path should be UTF-8");
    let result = verify_function_from_file(path_str, case)
        .unwrap_or_else(|err| panic!("{case} ({upstream_case}) should extract: {err}"));

    let source = std::fs::read_to_string(path)
        .unwrap_or_else(|err| panic!("{} should be readable: {err}", path.display()));
    let file = syn::parse_file(&source)
        .unwrap_or_else(|err| panic!("{} should parse as Rust syntax: {err}", path.display()));
    let function = file
        .items
        .iter()
        .find_map(|item| match item {
            syn::Item::Fn(function) if function.sig.ident == case => Some(function),
            _ => None,
        })
        .unwrap_or_else(|| {
            panic!(
                "{case} ({upstream_case}) should exist in {}",
                path.display()
            )
        });
    let vc = extract_verification_conditions_with_file_context(&file, function)
        .unwrap_or_else(|err| panic!("{case} ({upstream_case}) should extract VCs: {err}"));

    (result, vc.obligations().len())
}

fn literal_string(expr: &syn::Expr) -> String {
    match expr {
        syn::Expr::Lit(syn::ExprLit {
            lit: syn::Lit::Str(lit),
            ..
        }) => lit.value(),
        _ => panic!("expected string literal in mut_refs metadata"),
    }
}

fn literal_usize(expr: &syn::Expr) -> usize {
    match expr {
        syn::Expr::Lit(syn::ExprLit {
            lit: syn::Lit::Int(lit),
            ..
        }) => lit
            .base10_parse::<usize>()
            .unwrap_or_else(|err| panic!("expected usize literal in mut_refs metadata: {err}")),
        _ => panic!("expected usize literal in mut_refs metadata"),
    }
}

fn referenced_array_const(file: &syn::File, const_name: &str) -> syn::ExprArray {
    let const_item = file
        .items
        .iter()
        .find_map(|item| match item {
            syn::Item::Const(item) if item.ident == const_name => Some(item),
            _ => None,
        })
        .unwrap_or_else(|| panic!("mut_refs port should define {const_name}"));

    let syn::Expr::Reference(reference) = const_item.expr.as_ref() else {
        panic!("{const_name} should be a referenced array");
    };
    let syn::Expr::Array(array) = reference.expr.as_ref() else {
        panic!("{const_name} should reference an array");
    };
    array.clone()
}

fn string_slice(expr: &syn::Expr) -> Vec<String> {
    let syn::Expr::Reference(reference) = expr else {
        panic!("expected referenced string-slice metadata");
    };
    let syn::Expr::Array(array) = reference.expr.as_ref() else {
        panic!("expected string-slice array metadata");
    };

    array.elems.iter().map(literal_string).collect()
}

fn error_pattern_entries(file: &syn::File) -> BTreeMap<String, Vec<String>> {
    let array = referenced_array_const(file, "MUT_REFS_RS_EXPECTED_ERROR_PATTERNS");
    let mut entries = BTreeMap::new();

    for entry in &array.elems {
        let syn::Expr::Tuple(tuple) = entry else {
            panic!("expected tuple error-pattern metadata entry");
        };
        assert_eq!(
            tuple.elems.len(),
            2,
            "error-pattern entries should have case and fragments"
        );
        let case_id = literal_string(&tuple.elems[0]);
        let patterns = string_slice(&tuple.elems[1]);
        assert!(
            entries.insert(case_id.clone(), patterns).is_none(),
            "duplicate error-pattern metadata for {case_id}"
        );
    }

    entries
}

fn metadata_entries(file: &syn::File) -> Vec<CaseMetadata> {
    let array = referenced_array_const(file, "MUT_REFS_RS_EXPECTED_CASES");
    let mut error_patterns = error_pattern_entries(file);
    let mut seen = BTreeSet::new();
    let mut entries = Vec::new();

    for entry in &array.elems {
        let syn::Expr::Tuple(tuple) = entry else {
            panic!("expected tuple metadata entry");
        };
        assert_eq!(
            tuple.elems.len(),
            4,
            "metadata entries should have case, upstream case, status, and min obligations"
        );
        let case_id = literal_string(&tuple.elems[0]);
        assert!(
            seen.insert(case_id.clone()),
            "duplicate mut_refs metadata for {case_id}"
        );
        entries.push(CaseMetadata {
            expected_error_patterns: error_patterns.remove(&case_id).unwrap_or_default(),
            case_id,
            upstream_case_id: literal_string(&tuple.elems[1]),
            status: literal_string(&tuple.elems[2]),
            min_obligations: literal_usize(&tuple.elems[3]),
        });
    }

    assert!(
        error_patterns.is_empty(),
        "error-pattern metadata should not contain orphan cases: {error_patterns:?}"
    );
    entries
}

fn expected_case(case: &str) -> (&'static str, &'static str, usize) {
    EXPECTED_CASE_METADATA
        .iter()
        .find_map(|(candidate, upstream_case, status, min_obligations)| {
            (*candidate == case).then_some((*upstream_case, *status, *min_obligations))
        })
        .unwrap_or_else(|| panic!("{case} should be present in expected metadata"))
}

fn expected_metadata_from_tests() -> Vec<CaseMetadata> {
    let mut error_patterns = BTreeMap::new();
    for (case, _, expected_fragments) in FAIL_CLOSED_CASES {
        assert!(
            error_patterns
                .insert(
                    *case,
                    expected_fragments
                        .iter()
                        .map(|fragment| (*fragment).to_string())
                        .collect::<Vec<_>>(),
                )
                .is_none(),
            "duplicate fail-closed metadata for {case}"
        );
    }

    EXPECTED_CASE_METADATA
        .iter()
        .map(
            |(case_id, upstream_case_id, status, min_obligations)| CaseMetadata {
                case_id: (*case_id).to_string(),
                upstream_case_id: (*upstream_case_id).to_string(),
                status: (*status).to_string(),
                min_obligations: *min_obligations,
                expected_error_patterns: error_patterns.remove(case_id).unwrap_or_default(),
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
            entry["upstream_path"].as_str() == Some("source/rust_verify_test/tests/mut_refs.rs")
        })
        .expect("Verus manifest should contain mut_refs.rs row");

    row["expected_cases"]
        .as_array()
        .expect("mut_refs.rs row should contain expected_cases")
        .iter()
        .map(|case| CaseMetadata {
            case_id: case["case_id"]
                .as_str()
                .expect("manifest case should contain case_id")
                .to_string(),
            upstream_case_id: case
                .get("upstream_case_id")
                .and_then(serde_json::Value::as_str)
                .unwrap_or("")
                .to_string(),
            status: case["expected_verdict"]
                .as_str()
                .expect("manifest case should contain expected_verdict")
                .to_string(),
            min_obligations: case["min_obligations"]
                .as_u64()
                .expect("manifest case should contain min_obligations")
                .try_into()
                .expect("min_obligations should fit usize"),
            expected_error_patterns: case
                .get("expected_error_patterns")
                .and_then(serde_json::Value::as_array)
                .map(|patterns| {
                    patterns
                        .iter()
                        .map(|pattern| {
                            pattern
                                .as_str()
                                .expect("expected_error_patterns entries should be strings")
                                .to_string()
                        })
                        .collect()
                })
                .unwrap_or_default(),
        })
        .collect()
}

fn reject_unknown(result: &VerifyResult, case: &str, upstream_case: &str) {
    if let VerifyResult::Unknown { reason, .. } = result {
        panic!("{case} ({upstream_case}) returned solver Unknown, which is not stable evidence: {reason}");
    }
}

fn expect_fail_closed_error_contains_all(
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

    for expected_fragment in expected_fragments {
        assert!(
            message.contains(expected_fragment),
            "{case} ({upstream_case}) error should contain {expected_fragment:?}, got: {message}"
        );
    }
}

const FAIL_CLOSED_CASES: &[(&str, &str, &[&str])] = &[
    (
        "mut_refs_assign_op_field_add_assign_currently_blocked",
        "assign_op_to_mut_ref::test_add_assign_fields compound field assignment boundary",
        &[
            "assignment through a mutable-reference projection is unsupported",
            "x_ref . x",
        ],
    ),
    (
        "mut_refs_short_circuit_alias_reassignment_currently_blocked",
        "control_flow_bin_ops_short_circuiting2::test_and_1 alias-reassignment evaluation-order boundary",
        &[
            "assignment through a dereferenced reference is unsupported",
            "* x_ref",
            "TrustVc only models direct writes through aliases created by `&mut local`",
        ],
    ),
    (
        "mut_refs_assign_in_rhs_alias_reassignment_currently_blocked",
        "mut_ref_assign_in_rhs::test1 assignment-RHS alias-reassignment boundary",
        &[
            "assignment through a dereferenced reference is unsupported",
            "* a_ref",
            "TrustVc only models direct writes through aliases created by `&mut local`",
        ],
    ),
    (
        "mut_refs_compound_primitive_eval_order_currently_blocked",
        "compound_op_primitive_evaluation_order::test_primitive_mut_refs boundary",
        &[
            "assignment through a dereferenced reference is unsupported in vc_extraction",
        ],
    ),
    (
        "mut_refs_has_resolved_currently_blocked",
        "test_basic::test_mut_ref_in_pair has_resolved boundary",
        &["has_resolved", "is refused"],
    ),
    (
        "mut_refs_after_borrow_currently_blocked",
        "test_after_borrow_ok after_borrow boundary",
        &["after_borrow", "is refused"],
    ),
    (
        "mut_refs_mut_ref_future_currently_blocked",
        "test_spec_functions_ok mut_ref_future boundary",
        &["mut_ref_future", "END of its borrow"],
    ),
    (
        "mut_refs_final_currently_blocked",
        "test_spec_functions_ok final boundary",
        &["final", "END of its borrow"],
    ),
    (
        "mut_refs_old_state_currently_blocked",
        "backwards_compat old-state snapshot boundary",
        &[
            "Unsupported old-state expression `old(...)`",
            "old-state",
            "old",
        ],
    ),
];

const EXPECTED_CASE_METADATA: &[(&str, &str, &str, usize)] = &[
    ("mut_refs_basic_no_update", "", "verified", 1),
    ("mut_refs_basic_direct_update", "", "verified", 2),
    (
        "mut_refs_basic_direct_update_wrong_old_value_counterexample",
        "",
        "counterexample",
        1,
    ),
    ("mut_refs_basic_field_update", "", "verified", 2),
    (
        "mut_refs_basic_field_borrow_update_verified",
        "",
        "verified",
        2,
    ),
    (
        "mut_refs_basic_reborrow_update_currently_blocked",
        "",
        "verified",
        2,
    ),
    (
        "mut_refs_basic_nested_reassign_mut_ref_verified",
        "",
        "verified",
        2,
    ),
    (
        "mut_refs_basic_nested_reassign_wrong_target_counterexample",
        "",
        "counterexample",
        1,
    ),
    (
        "mut_refs_basic_mut_ref_in_pair_write_currently_blocked",
        "",
        "verified",
        3,
    ),
    ("mut_refs_assign_op_add_assign_verified", "", "verified", 4),
    (
        "mut_refs_copy_from_behind_mut_ref_value_read_verified",
        "",
        "verified",
        2,
    ),
    (
        "mut_refs_copy_from_behind_mut_ref_wrong_value_counterexample",
        "",
        "counterexample",
        1,
    ),
    (
        "mut_refs_copy_from_behind_mut_ref_id_value_read_verified",
        "",
        "verified",
        2,
    ),
    (
        "mut_refs_auto_coerce_to_shared_borrow_verified",
        "",
        "verified",
        1,
    ),
    (
        "mut_refs_auto_coerce_to_shared_borrow_direct_call_verified",
        "",
        "verified",
        1,
    ),
    (
        "mut_refs_param_scalar_write_currently_blocked",
        "",
        "verified",
        2,
    ),
    (
        "mut_refs_param_scalar_write_via_local_alias_verified",
        "",
        "verified",
        2,
    ),
    (
        "mut_refs_assign_op_field_add_assign_currently_blocked",
        "",
        "error",
        0,
    ),
    (
        "mut_refs_control_flow_conditional_local_write_verified",
        "",
        "verified",
        2,
    ),
    (
        "mut_refs_control_flow_conditional_false_tail_counterexample",
        "",
        "counterexample",
        1,
    ),
    (
        "mut_refs_control_flow_tuple_pair_write_currently_blocked",
        "",
        "verified",
        2,
    ),
    (
        "mut_refs_moves_via_let_tuple_write_currently_blocked",
        "",
        "verified",
        3,
    ),
    (
        "mut_refs_short_circuit_alias_reassignment_currently_blocked",
        "",
        "error",
        0,
    ),
    (
        "mut_refs_assign_in_rhs_alias_reassignment_currently_blocked",
        "",
        "error",
        0,
    ),
    (
        "mut_refs_compound_primitive_eval_order_currently_blocked",
        "",
        "error",
        0,
    ),
    ("mut_refs_has_resolved_currently_blocked", "", "error", 0),
    ("mut_refs_after_borrow_currently_blocked", "", "error", 0),
    (
        "mut_refs_mut_ref_current_unconstrained_counterexample",
        "",
        "counterexample",
        1,
    ),
    (
        "mut_refs_mut_ref_current_after_write_verified",
        "",
        "verified",
        1,
    ),
    (
        "mut_refs_mut_ref_current_after_write_stale_counterexample",
        "",
        "counterexample",
        1,
    ),
    ("mut_refs_mut_ref_future_currently_blocked", "", "error", 0),
    ("mut_refs_final_currently_blocked", "", "error", 0),
    ("mut_refs_old_state_currently_blocked", "", "error", 0),
    (
        "mut_refs_two_phase_call_takes_mut_ref_verified",
        "two_phase_borrow_basic::call_takes_mut_ref mut_ref_future ensures",
        "verified",
        1,
    ),
    (
        "mut_refs_two_phase_direct_call_verified",
        "two_phase_borrow_basic::test1 caller instantiates the mut_ref_future ensures",
        "verified",
        1,
    ),
    (
        "mut_refs_two_phase_direct_call_wrong_value_counterexample",
        "two_phase_borrow_basic::test1 caller, wrong post value",
        "counterexample",
        1,
    ),
];

#[test]
fn mut_refs_rs_port_file_is_rust_syntax() {
    let source =
        std::fs::read_to_string(mut_refs_port_path()).expect("mut_refs port should be readable");
    syn::parse_file(&source).expect("mut_refs port should parse as ordinary Rust syntax");
}

#[test]
fn mut_refs_rs_pinned_upstream_case_shapes_are_present() {
    let path = pinned_upstream_mut_refs_path();
    if !path.exists() {
        eprintln!(
            "skipping pinned upstream mut_refs.rs shape check; missing {}",
            path.display()
        );
        return;
    }

    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", path.display()));
    for expected in [
        "#[test] test_basic",
        "fn test_no_update()",
        "fn test_basic_update()",
        "fn test_field_update()",
        "fn test_field_update2()",
        "fn test_reborrow()",
        "#[test] test_nested_mut_refs",
        "fn test_nested()",
        "fn test_nested_fails()",
        "#[test] copy_from_behind_mut_ref_doesnt_leave_anything_uninitialized",
        "let z = id(*x_ref);",
        "#[test] test_params",
        "fn test2(x: &mut u64)",
        "fn test2_fails(x: &mut u64)",
        "#[test] auto_coerce_to_shr_borrow",
        "fn test_shr()",
        "#[test] control_flow_conditional",
        "fn test_fails(b: bool)",
        "#[test] control_flow_conditional_with_pair",
        "#[test] control_flow_bin_ops_short_circuiting2",
        "fn test_and_1(arg1: u64, arg2: u64)",
        "#[test] test_moves_via_let_decl",
        "#[test] mut_ref_assign_in_rhs",
        "#[test] compound_op_primitive_evaluation_order",
        "fn test_primitive_mut_refs()",
        "#[test] test_after_borrow_ok",
        "#[test] test_spec_functions_ok",
        "#[test] assign_op_to_mut_ref",
        "#[test] backwards_compat",
        "fn test_add_assign(i: u64)",
        "fn test_add_assign_fields(i: u64)",
        "has_resolved(u_ref.0)",
        "after_borrow(x)",
        "mut_ref_current(x)",
        "mut_ref_future(x)",
        "*final(x)",
    ] {
        assert!(
            source.contains(expected),
            "pinned upstream mut_refs.rs should still contain {expected}"
        );
    }
}

#[test]
fn mut_refs_rs_expected_case_metadata_is_exact() {
    let file = mut_refs_port_file();
    assert!(
        std::fs::read_to_string(mut_refs_port_path())
            .expect("mut_refs port should be readable")
            .contains("mut_refs_rs_expected_cases"),
        "mut_refs port metadata should expose the expected-case inventory"
    );
    let source =
        std::fs::read_to_string(mut_refs_port_path()).expect("mut_refs port should be readable");
    assert!(
        source.contains("MUT_REFS_RS_EXPECTED_ERROR_PATTERNS")
            && source.contains("mut_refs_rs_expected_error_patterns"),
        "mut_refs port metadata should expose expected error patterns"
    );

    let actual = metadata_entries(&file);
    let expected = expected_metadata_from_tests();
    assert_eq!(
        actual, expected,
        "mut_refs port metadata should exactly match the regression inventory"
    );

    for required_status in ["verified", "counterexample", "error"] {
        assert!(
            actual.iter().any(|case| case.status == required_status),
            "metadata should include at least one {required_status} case"
        );
    }

    let mut names = std::collections::BTreeSet::new();
    for case in &actual {
        assert!(
            names.insert(case.case_id.clone()),
            "metadata should not contain duplicate case {}",
            case.case_id
        );
        assert!(
            matches!(
                case.status.as_str(),
                "verified" | "counterexample" | "error"
            ),
            "{} ({}) has schema-invalid status {}",
            case.case_id,
            case.upstream_case_id,
            case.status
        );
        assert!(
            case.status != "unknown",
            "{} ({}) must not use Unknown as expected evidence",
            case.case_id,
            case.upstream_case_id
        );
        match case.status.as_str() {
            "verified" | "counterexample" => assert!(
                case.min_obligations >= 1,
                "{} ({}) should record at least one obligation",
                case.case_id,
                case.upstream_case_id
            ),
            "error" => assert_eq!(
                case.min_obligations, 0,
                "{} ({}) error metadata should record zero obligations",
                case.case_id, case.upstream_case_id
            ),
            _ => unreachable!(),
        }
    }
}

#[test]
fn mut_refs_rs_expected_case_metadata_matches_manifest() {
    let file = mut_refs_port_file();
    assert_eq!(
        metadata_entries(&file),
        manifest_expected_metadata(),
        "mut_refs.rs manifest expected_cases should match port metadata and error patterns exactly"
    );
}

#[test]
fn mut_refs_rs_expected_case_metadata_names_exist_in_port() {
    let file = mut_refs_port_file();
    let function_names = file
        .items
        .iter()
        .filter_map(|item| match item {
            syn::Item::Fn(function) => Some(function.sig.ident.to_string()),
            _ => None,
        })
        .collect::<std::collections::BTreeSet<_>>();

    for case in metadata_entries(&file) {
        assert!(
            function_names.contains(&case.case_id),
            "metadata case {} should name a function in mut_refs port",
            case.case_id
        );
    }
}

#[test]
fn mut_refs_rs_verified_subset_verifies_from_file() {
    let path = mut_refs_port_path();

    for (case, upstream_case, status, min_obligations) in EXPECTED_CASE_METADATA
        .iter()
        .filter(|(_, _, status, _)| *status == "verified")
    {
        let (result, obligations) = verify_case(&path, case, upstream_case);
        reject_unknown(&result, case, upstream_case);
        assert!(
            obligations >= *min_obligations,
            "{case} ({upstream_case}) should collect at least {min_obligations} obligation(s), got {obligations}"
        );
        assert!(
            matches!(result, VerifyResult::Verified),
            "{case} ({upstream_case}) should verify, got: {result:?}"
        );
        assert_eq!(*status, "verified");
    }
}

#[test]
fn mut_refs_rs_direct_update_wrong_old_value_is_rejected_from_file() {
    let path = mut_refs_port_path();

    for (case, upstream_case, status, min_obligations) in EXPECTED_CASE_METADATA
        .iter()
        .filter(|(_, _, status, _)| *status == "counterexample")
    {
        let (result, obligations) = verify_case(&path, case, upstream_case);
        reject_unknown(&result, case, upstream_case);
        assert!(
            obligations >= *min_obligations,
            "{case} ({upstream_case}) should collect at least {min_obligations} obligation(s), got {obligations}"
        );
        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "{case} ({upstream_case}) should be rejected, got: {result:?}"
        );
        assert_eq!(*status, "counterexample");
    }
}

#[test]
fn mut_refs_rs_verus_only_boundaries_fail_closed_from_file() {
    let path = mut_refs_port_path();
    let path = path.to_str().expect("mut_refs port path should be UTF-8");

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

    for (case, upstream_case, expected_patterns) in FAIL_CLOSED_CASES {
        let (_, status, _) = expected_case(case);
        assert_eq!(status, "error");
        expect_fail_closed_error_contains_all(path, case, upstream_case, expected_patterns);
    }
}
