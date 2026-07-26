// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Executable guards for the first upstream mut_refs_loops.rs TrustVc scout.
//!
//! These tests intentionally keep upstream mut_refs_loops.rs as an unsupported
//! gap. They pin only stable Rust-valid TrustVc behavior around direct local
//! mutable-reference writes in loop, while, continue, for-loop, nested-loop,
//! nested-while, and pre-loop reassigned-alias bodies; loop-return,
//! single-break, repeated-break, nested-break, and post-break writeback;
//! labeled-break/labeled-continue flow; aliased parameter writeback subsets;
//! concrete wrong-value counterexamples;
//! and fail-closed boundaries for Verus-only borrow-resolution/future-state
//! predicates, direct parameter writes, in-loop alias reassignment,
//! tuple-projected writes, leaked-reference reassignment, closure loop bodies,
//! and mutable-reference condition calls.

mod common;

use std::{
    collections::{BTreeMap, BTreeSet},
    path::{Path, PathBuf},
};
use trust_vc_core::{
    extract_verification_conditions_with_file_context, verify_function_from_file, VerifyResult,
};

fn mut_refs_loops_port_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/ported/mut_refs_loops.rs")
}

fn pinned_upstream_mut_refs_loops_path() -> PathBuf {
    common::pinned_verus_test_path("mut_refs_loops.rs")
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
            panic!("{case} ({upstream_case}) returned solver Unknown, which is not stable evidence: {reason}")
        }
        Ok(other) => {
            panic!("{case} ({upstream_case}) should fail closed with Error, got: {other:?}")
        }
    }
}

const VERIFIED_CASES: &[(&str, &str, usize)] = &[
    (
        "mut_refs_loop_body_local_write_verified",
        "control_flow_loops",
        2,
    ),
    (
        "mut_refs_while_body_local_write_verified",
        "control_flow_while_loops",
        2,
    ),
    (
        "mut_refs_loop_preborrow_write_before_loop_exit_verified",
        "control_flow_loops",
        2,
    ),
    (
        "mut_refs_while_preborrow_write_before_loop_exit_verified",
        "control_flow_while_loops",
        2,
    ),
    (
        "mut_refs_for_preborrow_write_before_loop_exit_verified",
        "for_loops",
        2,
    ),
    (
        "mut_refs_loop_body_local_write_continue_verified",
        "control_flow_loops",
        2,
    ),
    (
        "mut_refs_while_body_local_write_continue_verified",
        "control_flow_while_loops",
        2,
    ),
    ("mut_refs_for_body_local_write_verified", "for_loops", 2),
    (
        "mut_refs_nested_loop_local_write_labeled_break_verified",
        "control_flow_loops_nested",
        2,
    ),
    (
        "mut_refs_while_nested_loop_local_write_labeled_break_verified",
        "control_flow_while_loops_nested",
        2,
    ),
    (
        "mut_refs_nested_loop_local_write_labeled_continue_verified",
        "control_flow_loops_nested",
        2,
    ),
    (
        "mut_refs_while_nested_loop_local_write_labeled_continue_verified",
        "control_flow_while_loops_nested",
        2,
    ),
    (
        "mut_refs_loop_reassigned_alias_before_loop_body_verified",
        "control_flow_loops_nested",
        2,
    ),
    (
        "mut_refs_while_reassigned_alias_before_loop_body_verified",
        "control_flow_while_loops_nested",
        2,
    ),
    (
        "mut_refs_loop_preborrow_writeback_return_verified",
        "future_preserved_in_loop",
        2,
    ),
    (
        "mut_refs_loop_preborrow_break_then_writeback_verified",
        "future_preserved_in_loop",
        2,
    ),
    (
        "mut_refs_loop_parameter_alias_writeback_return_verified",
        "future_preserved_in_loop",
        2,
    ),
    (
        "mut_refs_loop_parameter_alias_break_then_writeback_verified",
        "future_preserved_in_loop",
        2,
    ),
    (
        "mut_refs_loop_parameter_alias_two_breaks_writeback_verified",
        "future_preserved_in_loop_fails3",
        2,
    ),
    (
        "mut_refs_loop_parameter_alias_nested_break_writeback_verified",
        "future_preserved_in_loop_fails4",
        2,
    ),
    (
        "mut_refs_loop_parameter_writeback_boundary_verified",
        "future_preserved_in_loop",
        2,
    ),
];

const COUNTEREXAMPLE_CASES: &[(&str, &str, usize)] = &[
    (
        "mut_refs_loop_body_wrong_written_value_counterexample",
        "control_flow_loops",
        1,
    ),
    (
        "mut_refs_loop_preborrow_write_before_loop_wrong_value_counterexample",
        "control_flow_loops",
        1,
    ),
    (
        "mut_refs_loop_preborrow_wrong_writeback_counterexample",
        "future_preserved_in_loop",
        1,
    ),
    (
        "mut_refs_loop_preborrow_break_wrong_writeback_counterexample",
        "future_preserved_in_loop",
        1,
    ),
    (
        "mut_refs_for_body_wrong_written_value_counterexample",
        "for_loops",
        1,
    ),
    (
        "mut_refs_loop_preborrow_two_breaks_wrong_writeback_counterexample",
        "future_preserved_in_loop_fails3",
        1,
    ),
    (
        "mut_refs_loop_reassigned_alias_before_loop_wrong_written_value_counterexample",
        "control_flow_loops_nested",
        1,
    ),
];

const FAIL_CLOSED_CASES: &[(&str, &str, &[&str])] = &[
    (
        "mut_refs_loop_has_resolved_boundary_currently_errors",
        "control_flow_loops",
        &["has_resolved", "unknown return type"],
    ),
    (
        "mut_refs_loop_after_borrow_invariant_boundary_currently_errors",
        "control_flow_loops",
        &["after_borrow", "unknown return type", "Failed to lower"],
    ),
    (
        "mut_refs_loop_final_post_state_boundary_currently_errors",
        "future_preserved_in_loop",
        &[
            "Failed to parse assert!() expression",
            "expected an expression",
            "final",
        ],
    ),
    (
        "mut_refs_loop_nested_reassigned_alias_boundary_currently_errors",
        "control_flow_loops_nested",
        &[
            "assignment through a dereferenced reference is unsupported",
            "* x_ref",
        ],
    ),
    (
        "mut_refs_while_nested_reassigned_alias_boundary_currently_errors",
        "control_flow_while_loops_nested",
        &[
            "assignment through a dereferenced reference is unsupported",
            "* x_ref",
        ],
    ),
    (
        "mut_refs_loop_tuple_field_writeback_boundary_currently_errors",
        "future_preserved_in_loop",
        &[
            "assignment through a mutable-reference projection is unsupported",
            "tuple-field",
            "pair_ref . 0",
            "field '0'",
        ],
    ),
    (
        "mut_refs_loop_nested_tuple_mut_ref_write_boundary_currently_errors",
        "future_preserved_in_loop_nested",
        &[
            "assignment through a dereferenced reference is unsupported",
            "* pair . 0",
        ],
    ),
    (
        "mut_refs_loop_parameter_reassignment_leak_boundary_currently_errors",
        "future_preserved_in_loop_fails1",
        &[
            "assignment through a dereferenced reference is unsupported",
            "* aliased_ref",
        ],
    ),
    (
        "mut_refs_loop_closure_mut_ref_body_boundary_currently_errors",
        "closure_future_preserved_in_loop",
        &[
            "assignment through a dereferenced reference is unsupported",
            "update",
            "value_ref",
        ],
    ),
    (
        "mut_refs_loop_mut_ref_condition_call_currently_errors",
        "while_loops_with_mutation_in_condition",
        &["unresolved variable `value`", "Failed to lower obligation"],
    ),
];

#[derive(Clone, Debug, Eq, PartialEq)]
struct CaseMetadata {
    case_id: String,
    upstream_case_id: String,
    expected_verdict: String,
    min_obligations: usize,
    expected_error_patterns: Vec<String>,
}

fn literal_string(expr: &syn::Expr) -> String {
    let syn::Expr::Lit(lit) = expr else {
        panic!("expected string literal");
    };
    let syn::Lit::Str(value) = &lit.lit else {
        panic!("expected string literal");
    };
    value.value()
}

fn literal_usize(expr: &syn::Expr) -> usize {
    let syn::Expr::Lit(lit) = expr else {
        panic!("expected integer literal");
    };
    let syn::Lit::Int(value) = &lit.lit else {
        panic!("expected integer literal");
    };
    value
        .base10_parse()
        .expect("min obligations should be a usize literal")
}

fn referenced_array_const(file: &syn::File, const_name: &str) -> syn::ExprArray {
    let const_item = file
        .items
        .iter()
        .find_map(|item| match item {
            syn::Item::Const(item) if item.ident == const_name => Some(item),
            _ => None,
        })
        .unwrap_or_else(|| panic!("mut_refs_loops port should define {const_name}"));

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
    let array = referenced_array_const(file, "MUT_REFS_LOOPS_RS_EXPECTED_ERROR_PATTERNS");
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
    let array = referenced_array_const(file, "MUT_REFS_LOOPS_RS_EXPECTED_CASES");
    let mut error_patterns = error_pattern_entries(file);
    let mut seen = BTreeSet::new();
    let mut entries = Vec::new();

    for entry in &array.elems {
        let syn::Expr::Tuple(tuple) = entry else {
            panic!("expected tuple expected-case metadata entry");
        };
        assert_eq!(
            tuple.elems.len(),
            4,
            "expected-case entries should have case, upstream case, verdict, and min obligations"
        );
        let case_id = literal_string(&tuple.elems[0]);
        assert!(
            seen.insert(case_id.clone()),
            "duplicate mut_refs_loops metadata for {case_id}"
        );
        entries.push(CaseMetadata {
            expected_error_patterns: error_patterns.remove(&case_id).unwrap_or_default(),
            case_id,
            upstream_case_id: literal_string(&tuple.elems[1]),
            expected_verdict: literal_string(&tuple.elems[2]),
            min_obligations: literal_usize(&tuple.elems[3]),
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
            entry["upstream_path"].as_str()
                == Some("source/rust_verify_test/tests/mut_refs_loops.rs")
        })
        .expect("Verus manifest should contain mut_refs_loops.rs row");

    row["expected_cases"]
        .as_array()
        .expect("mut_refs_loops.rs row should contain expected_cases")
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
            expected_verdict: case["expected_verdict"]
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

#[test]
fn mut_refs_loops_rs_port_file_is_rust_syntax() {
    let source = std::fs::read_to_string(mut_refs_loops_port_path())
        .expect("mut_refs_loops port should be readable");
    syn::parse_file(&source).expect("mut_refs_loops port should parse as ordinary Rust syntax");
}

#[test]
fn mut_refs_loops_rs_pinned_upstream_case_shapes_are_present() {
    let path = pinned_upstream_mut_refs_loops_path();
    if !path.exists() {
        eprintln!(
            "skipping pinned upstream mut_refs_loops.rs shape check; missing {}",
            path.display()
        );
        return;
    }

    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", path.display()));
    for expected in [
        "#[test] control_flow_loops",
        "#[test] control_flow_while_loops",
        "#[test] loop_vs_while_loop",
        "#[test] loops_resolve_depends_on_condition_branch",
        "#[test] loops_resolve_depends_on_condition_branch2",
        "#[test] control_flow_loops_nested",
        "#[test] control_flow_while_loops_nested",
        "#[test] for_loops",
        "#[test] for_loops_loop_isolation_false",
        "#[test] while_loops_with_mutation_in_condition",
        "#[test] future_preserved_in_loop",
        "#[test] future_preserved_in_loop_nested",
        "#[test] future_preserved_in_loop_fails1",
        "#[test] future_preserved_in_loop_fails2",
        "#[test] future_preserved_in_loop_fails3",
        "#[test] future_preserved_in_loop_fails4",
        "#[test] future_preserved_in_loop_needs_inv",
        "#[test] no_iso_future_preserved_in_loop_nested",
        "#[test] no_iso_future_preserved_in_loop_fails1",
        "#[test] no_iso_future_preserved_in_loop_needs_inv",
        "#[test] no_iso_future_preserved_in_loop_fails3",
        "#[test] closure_future_preserved_in_loop",
        "#[test] closure_future_preserved_in_loop_fails1",
        "#[test] no_iso_closure_future_preserved_in_loop",
        "assert(has_resolved(x_ref))",
        "after_borrow(x) == *final(x_ref)",
        "ensures *final(a) == 5",
        "ensures *final(a) === (5, 6)",
        "fn leak_ref<'a>() -> &'a mut u64",
        "let c = |a: &mut u64|",
    ] {
        assert!(
            source.contains(expected),
            "pinned upstream mut_refs_loops.rs should still contain {expected}"
        );
    }
}

#[test]
fn mut_refs_loops_rs_expected_case_metadata_is_exact() {
    let source = std::fs::read_to_string(mut_refs_loops_port_path())
        .expect("mut_refs_loops port should be readable");
    let file = syn::parse_file(&source).expect("mut_refs_loops port should parse as Rust syntax");
    assert!(
        source.contains("MUT_REFS_LOOPS_RS_EXPECTED_CASES")
            && source.contains("mut_refs_loops_rs_expected_cases")
            && source.contains("MUT_REFS_LOOPS_RS_EXPECTED_ERROR_PATTERNS")
            && source.contains("mut_refs_loops_rs_expected_error_patterns"),
        "mut_refs_loops port should expose expected-case metadata"
    );

    let actual = metadata_entries(&file);
    let expected_total =
        VERIFIED_CASES.len() + COUNTEREXAMPLE_CASES.len() + FAIL_CLOSED_CASES.len();
    assert_eq!(
        actual.len(),
        expected_total,
        "mut_refs_loops port metadata should list exactly the expected case inventory"
    );

    let actual_by_case = actual
        .iter()
        .map(|case| (case.case_id.as_str(), case))
        .collect::<BTreeMap<_, _>>();
    let check_entry = |case: &str,
                       upstream_case: &str,
                       expected_verdict: &str,
                       min_obligations: usize,
                       expected_fragments: &[&str]| {
        let actual = actual_by_case
            .get(case)
            .unwrap_or_else(|| panic!("mut_refs_loops metadata should contain {case}"));
        assert_eq!(actual.upstream_case_id, upstream_case);
        assert_eq!(actual.expected_verdict, expected_verdict);
        assert_eq!(actual.min_obligations, min_obligations);
        assert_eq!(
            actual.expected_error_patterns,
            expected_fragments
                .iter()
                .map(|fragment| (*fragment).to_string())
                .collect::<Vec<_>>()
        );
    };

    for (case, upstream_case, min_obligations) in VERIFIED_CASES {
        check_entry(case, upstream_case, "verified", *min_obligations, &[]);
    }
    for (case, upstream_case, min_obligations) in COUNTEREXAMPLE_CASES {
        check_entry(case, upstream_case, "counterexample", *min_obligations, &[]);
    }
    for (case, upstream_case, expected_fragments) in FAIL_CLOSED_CASES {
        check_entry(case, upstream_case, "error", 0, expected_fragments);
    }
}

#[test]
fn mut_refs_loops_rs_expected_case_metadata_matches_manifest() {
    let source = std::fs::read_to_string(mut_refs_loops_port_path())
        .expect("mut_refs_loops port should be readable");
    let file = syn::parse_file(&source).expect("mut_refs_loops port should parse as Rust syntax");
    assert_eq!(
        metadata_entries(&file),
        manifest_expected_metadata(),
        "mut_refs_loops.rs manifest expected_cases should match port metadata and error patterns exactly"
    );
}

#[test]
fn mut_refs_loops_rs_verified_subset_verifies_from_file() {
    let path = mut_refs_loops_port_path();
    let path = path
        .to_str()
        .expect("mut_refs_loops port path should be UTF-8");

    for (case, upstream_case, _) in VERIFIED_CASES {
        let result = verify_case(path, case, upstream_case);
        assert!(
            matches!(result, VerifyResult::Verified),
            "{case} ({upstream_case}) should verify, got: {result:?}"
        );
    }
}

#[test]
fn mut_refs_loops_rs_non_error_subset_collects_min_obligations() {
    let path = mut_refs_loops_port_path();
    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|err| panic!("mut_refs_loops port should read: {err}"));
    let file = syn::parse_file(&source)
        .unwrap_or_else(|err| panic!("mut_refs_loops port should parse: {err}"));

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
                panic!("{case} ({upstream_case}) should exist in mut_refs_loops port")
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
fn mut_refs_loops_rs_wrong_written_value_is_rejected_from_file() {
    let path = mut_refs_loops_port_path();
    let path = path
        .to_str()
        .expect("mut_refs_loops port path should be UTF-8");

    for (case, upstream_case, _) in COUNTEREXAMPLE_CASES {
        let result = verify_case(path, case, upstream_case);
        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "{case} ({upstream_case}) should produce a counterexample, got: {result:?}"
        );
    }
}

#[test]
fn mut_refs_loops_rs_has_resolved_boundary_fails_closed_from_file() {
    let path = mut_refs_loops_port_path();
    let path = path
        .to_str()
        .expect("mut_refs_loops port path should be UTF-8");

    for (case, upstream_case, expected_fragments) in FAIL_CLOSED_CASES {
        let message = fail_closed_message(path, case, upstream_case);
        assert!(
            expected_fragments
                .iter()
                .any(|expected_fragment| message.contains(expected_fragment)),
            "{case} ({upstream_case}) error should contain one of {expected_fragments:?}, got: {message}"
        );
    }
}
