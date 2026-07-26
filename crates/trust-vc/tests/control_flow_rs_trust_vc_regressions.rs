// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Executable guards for the currently ported upstream control_flow.rs subset.
//!
//! These tests intentionally do not claim full Verus control_flow.rs parity.
//! They prove only the listed upstream-derived early-return, match-arm return,
//! local-initializer return, short-circuit, and precondition-in-conditional
//! slices while the manifest keeps
//! `source/rust_verify_test/tests/control_flow.rs` fail-closed.

mod common;

use std::{
    collections::{BTreeMap, BTreeSet},
    path::{Path, PathBuf},
};
use trust_vc_core::{
    extract_verification_conditions_with_file_context, verify_function_from_file, VerifyResult,
};

fn control_flow_port_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/ported/control_flow.rs")
}

fn verus_manifest_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/verus-tests.json")
}

fn pinned_upstream_control_flow_path() -> PathBuf {
    common::pinned_verus_test_path("control_flow.rs")
}

fn verify_case(path: &str, case: &str, upstream_case: &str) -> VerifyResult {
    verify_function_from_file(path, case)
        .unwrap_or_else(|err| panic!("{case} ({upstream_case}) should extract: {err}"))
}

fn fail_closed_message(path: &str, case: &str, upstream_case: &str) -> String {
    match verify_function_from_file(path, case) {
        Ok(VerifyResult::Error { message }) => message,
        Ok(result) => {
            panic!("{case} ({upstream_case}) should fail closed with Error, got: {result:?}")
        }
        Err(err) => err.to_string(),
    }
}

fn assert_contains_any(message: &str, expected_fragments: &[&str], label: &str) {
    assert!(
        expected_fragments
            .iter()
            .any(|fragment| message.contains(fragment)),
        "{label} should contain one of {expected_fragments:?}, got: {message}"
    );
}

const VERIFIED_CASES: &[(&str, &str, usize)] = &[
    (
        "control_flow_final_stmt_return_verified",
        "distinguish_returns_and_implict_units::test_final_stmt_return",
        2,
    ),
    (
        "control_flow_tail_if_return_verified",
        "distinguish_returns_and_implict_units::test_return_from_if",
        2,
    ),
    (
        "control_flow_tail_else_return_verified",
        "distinguish_returns_and_implict_units::test_return_from_else",
        2,
    ),
    (
        "control_flow_short_circuit_return_verified",
        "distinguish_returns_and_implict_units::never_short_circuit_right",
        2,
    ),
    (
        "control_flow_match_arm_return_verified",
        "distinguish_returns_and_implict_units::test_return_from_match",
        2,
    ),
    (
        "control_flow_local_initializer_return_verified",
        "distinguish_returns_and_implict_units::test_add_u32_and_never",
        2,
    ),
    (
        "control_flow_multiple_top_level_returns_first_dominates_verified",
        "misc_never_returns_fail::return_return",
        2,
    ),
];

const COUNTEREXAMPLE_CASES: &[(&str, &str, usize)] = &[
    (
        "control_flow_final_stmt_return_counterexample",
        "final_stmt_return_fail::test_final_stmt_return",
        2,
    ),
    (
        "control_flow_postcondition_fail_if_value_counterexample",
        "postconditions_fail_in_returns_in_conditional::postcondition_fail_if_value",
        2,
    ),
    (
        "control_flow_postcondition_fail_else_value_counterexample",
        "postconditions_fail_in_returns_in_conditional::postcondition_fail_else_value",
        2,
    ),
    (
        "control_flow_tail_if_return_counterexample",
        "return_from_if_else_fail::test_return_from_if",
        2,
    ),
    (
        "control_flow_short_circuit_return_counterexample",
        "short_circuit_returns_fail::never_short_circuit_right",
        2,
    ),
    (
        "control_flow_match_arm_return_counterexample",
        "return_from_match_fail::test_return_from_match",
        2,
    ),
    (
        "control_flow_requires_in_conditional_counterexample",
        "requires_in_conditional_pure::test",
        1,
    ),
];

const ERROR_CASES: &[(&str, &str, &[&str])] = &[
    (
        "control_flow_never_expression_binop_error",
        "distinguish_returns_and_implict_units::never_binop_left",
        &["return", "never", "unsupported nested explicit return path"],
    ),
    (
        "control_flow_nested_return_in_return_value_error",
        "misc_never_returns_fail::never_in_return",
        &["nested explicit return in return value"],
    ),
];

const EXPECTED_CASE_METADATA: &[(&str, &str, &str, usize)] = &[
    (
        "control_flow_final_stmt_return_verified",
        "distinguish_returns_and_implict_units::test_final_stmt_return",
        "verified",
        2,
    ),
    (
        "control_flow_final_stmt_return_counterexample",
        "final_stmt_return_fail::test_final_stmt_return",
        "counterexample",
        2,
    ),
    (
        "control_flow_postcondition_fail_if_value_counterexample",
        "postconditions_fail_in_returns_in_conditional::postcondition_fail_if_value",
        "counterexample",
        2,
    ),
    (
        "control_flow_postcondition_fail_else_value_counterexample",
        "postconditions_fail_in_returns_in_conditional::postcondition_fail_else_value",
        "counterexample",
        2,
    ),
    (
        "control_flow_tail_if_return_verified",
        "distinguish_returns_and_implict_units::test_return_from_if",
        "verified",
        2,
    ),
    (
        "control_flow_tail_if_return_counterexample",
        "return_from_if_else_fail::test_return_from_if",
        "counterexample",
        2,
    ),
    (
        "control_flow_tail_else_return_verified",
        "distinguish_returns_and_implict_units::test_return_from_else",
        "verified",
        2,
    ),
    (
        "control_flow_short_circuit_return_verified",
        "distinguish_returns_and_implict_units::never_short_circuit_right",
        "verified",
        2,
    ),
    (
        "control_flow_short_circuit_return_counterexample",
        "short_circuit_returns_fail::never_short_circuit_right",
        "counterexample",
        2,
    ),
    (
        "control_flow_match_arm_return_verified",
        "distinguish_returns_and_implict_units::test_return_from_match",
        "verified",
        2,
    ),
    (
        "control_flow_match_arm_return_counterexample",
        "return_from_match_fail::test_return_from_match",
        "counterexample",
        2,
    ),
    (
        "control_flow_local_initializer_return_verified",
        "distinguish_returns_and_implict_units::test_add_u32_and_never",
        "verified",
        2,
    ),
    (
        "control_flow_requires_in_conditional_counterexample",
        "requires_in_conditional_pure::test",
        "counterexample",
        1,
    ),
    (
        "control_flow_never_expression_binop_error",
        "distinguish_returns_and_implict_units::never_binop_left",
        "error",
        0,
    ),
    (
        "control_flow_nested_return_in_return_value_error",
        "misc_never_returns_fail::never_in_return",
        "error",
        0,
    ),
    (
        "control_flow_multiple_top_level_returns_first_dominates_verified",
        "misc_never_returns_fail::return_return",
        "verified",
        2,
    ),
];

#[derive(Debug, Eq, PartialEq)]
struct CaseMetadata {
    case_id: String,
    upstream_case_id: String,
    expected_verdict: String,
    min_obligations: usize,
    expected_error_patterns: Vec<String>,
}

fn referenced_array_const(file: &syn::File, const_name: &str) -> syn::ExprArray {
    let const_item = file
        .items
        .iter()
        .find_map(|item| match item {
            syn::Item::Const(item) if item.ident == const_name => Some(item),
            _ => None,
        })
        .unwrap_or_else(|| panic!("control_flow port should define {const_name}"));

    let syn::Expr::Reference(reference) = const_item.expr.as_ref() else {
        panic!("{const_name} should be a referenced array");
    };
    let syn::Expr::Array(array) = reference.expr.as_ref() else {
        panic!("{const_name} should reference an array");
    };
    array.clone()
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
    let array = referenced_array_const(file, "CONTROL_FLOW_RS_FAIL_CLOSED_ERROR_PATTERNS");
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
    let array = referenced_array_const(file, "CONTROL_FLOW_RS_EXPECTED_CASES");
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
            "duplicate control_flow metadata for {case_id}"
        );
        let expected_error_patterns = error_patterns.remove(&case_id).unwrap_or_default();
        entries.push(CaseMetadata {
            case_id,
            upstream_case_id: literal_string(&tuple.elems[1]),
            expected_verdict: literal_string(&tuple.elems[2]),
            min_obligations: literal_usize(&tuple.elems[3]),
            expected_error_patterns,
        });
    }

    assert!(
        error_patterns.is_empty(),
        "error-pattern metadata should not contain orphan cases: {error_patterns:?}"
    );
    entries
}

fn expected_metadata() -> Vec<CaseMetadata> {
    let mut error_patterns = BTreeMap::new();
    for (case, _, expected_fragments) in ERROR_CASES {
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
            "duplicate error-case metadata for {case}"
        );
    }

    EXPECTED_CASE_METADATA
        .iter()
        .map(
            |(case_id, upstream_case_id, expected_verdict, min_obligations)| CaseMetadata {
                case_id: (*case_id).to_string(),
                upstream_case_id: (*upstream_case_id).to_string(),
                expected_verdict: (*expected_verdict).to_string(),
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
            entry["upstream_path"].as_str() == Some("source/rust_verify_test/tests/control_flow.rs")
        })
        .expect("Verus manifest should contain control_flow.rs row");

    row["expected_cases"]
        .as_array()
        .expect("control_flow.rs row should contain expected_cases")
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
            expected_error_patterns: entry["expected_error_patterns"]
                .as_array()
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
fn control_flow_rs_port_file_is_rust_syntax() {
    let source = std::fs::read_to_string(control_flow_port_path())
        .expect("control_flow port should be readable");
    syn::parse_file(&source).expect("control_flow port should parse as ordinary Rust syntax");
}

#[test]
fn control_flow_rs_pinned_upstream_case_shapes_are_present() {
    let path = pinned_upstream_control_flow_path();
    if !path.exists() {
        eprintln!(
            "skipping pinned upstream control_flow.rs shape check; missing {}",
            path.display()
        );
        return;
    }

    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", path.display()));
    for expected in [
        "#[test] distinguish_returns_and_implict_units",
        "#[test] postconditions_fail_in_returns_in_conditional",
        "#[test] return_from_if_else_fail",
        "#[test] return_from_match_fail",
        "#[test] return_in_let_fail",
        "#[test] final_stmt_return_fail",
        "#[test] short_circuit_returns_fail",
        "#[test] misc_never_returns_fail",
        "#[test] requires_in_conditional_pure",
    ] {
        assert!(
            source.contains(expected),
            "pinned upstream control_flow.rs should still contain {expected}"
        );
    }
}

#[test]
fn control_flow_rs_expected_case_metadata_is_exact() {
    let source = std::fs::read_to_string(control_flow_port_path())
        .expect("control_flow port should be readable");
    let file =
        syn::parse_file(&source).expect("control_flow port should parse as ordinary Rust syntax");
    assert_eq!(metadata_entries(&file), expected_metadata());
    assert!(
        source.contains("control_flow_rs_expected_cases")
            && source.contains("control_flow_rs_fail_closed_error_patterns"),
        "control_flow port should export expected-case and error-pattern metadata"
    );
}

#[test]
fn control_flow_rs_expected_case_metadata_matches_manifest() {
    let source = std::fs::read_to_string(control_flow_port_path())
        .expect("control_flow port should be readable");
    let file =
        syn::parse_file(&source).expect("control_flow port should parse as ordinary Rust syntax");
    assert_eq!(metadata_entries(&file), manifest_expected_metadata());
}

#[test]
fn control_flow_rs_verified_subset_verifies_from_file() {
    let path = control_flow_port_path();
    let path = path
        .to_str()
        .expect("control_flow port path should be UTF-8");

    for (case, upstream_case, _) in VERIFIED_CASES {
        let result = verify_case(path, case, upstream_case);
        assert!(
            matches!(result, VerifyResult::Verified),
            "{case} ({upstream_case}) should verify, got: {result:?}"
        );
    }
}

#[test]
fn control_flow_rs_counterexample_subset_is_rejected_from_file() {
    let path = control_flow_port_path();
    let path = path
        .to_str()
        .expect("control_flow port path should be UTF-8");

    for (case, upstream_case, _) in COUNTEREXAMPLE_CASES {
        let result = verify_case(path, case, upstream_case);
        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "{case} ({upstream_case}) should be rejected, got: {result:?}"
        );
    }
}

#[test]
fn control_flow_rs_error_cases_fail_closed_from_file() {
    let path = control_flow_port_path();
    let path = path
        .to_str()
        .expect("control_flow port path should be UTF-8");

    for (case, upstream_case, expected_fragments) in ERROR_CASES {
        let message = fail_closed_message(path, case, upstream_case);
        assert_contains_any(
            &message,
            expected_fragments,
            &format!("{case} ({upstream_case})"),
        );
    }
}

#[test]
fn control_flow_rs_expected_obligations_are_collected_from_file() {
    let path = control_flow_port_path();
    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|err| panic!("control_flow port should read: {err}"));
    let file = syn::parse_file(&source)
        .unwrap_or_else(|err| panic!("control_flow port should parse: {err}"));

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
                panic!("{case} ({upstream_case}) should exist in control_flow port")
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
