// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Executable guards for the upstream loops.rs TrustVc scout.
//!
//! These tests intentionally keep upstream loops.rs as an unsupported gap. They
//! pin only stable Rust-valid TrustVc behavior around loop invariants,
//! normal-exit facts, unmodified/shadowed variable facts, break/continue loop
//! clauses, current-gap nested-break counterexamples, upstream shape pins, and
//! fail-closed boundaries for loop_decreases! and old-state loop invariants.

mod common;

use std::{
    collections::{BTreeMap, BTreeSet},
    path::{Path, PathBuf},
};
use trust_vc_core::{
    extract_verification_conditions_with_file_context, verify_function_from_file, VerifyResult,
};

fn loops_port_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/ported/loops.rs")
}

fn pinned_upstream_loops_path() -> PathBuf {
    common::pinned_verus_test_path("loops.rs")
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

const VERIFIED_CASES: &[(&str, &str, usize)] = &[
    (
        "basic_while_invariant_establishes_assertion",
        "basic_while",
        3,
    ),
    (
        "while_unmodified_variable_not_havoced_verified",
        "test_variables_not_havoc_basic",
        1,
    ),
    (
        "while_shadowed_variable_no_effect_verified",
        "test_variables_no_effect_basic",
        1,
    ),
    (
        "nested_while_outer_variable_not_havoced_verified",
        "test_variables_not_havoc_nested",
        1,
    ),
    ("while_bool_guard_normal_exit", "while_b", 3),
    (
        "loop_continue_loop_ensures_post_loop_use",
        "example_loop_continue",
        4,
    ),
    ("loop_break_invariant_except_break", "example_loop_break", 4),
    (
        "loop_break_regular_invariant_preserves_unmodified_fact",
        "basic_loop",
        3,
    ),
    (
        "loop_labeled_inner_break_regular_invariant_preserves_unmodified_fact",
        "loop2_ok_y unmodified-state subset",
        3,
    ),
    (
        "while_nested_inner_break_current_gap_counterexample",
        "while_b2 current TrustVc gap",
        2,
    ),
    (
        "while_labeled_inner_break_current_gap_counterexample",
        "while_b2_y current TrustVc gap",
        2,
    ),
    (
        "while_loop_decreases_verified",
        "loop_termination_supported / loop_decreases1 boundary",
        9,
    ),
];

const COUNTEREXAMPLE_CASES: &[(&str, &str, usize)] = &[
    (
        "basic_while_missing_upper_invariant_counterexample",
        "basic_while_fail1",
        1,
    ),
    (
        "while_break_does_not_assume_normal_exit_counterexample",
        "while_to_loop_break",
        1,
    ),
    (
        "while_labeled_break_to_outer_counterexample",
        "while_b2_x",
        1,
    ),
    ("loop_break_false_counterexample", "loop_break_false", 1),
    (
        "loop_labeled_break_false_counterexample",
        "loop_break_false_y",
        1,
    ),
    (
        "loop_nested_break_to_outer_false_counterexample",
        "loop_infinite2x",
        1,
    ),
    (
        "loop_break_regular_unmodified_invariant_current_gap_counterexample",
        "basic_loop non-tautological invariant current TrustVc gap",
        3,
    ),
    (
        "loop_labeled_inner_break_regular_invariant_current_gap_counterexample",
        "loop2_ok_y non-tautological invariant current TrustVc gap",
        3,
    ),
];

const FAIL_CLOSED_CASES: &[(&str, &str, &[&str])] = &[(
    "loop_old_state_invariant_boundary_currently_errors",
    "loop_references_old_version_of_mut_var old-state boundary",
    &[
        "Unsupported old-state expression `old(...)`",
        "old-state",
        "old",
    ],
)];

const EXPECTED_CASE_METADATA: &[(&str, &str, &str, usize)] = &[
    (
        "basic_while_invariant_establishes_assertion",
        "basic_while",
        "verified",
        3,
    ),
    (
        "while_unmodified_variable_not_havoced_verified",
        "test_variables_not_havoc_basic",
        "verified",
        1,
    ),
    (
        "while_shadowed_variable_no_effect_verified",
        "test_variables_no_effect_basic",
        "verified",
        1,
    ),
    (
        "nested_while_outer_variable_not_havoced_verified",
        "test_variables_not_havoc_nested",
        "verified",
        1,
    ),
    ("while_bool_guard_normal_exit", "while_b", "verified", 3),
    (
        "loop_continue_loop_ensures_post_loop_use",
        "example_loop_continue",
        "verified",
        4,
    ),
    (
        "loop_break_invariant_except_break",
        "example_loop_break",
        "verified",
        4,
    ),
    (
        "loop_break_regular_invariant_preserves_unmodified_fact",
        "basic_loop",
        "verified",
        3,
    ),
    (
        "loop_labeled_inner_break_regular_invariant_preserves_unmodified_fact",
        "loop2_ok_y unmodified-state subset",
        "verified",
        3,
    ),
    (
        "basic_while_missing_upper_invariant_counterexample",
        "basic_while_fail1",
        "counterexample",
        1,
    ),
    (
        "while_nested_inner_break_current_gap_counterexample",
        "while_b2 current TrustVc gap",
        "verified",
        2,
    ),
    (
        "while_labeled_inner_break_current_gap_counterexample",
        "while_b2_y current TrustVc gap",
        "verified",
        2,
    ),
    (
        "while_break_does_not_assume_normal_exit_counterexample",
        "while_to_loop_break",
        "counterexample",
        1,
    ),
    (
        "while_labeled_break_to_outer_counterexample",
        "while_b2_x",
        "counterexample",
        1,
    ),
    (
        "loop_break_false_counterexample",
        "loop_break_false",
        "counterexample",
        1,
    ),
    (
        "loop_labeled_break_false_counterexample",
        "loop_break_false_y",
        "counterexample",
        1,
    ),
    (
        "loop_nested_break_to_outer_false_counterexample",
        "loop_infinite2x",
        "counterexample",
        1,
    ),
    (
        "loop_break_regular_unmodified_invariant_current_gap_counterexample",
        "basic_loop non-tautological invariant current TrustVc gap",
        "counterexample",
        3,
    ),
    (
        "loop_labeled_inner_break_regular_invariant_current_gap_counterexample",
        "loop2_ok_y non-tautological invariant current TrustVc gap",
        "counterexample",
        3,
    ),
    (
        "while_loop_decreases_verified",
        "loop_termination_supported / loop_decreases1 boundary",
        "verified",
        9,
    ),
    (
        "loop_old_state_invariant_boundary_currently_errors",
        "loop_references_old_version_of_mut_var old-state boundary",
        "error",
        0,
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
        .unwrap_or_else(|| panic!("loops port should define {const_name}"));

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
    let array = referenced_array_const(file, "LOOPS_RS_EXPECTED_ERROR_PATTERNS");
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
    let array = referenced_array_const(file, "LOOPS_RS_EXPECTED_CASES");
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
            "duplicate loops metadata for {case_id}"
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

fn expected_error_pattern_entries() -> BTreeMap<String, Vec<String>> {
    FAIL_CLOSED_CASES
        .iter()
        .map(|&(case, _, patterns)| {
            (
                case.to_string(),
                patterns
                    .iter()
                    .map(|pattern| (*pattern).to_string())
                    .collect(),
            )
        })
        .collect()
}

fn expected_metadata_from_tests() -> Vec<CaseMetadata> {
    let mut patterns_by_case = expected_error_pattern_entries();

    EXPECTED_CASE_METADATA
        .iter()
        .map(
            |(case_id, upstream_case_id, expected_verdict, min_obligations)| CaseMetadata {
                case_id: (*case_id).to_string(),
                upstream_case_id: (*upstream_case_id).to_string(),
                expected_verdict: (*expected_verdict).to_string(),
                min_obligations: *min_obligations,
                expected_error_patterns: patterns_by_case.remove(*case_id).unwrap_or_default(),
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
            entry["upstream_path"].as_str() == Some("source/rust_verify_test/tests/loops.rs")
        })
        .expect("Verus manifest should contain loops.rs row");

    row["expected_cases"]
        .as_array()
        .expect("loops.rs row should contain expected_cases")
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
fn loops_rs_port_file_is_rust_syntax() {
    let source = std::fs::read_to_string(loops_port_path()).expect("loops port should be readable");
    syn::parse_file(&source).expect("loops port should parse as ordinary Rust syntax");
}

#[test]
fn loops_rs_pinned_upstream_case_shapes_are_present() {
    let path = pinned_upstream_loops_path();
    if !path.exists() {
        eprintln!(
            "skipping pinned upstream loops.rs shape check; missing {}",
            path.display()
        );
        return;
    }

    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", path.display()));
    for expected in [
        "#[test] basic_while",
        "#[test] basic_while_fail1",
        "#[test] basic_while_fail2",
        "#[test] complex_while",
        "#[test] test_variables_havoc_basic",
        "#[test] test_variables_not_havoc_basic",
        "#[test] test_variables_no_effect_basic",
        "#[test] test_variables_not_havoc_nested",
        "#[test] basic_loop",
        "#[test] loop_termination_supported",
        "#[test] example_loop_break",
        "#[test] example_loop_continue",
        "#[test] loop_break_false_y",
        "#[test] while_b_ok",
        "#[test] while_b2",
        "#[test] while_b2_x",
        "#[test] while_b2_y",
        "#[test] while_to_loop_ensures",
        "#[test] loop_infinite2x",
        "#[test] loop2_ok_y",
        "#[test] loop_decreases1",
        "#[test] loop_references_old_version_of_mut_var",
        "#[test] iter_loop",
        "#[test] for_loop1",
        "#[test] loop_invariant_except_break_nonlinear",
        "#[test] loop_continue_no_break",
        "#[test] recursive_call_in_loop2",
        "#[test] loop_via_subrange",
        "#[test] loop_isolation_false_requires_allow_complex_invariants",
        "for x in iter: 0..10",
        "src@.subrange(lo as int, hi as int)",
        "loop invariants with 'loop_isolation(false)'",
    ] {
        assert!(
            source.contains(expected),
            "pinned upstream loops.rs should still contain {expected}"
        );
    }
}

#[test]
fn loops_rs_expected_case_metadata_is_exact() {
    let source = std::fs::read_to_string(loops_port_path()).expect("loops port should be readable");
    let file = syn::parse_file(&source).expect("loops port should parse as ordinary Rust syntax");

    assert_eq!(
        metadata_entries(&file),
        expected_metadata_from_tests(),
        "loops port expected-case metadata should match the regression inventory"
    );
    assert_eq!(
        error_pattern_entries(&file),
        expected_error_pattern_entries(),
        "loops port error-pattern metadata should match fail-closed cases"
    );
    assert!(
        source.contains("loops_rs_expected_cases")
            && source.contains("loops_rs_expected_error_patterns"),
        "loops port should expose expected-case and error-pattern metadata accessors"
    );
}

#[test]
fn loops_rs_expected_case_metadata_matches_manifest() {
    let source = std::fs::read_to_string(loops_port_path()).expect("loops port should be readable");
    let file = syn::parse_file(&source).expect("loops port should parse as ordinary Rust syntax");

    assert_eq!(
        metadata_entries(&file),
        manifest_expected_metadata(),
        "loops manifest expected_cases should match port metadata exactly"
    );
}

#[test]
fn loops_rs_error_cases_have_expected_error_patterns() {
    let source = std::fs::read_to_string(loops_port_path()).expect("loops port should be readable");
    let file = syn::parse_file(&source).expect("loops port should parse as ordinary Rust syntax");
    let mut patterns_by_case = error_pattern_entries(&file);

    for expected_case in metadata_entries(&file) {
        if expected_case.expected_verdict == "error" {
            assert_eq!(
                expected_case.min_obligations, 0,
                "{} ({}) error evidence should not declare obligations",
                expected_case.case_id, expected_case.upstream_case_id
            );
            let expected_patterns = patterns_by_case
                .remove(&expected_case.case_id)
                .unwrap_or_else(|| {
                    panic!(
                        "{} ({}) should have expected_error_patterns metadata",
                        expected_case.case_id, expected_case.upstream_case_id
                    )
                });
            assert!(
                !expected_patterns.is_empty(),
                "{} ({}) expected_error_patterns should not be empty",
                expected_case.case_id,
                expected_case.upstream_case_id
            );
        } else {
            assert!(
                !patterns_by_case.contains_key(&expected_case.case_id),
                "{} ({}) non-error metadata should not declare expected_error_patterns",
                expected_case.case_id,
                expected_case.upstream_case_id
            );
        }
    }

    assert!(
        patterns_by_case.is_empty(),
        "expected_error_patterns should not contain orphan cases: {patterns_by_case:?}"
    );
}

#[test]
fn loops_rs_non_error_subset_collects_min_obligations() {
    let path = loops_port_path();
    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|err| panic!("loops port should read: {err}"));
    let file =
        syn::parse_file(&source).unwrap_or_else(|err| panic!("loops port should parse: {err}"));

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
            .unwrap_or_else(|| panic!("{case} ({upstream_case}) should exist in loops port"));
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
fn loops_rs_verified_subset_verifies_from_file() {
    let path = loops_port_path();
    let path = path.to_str().expect("loops port path should be UTF-8");

    for (case, upstream_case, _) in VERIFIED_CASES {
        let result = verify_case(path, case, upstream_case);
        assert!(
            matches!(result, VerifyResult::Verified),
            "{case} ({upstream_case}) should verify, got: {result:?}"
        );
    }
}

#[test]
fn loops_rs_counterexample_subset_is_rejected_from_file() {
    let path = loops_port_path();
    let path = path.to_str().expect("loops port path should be UTF-8");

    for (case, upstream_case, _) in COUNTEREXAMPLE_CASES {
        let result = verify_case(path, case, upstream_case);
        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "{case} ({upstream_case}) should produce a counterexample, got: {result:?}"
        );
    }
}

#[test]
fn loops_rs_unsupported_boundaries_fail_closed_from_file() {
    let path = loops_port_path();
    let path = path.to_str().expect("loops port path should be UTF-8");

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
