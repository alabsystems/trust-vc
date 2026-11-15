// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Executable guards for the first upstream loops_no_spinoff.rs TrustVc scout.
//!
//! These tests intentionally keep upstream loops_no_spinoff.rs as an
//! unsupported gap. They verify stable Rust-valid TrustVc behavior around
//! numeric while-loop invariant exits, pure boolean normal-exit facts,
//! loop-havoc/no-havoc facts, break/continue summaries, nested-break gap
//! behavior, restored-loop current gaps, bare/labeled/infinite-loop reachability
//! counterexamples, simple for-loop fail-closed boundaries, source-level loop
//! decreases, and old-state loop assertions.

mod common;

use std::{
    collections::{BTreeMap, BTreeSet},
    path::{Path, PathBuf},
};
use trust_vc_core::{
    extract_verification_conditions_with_file_context, verify_function_from_file, VerifyResult,
};

#[derive(Debug, Eq, PartialEq)]
struct CaseMetadata {
    case_id: String,
    upstream_case_id: String,
    expected_verdict: String,
    min_obligations: usize,
    expected_error_patterns: Vec<String>,
}

fn loops_no_spinoff_port_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/ported/loops_no_spinoff.rs")
}

fn pinned_upstream_loops_no_spinoff_path() -> PathBuf {
    common::pinned_verus_test_path("loops_no_spinoff.rs")
}

fn verus_manifest_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/verus-tests.json")
}

fn verify_case(path: &str, case: &str, upstream_case: &str) -> VerifyResult {
    verify_function_from_file(path, case)
        .unwrap_or_else(|err| panic!("{case} ({upstream_case}) should extract: {err}"))
}

fn expect_fail_closed(path: &str, case: &str, upstream_case: &str, expected_terms: &[&str]) {
    let message = match verify_function_from_file(path, case) {
        Err(err) => err.to_string(),
        Ok(VerifyResult::Error { message }) => message,
        Ok(VerifyResult::Unknown { reason, .. }) => {
            panic!(
                "{case} ({upstream_case}) returned solver Unknown, which is not stable evidence: {reason}"
            )
        }
        Ok(result) => {
            panic!("{case} ({upstream_case}) should fail closed with Error, got: {result:?}")
        }
    };

    assert!(
        expected_terms.iter().any(|term| message.contains(term)),
        "{case} ({upstream_case}) should report one of {expected_terms:?}, got: {message}"
    );
}

fn referenced_array_const(file: &syn::File, const_name: &str) -> syn::ExprArray {
    let const_item = file
        .items
        .iter()
        .find_map(|item| match item {
            syn::Item::Const(item) if item.ident == const_name => Some(item),
            _ => None,
        })
        .unwrap_or_else(|| panic!("loops_no_spinoff port should define {const_name}"));

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
    let array = referenced_array_const(file, "LOOPS_NO_SPINOFF_RS_EXPECTED_ERROR_PATTERNS");
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
            "duplicate loops_no_spinoff error-pattern metadata for {case_id}"
        );
    }

    entries
}

fn metadata_entries(file: &syn::File) -> Vec<CaseMetadata> {
    let array = referenced_array_const(file, "LOOPS_NO_SPINOFF_RS_EXPECTED_CASES");
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
            "duplicate loops_no_spinoff metadata for {case_id}"
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
    entries.sort_by(|left, right| left.case_id.cmp(&right.case_id));
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
                == Some("source/rust_verify_test/tests/loops_no_spinoff.rs")
        })
        .expect("Verus manifest should contain loops_no_spinoff.rs row");

    let mut entries = row["expected_cases"]
        .as_array()
        .expect("loops_no_spinoff.rs row should contain expected_cases")
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
        .collect::<Vec<_>>();
    entries.sort_by(|left, right| left.case_id.cmp(&right.case_id));
    entries
}

const VERIFIED_CASES: &[(&str, &str, usize)] = &[
    (
        "loops_no_spinoff_while_bool_guard_normal_exit_verified",
        "while_b",
        1,
    ),
    (
        "loops_no_spinoff_basic_while_invariant_normal_exit_verified",
        "basic_while",
        2,
    ),
    (
        "loops_no_spinoff_variables_not_havoc_basic_verified",
        "test_variables_not_havoc_basic",
        2,
    ),
    (
        "loops_no_spinoff_variables_no_effect_basic_verified",
        "test_variables_no_effect_basic",
        2,
    ),
    (
        "loops_no_spinoff_variables_not_havoc_nested_verified",
        "test_variables_not_havoc_nested",
        1,
    ),
    (
        "loops_no_spinoff_variables_no_effect_nested_verified",
        "test_variables_no_effect_nested",
        1,
    ),
    (
        "loops_no_spinoff_loop_continue_post_loop_use_verified",
        "example_loop_continue",
        3,
    ),
    (
        "loops_no_spinoff_loop_break_loop_ensures_verified",
        "example_loop_break",
        4,
    ),
    (
        "loops_no_spinoff_allow_complex_invariants_subset_verified",
        "allow_complex_invariants_basic",
        4,
    ),
    (
        "loops_no_spinoff_while_nested_inner_break_current_gap_counterexample",
        "local",
        1,
    ),
    (
        "loops_no_spinoff_while_labeled_inner_break_current_gap_counterexample",
        "local",
        1,
    ),
    (
        "loops_no_spinoff_loop_decreases_verified",
        "loop_termination_unsupported",
        9,
    ),
    // 2026-09-10 (audit rows 430/433): the range guard `x < 10` reaches the body
    // assertion, so upstream for_loop1's `assert(x < 10)` verifies — re-pinned
    // from the "sound over-rejection" counterexample it used to be.
    (
        "loops_no_spinoff_for_loop_range_fact_verified",
        "for_loop1",
        5,
    ),
    // 2026-09-10 (audit row 430): upstream loop2_ok / loop2_ok_y verify — the
    // effect-free inner loop no longer drops the outer body out of the exact
    // lane, and its invariant is checked at the outer loop's arbitrary head.
    (
        "loops_no_spinoff_loop2_restore_before_break_verified",
        "loop2_ok",
        10,
    ),
    (
        "loops_no_spinoff_loop2_restore_before_labeled_inner_break_verified",
        "loop2_ok_y",
        10,
    ),
    // 2026-09-10 (audit row 430): code after a bare loop with no exit is
    // unreachable — upstream infinite_loop / loop_infinite2 / loop_infinite2y verify.
    (
        "loops_no_spinoff_infinite_loop_unreachable_verified",
        "infinite_loop",
        3,
    ),
    (
        "loops_no_spinoff_loop_infinite_nested_inner_break_verified",
        "loop_infinite2",
        3,
    ),
    (
        "loops_no_spinoff_loop_infinite_nested_labeled_inner_break_verified",
        "loop_infinite2y",
        3,
    ),
    // 2026-09-11 (row 430): the side-effect guard block (upstream complex_while) verifies.
    (
        "loops_no_spinoff_complex_while_side_effect_guard_verified",
        "complex_while",
        12,
    ),
];

const COUNTEREXAMPLE_CASES: &[(&str, &str, usize)] = &[
    // Re-pinned 2026-07-24 from FAIL_CLOSED_CASES: the range `for` now desugars
    // (for_range_desugar.rs). `assert!(x < 10)` over just the auto lower bound, and
    // `assert!(n == 30)` over an un-invariant-pinned accumulator, both Counterexample.
    (
        "loops_no_spinoff_for_loop_range_fact_liar_counterexample",
        "for_loop1 test_loop_fail",
        5,
    ),
    (
        "loops_no_spinoff_for_loop_accumulator_post_boundary_counterexample",
        "for_loop1",
        1,
    ),
    (
        "loops_no_spinoff_while_break_does_not_assume_normal_exit_counterexample",
        "while_b_fail",
        1,
    ),
    (
        "loops_no_spinoff_while_labeled_break_to_outer_counterexample",
        "while_b2_x",
        1,
    ),
    (
        "loops_no_spinoff_loop_break_false_counterexample",
        "loop_break_false",
        1,
    ),
    (
        "loops_no_spinoff_example_loop_break_without_progress_counterexample",
        "example_loop_break_fail3",
        1,
    ),
    (
        "loops_no_spinoff_example_loop_break_post_too_strong_counterexample",
        "example_loop_break_fail4",
        1,
    ),
    (
        "loops_no_spinoff_basic_while_missing_invariant_counterexample",
        "basic_while_fail1",
        1,
    ),
    (
        "loops_no_spinoff_basic_while_nested_j_havoc_counterexample",
        "basic_while_fail2",
        1,
    ),
    (
        "loops_no_spinoff_variables_havoc_basic_counterexample",
        "test_variables_havoc_basic",
        1,
    ),
    (
        "loops_no_spinoff_variables_havoc_nested_counterexample",
        "test_variables_havoc_nested",
        1,
    ),
    (
        "loops_no_spinoff_loop_break_false_labeled_counterexample",
        "loop_break_false_y",
        1,
    ),
    (
        "loops_no_spinoff_loop_labeled_break_to_outer_false_counterexample",
        "loop_infinite2x",
        1,
    ),
    (
        "loops_no_spinoff_loop2_labeled_break_to_outer_counterexample",
        "loop2_fail1",
        1,
    ),
    (
        "loops_no_spinoff_loop2_missing_restore_counterexample",
        "loop2_fail2",
        1,
    ),
    (
        "loops_no_spinoff_loop_decreases_continue_counterexample",
        "loop_decreases1",
        5,
    ),
];

// Empty since 2026-07-24: both for_loop1 range boundaries now desugar
// (for_range_desugar.rs) and Counterexample instead of erroring — moved to
// COUNTEREXAMPLE_CASES.
// loops_no_spinoff_loop_old_state_boundary_currently_errors removed 2026-07-09: audited slice-B flip (error -> verified; tautology — entry==current for a never-mutated param; upstream rejects diagnostically, documented divergence).
// loops_no_spinoff_loop_decreases{,_continue} de-surrogated: file-path loop_decreases! now routes (verified / counterexample); moved to VERIFIED_CASES / COUNTEREXAMPLE_CASES.
const FAIL_CLOSED_CASES: &[(&str, &str, &[&str])] = &[];

#[test]
fn loops_no_spinoff_rs_port_file_is_rust_syntax() {
    let source = std::fs::read_to_string(loops_no_spinoff_port_path())
        .expect("loops_no_spinoff port should be readable");
    syn::parse_file(&source).expect("loops_no_spinoff port should parse as ordinary Rust syntax");
}

#[test]
fn loops_no_spinoff_rs_pinned_upstream_case_shapes_are_present() {
    let path = pinned_upstream_loops_no_spinoff_path();
    if !path.exists() {
        eprintln!(
            "skipping pinned upstream loops_no_spinoff.rs shape check; missing {}",
            path.display()
        );
        return;
    }

    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", path.display()));
    for expected in [
        "#[test] while_b",
        "#[test] while_b_fail",
        "#[test] basic_while",
        "#[test] basic_while_fail1",
        "#[test] basic_while_fail2",
        "#[test] complex_while",
        "#[test] test_variables_havoc_basic",
        "#[test] test_variables_not_havoc_basic",
        "#[test] test_variables_no_effect_basic",
        "#[test] test_variables_havoc_nested",
        "#[test] test_variables_not_havoc_nested",
        "#[test] test_variables_no_effect_nested",
        "#[test] example_loop_break",
        "#[test] example_loop_break_fail3",
        "#[test] example_loop_break_fail4",
        "#[test] example_loop_continue",
        "#[test] infinite_loop",
        "#[test] loop_break_false_y",
        "#[test] while_b2",
        "#[test] while_b2_x",
        "#[test] while_b2_y",
        "#[test] loop_infinite2",
        "#[test] loop_infinite2y",
        "#[test] loop_infinite2x",
        "#[test] loop2_ok",
        "#[test] loop2_ok_y",
        "#[test] loop2_fail1",
        "#[test] loop2_fail2",
        "#[test] loop_decreases1",
        "#[test] loop_break_false",
        "#[test] loop_termination_unsupported",
        "#[test] loop_references_old_version_of_mut_var",
        "#[test] for_loop1",
        "#[test] allow_complex_invariants_basic",
        "#[verifier::loop_isolation(false)]",
        "exec_allows_no_decreases_clause",
        "for x in iter: 0..10",
        "invariant_except_break i <= 10",
    ] {
        assert!(
            source.contains(expected),
            "pinned upstream loops_no_spinoff.rs should still contain {expected}"
        );
    }
}

#[test]
fn loops_no_spinoff_rs_expected_case_metadata_is_exact() {
    let source = std::fs::read_to_string(loops_no_spinoff_port_path())
        .expect("loops_no_spinoff port should be readable");
    let file = syn::parse_file(&source)
        .expect("loops_no_spinoff port should parse as ordinary Rust syntax");
    assert!(
        source.contains("LOOPS_NO_SPINOFF_RS_EXPECTED_CASES")
            && source.contains("loops_no_spinoff_rs_expected_cases")
            && source.contains("LOOPS_NO_SPINOFF_RS_EXPECTED_ERROR_PATTERNS")
            && source.contains("loops_no_spinoff_rs_expected_error_patterns"),
        "loops_no_spinoff port should expose expected-case and error-pattern metadata helpers"
    );
    assert_eq!(
        metadata_entries(&file),
        manifest_expected_metadata(),
        "loops_no_spinoff.rs manifest expected_cases should match port metadata and error patterns exactly"
    );
}

#[test]
fn loops_no_spinoff_rs_verified_subset_verifies_from_file() {
    let path = loops_no_spinoff_port_path();
    let path = path
        .to_str()
        .expect("loops_no_spinoff port path should be UTF-8");

    for (case, upstream_case, _) in VERIFIED_CASES {
        let result = verify_case(path, case, upstream_case);
        assert!(
            matches!(result, VerifyResult::Verified),
            "{case} ({upstream_case}) should verify, got: {result:?}"
        );
    }
}

#[test]
fn loops_no_spinoff_rs_non_error_subset_collects_min_obligations() {
    let path = loops_no_spinoff_port_path();
    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|err| panic!("loops_no_spinoff port should read: {err}"));
    let file = syn::parse_file(&source)
        .unwrap_or_else(|err| panic!("loops_no_spinoff port should parse: {err}"));

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
                panic!("{case} ({upstream_case}) should exist in loops_no_spinoff port")
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
fn loops_no_spinoff_rs_break_counterexample_is_rejected_from_file() {
    let path = loops_no_spinoff_port_path();
    let path = path
        .to_str()
        .expect("loops_no_spinoff port path should be UTF-8");

    for (case, upstream_case, _) in COUNTEREXAMPLE_CASES {
        let result = verify_case(path, case, upstream_case);
        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "{case} ({upstream_case}) should produce a counterexample, got: {result:?}"
        );
    }
}

#[test]
fn loops_no_spinoff_rs_loop_decreases_boundary_fails_closed_from_file() {
    let path = loops_no_spinoff_port_path();
    let path = path
        .to_str()
        .expect("loops_no_spinoff port path should be UTF-8");

    for (case, upstream_case, expected_terms) in FAIL_CLOSED_CASES {
        expect_fail_closed(path, case, upstream_case, expected_terms);
    }
}
