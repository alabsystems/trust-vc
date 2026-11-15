// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Executable guards for the first upstream exec_termination.rs TrustVc scout slice.
//!
//! These tests intentionally do not claim full Verus exec_termination.rs parity.
//! They pin bounded recursive-decreases compute witnesses, wrong-value
//! counterexamples, Rust-valid loop-safety surrogates, upstream shape pins, and
//! fail-closed boundaries for source-level loop decreases and mutual recursion
//! while the manifest entry remains conceptually `unsupported-gap`.

mod common;

use std::{
    collections::{BTreeMap, BTreeSet},
    path::{Path, PathBuf},
};
use trust_vc_core::{verify_function_from_file, VerifyResult};

fn exec_termination_port_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/ported/exec_termination.rs")
}

fn verus_manifest_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/verus-tests.json")
}

fn pinned_upstream_exec_termination_path() -> PathBuf {
    common::pinned_verus_test_path("exec_termination.rs")
}

fn verify_case(path: &str, case: &str, upstream_case: &str) -> VerifyResult {
    verify_function_from_file(path, case)
        .unwrap_or_else(|err| panic!("{case} ({upstream_case}) should extract: {err}"))
}

fn expect_fail_closed(path: &str, case: &str, upstream_case: &str, expected_terms: &[&str]) {
    let message = match verify_function_from_file(path, case) {
        Err(err) => err.to_string(),
        Ok(VerifyResult::Error { message }) => message,
        Ok(result) => {
            panic!("{case} ({upstream_case}) should fail closed with Error, got: {result:?}")
        }
    };

    assert!(
        expected_terms.iter().any(|term| message.contains(term)),
        "{case} ({upstream_case}) should report one of {expected_terms:?}, got: {message}"
    );
}

const VERIFIED_CASES: &[(&str, &str)] = &[
    (
        "recursive_exec_function_with_decreases_clause_small_compute_verified",
        "recursive_exec_function_with_decreases_clause",
    ),
    // Flipped from FAIL_CLOSED_CASES 2026-07-04: mutually recursive spec-fn
    // dependencies are supported since the B5 mutual-recursion axioms (ad62cc3,
    // guarded by 841f753). Baseline Verified is the TRUE claim
    // mutual_even(4) by compute; false-mutation control (even -> odd(4), FALSE)
    // returned Counterexample 'by(compute): expression evaluates to false'
    // (control ledger 2026-07-04). Not manifest-embedded.
    (
        "mutually_recursive_exec_functions_with_decreases_currently_fail_closed",
        "mutually_recursive_exec_functions_need_decreases_clause",
    ),
    (
        "recursive_exec_function_with_two_decreasing_calls_small_compute_verified",
        "local bounded multi-call recursive-decreases witness",
    ),
    (
        "recursive_exec_function_with_lexicographic_decreases_small_compute_verified",
        "mutually_recursive_exec_functions_need_decreases_clause / dec2 lexicographic shape",
    ),
    (
        "while_loop_missing_decreases_safety_shape_verified",
        "while_loop_needs_decreases_clause safety-only surrogate",
    ),
    (
        "loop_with_break_loop_clause_safety_shape_verified",
        "loop_with_break_with_decreases_clause safety-only surrogate",
    ),
    // 2026-09-10 (audit rows 430/431): the break-only `if` no longer leaves the
    // exact lane, so the faithful shape verifies (upstream: Ok) — moved here from
    // the counterexample subset, where it had pinned the old under-verification.
    (
        "loop_with_break_with_decreases_clause_verified",
        "loop_with_break_with_decreases_clause",
    ),
];

const COUNTEREXAMPLE_CASES: &[(&str, &str)] = &[
    (
        "recursive_exec_function_with_decreases_clause_wrong_value_counterexample",
        "recursive_exec_function_with_decreases_clause",
    ),
    (
        "recursive_exec_function_with_two_decreasing_calls_wrong_value_counterexample",
        "local bounded multi-call recursive-decreases witness",
    ),
    (
        "recursive_exec_function_with_lexicographic_decreases_wrong_value_counterexample",
        "mutually_recursive_exec_functions_need_decreases_clause / dec2 lexicographic shape",
    ),
    (
        "while_loop_missing_decreases_wrong_exit_fact_counterexample",
        "while_loop_needs_decreases_clause safety-only surrogate",
    ),
    // Re-pinned 2026-07-24: the range `for` now desugars to a counter-driven
    // `while` (for_range_desugar.rs), so this loop is REASONED about rather than
    // fail-closed. The invariant `i <= 30` is not established on the unconstrained
    // `u64` parameter `i` → Counterexample (i = u64::MAX). Boundary moved from
    // Error to Counterexample; both "not verified", no false-verify.
    (
        "for_loop_with_decreases_clause_boundary_counterexample",
        "for_loop_with_decreases_clause",
    ),
];

// Empty since 2026-07-24: the only fail-closed for-loop boundary case now
// desugars and Counterexamples (moved to COUNTEREXAMPLE_CASES). Kept as an
// anchor for any future genuinely-fail-closed termination boundary.
const FAIL_CLOSED_CASES: &[(&str, &str, &[&str])] = &[];

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
        .unwrap_or_else(|| panic!("exec_termination port should define {const_name}"));

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
    let array = referenced_array_const(file, "EXEC_TERMINATION_RS_EXPECTED_ERROR_PATTERNS");
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
    let array = referenced_array_const(file, "EXEC_TERMINATION_RS_EXPECTED_CASES");
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
            "duplicate exec_termination metadata for {case_id}"
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
    vec![
        CaseMetadata {
            case_id: "recursive_exec_function_with_decreases_clause_small_compute_verified"
                .to_string(),
            upstream_case_id: "recursive_exec_function_with_decreases_clause".to_string(),
            expected_verdict: "verified".to_string(),
            min_obligations: 1,
            expected_error_patterns: Vec::new(),
        },
        CaseMetadata {
            case_id: "recursive_exec_function_with_decreases_clause_wrong_value_counterexample"
                .to_string(),
            upstream_case_id: "recursive_exec_function_with_decreases_clause".to_string(),
            expected_verdict: "counterexample".to_string(),
            min_obligations: 1,
            expected_error_patterns: Vec::new(),
        },
        CaseMetadata {
            case_id: "recursive_exec_function_with_two_decreasing_calls_small_compute_verified"
                .to_string(),
            upstream_case_id: String::new(),
            expected_verdict: "verified".to_string(),
            min_obligations: 1,
            expected_error_patterns: Vec::new(),
        },
        CaseMetadata {
            case_id: "recursive_exec_function_with_two_decreasing_calls_wrong_value_counterexample"
                .to_string(),
            upstream_case_id: String::new(),
            expected_verdict: "counterexample".to_string(),
            min_obligations: 1,
            expected_error_patterns: Vec::new(),
        },
        CaseMetadata {
            case_id: "loop_with_break_with_decreases_clause_verified".to_string(),
            upstream_case_id: "loop_with_break_with_decreases_clause".to_string(),
            expected_verdict: "verified".to_string(),
            min_obligations: 8,
            expected_error_patterns: Vec::new(),
        },
    ]
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
                == Some("source/rust_verify_test/tests/exec_termination.rs")
        })
        .expect("Verus manifest should contain exec_termination.rs row");

    row["expected_cases"]
        .as_array()
        .expect("exec_termination.rs row should contain expected_cases")
        .iter()
        .map(|entry| CaseMetadata {
            case_id: entry["case_id"]
                .as_str()
                .expect("case_id should be a string")
                .to_string(),
            upstream_case_id: entry["upstream_case_id"].as_str().unwrap_or("").to_string(),
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
                                .expect("expected_error_patterns values should be strings")
                                .to_string()
                        })
                        .collect()
                })
                .unwrap_or_default(),
        })
        .collect()
}

#[test]
fn exec_termination_rs_expected_case_metadata_is_exact() {
    let source = std::fs::read_to_string(exec_termination_port_path())
        .expect("exec_termination port should be readable");
    let file =
        syn::parse_file(&source).expect("exec_termination port should parse as ordinary Rust");
    assert_eq!(metadata_entries(&file), expected_metadata());
}

#[test]
fn exec_termination_rs_expected_case_metadata_matches_manifest() {
    let source = std::fs::read_to_string(exec_termination_port_path())
        .expect("exec_termination port should be readable");
    let file =
        syn::parse_file(&source).expect("exec_termination port should parse as ordinary Rust");
    assert_eq!(metadata_entries(&file), manifest_expected_metadata());
}

#[test]
fn exec_termination_rs_port_file_is_rust_syntax() {
    let source = std::fs::read_to_string(exec_termination_port_path())
        .expect("exec_termination port should be readable");
    syn::parse_file(&source).expect("exec_termination port should parse as ordinary Rust syntax");
}

#[test]
fn exec_termination_rs_pinned_upstream_case_shapes_are_present() {
    let path = pinned_upstream_exec_termination_path();
    if !path.exists() {
        eprintln!(
            "skipping pinned upstream exec_termination.rs shape check; missing {}",
            path.display()
        );
        return;
    }

    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", path.display()));
    for expected in [
        "#[test] recursive_exec_function_with_decreases_clause",
        "#[test] recursive_exec_function_with_decreases_clause_exec_allows_no_decreases_clause",
        "#[test] recursive_exec_function_with_decreases_clause_exec_allows_no_decreases_clause_fails",
        "#[test] recursive_exec_function_needs_decreases_clause",
        "#[test] mutually_recursive_exec_functions_need_decreases_clause",
        "#[test] mutually_recursive_exec_functions_with_extra_dependency_need_decreases_clause",
        "#[test] mutually_recursive_exec_functions_in_different_modules_need_decreases_clause",
        "#[test] while_loop_needs_decreases_clause",
        "#[test] nested_while_loops_need_decreases_clauses",
        "#[test] loop_with_break_with_decreases_clause",
        "#[test] loop_with_break_need_decreases_clause",
        "#[test] for_loop_with_decreases_clause",
        "#[test] for_loop_2_with_decreases_clause",
        "#[test] for_loop_doesnt_need_explicit_decreases_clause",
        "#[test] nontermination_infinite_loop_allowed_with_attribute",
        "#[test] nontermination_infinite_loop_with_ghost_allowed_with_attribute",
        "#[test] exec_recursive_function_with_while_loop_with_loop_isolation_false",
        "#[test] exec_recursive_function_with_while_loop_assume_termination",
        "#[test] exec_terminating_function_can_call_nonterminating_function",
        "#[test] exec_termination_flag_1",
        "#[test] exec_termination_flag_2",
        "#[test] exec_termination_flag_3",
        "#[test] exec_termination_flag_4",
        "#[test] exec_termination_flag_5",
        "exec_allows_no_decreases_clause",
        "assume_termination",
        "#[verifier::loop_isolation(false)]",
        "loop must have a decreases clause",
        "recursive function must have a decreases clause",
        "trait method declaration cannot declare exec_allows_no_decreases_clause",
    ] {
        assert!(
            source.contains(expected),
            "pinned upstream exec_termination.rs should still contain {expected}"
        );
    }
}

#[test]
fn exec_termination_rs_verified_subset_verifies_from_file() {
    let path = exec_termination_port_path();
    let path = path
        .to_str()
        .expect("exec_termination port path should be UTF-8");

    for (case, upstream_case) in VERIFIED_CASES {
        let result = verify_case(path, case, upstream_case);
        assert!(
            matches!(result, VerifyResult::Verified),
            "{case} ({upstream_case}) should verify, got: {result:?}"
        );
    }
}

#[test]
fn exec_termination_rs_counterexample_subset_is_rejected_from_file() {
    let path = exec_termination_port_path();
    let path = path
        .to_str()
        .expect("exec_termination port path should be UTF-8");

    for (case, upstream_case) in COUNTEREXAMPLE_CASES {
        let result = verify_case(path, case, upstream_case);
        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "{case} ({upstream_case}) should be rejected, got: {result:?}"
        );
    }
}

#[test]
fn exec_termination_rs_loop_decreases_boundary_fails_closed_from_file() {
    let path = exec_termination_port_path();
    let path = path
        .to_str()
        .expect("exec_termination port path should be UTF-8");

    for (case, upstream_case, expected_terms) in FAIL_CLOSED_CASES {
        expect_fail_closed(path, case, upstream_case, expected_terms);
    }
}
