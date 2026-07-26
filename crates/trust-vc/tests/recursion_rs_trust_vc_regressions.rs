// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Executable guards for the current upstream recursion.rs TrustVc scout slice.
//!
//! These tests intentionally do not claim full Verus recursion.rs parity. They
//! pin bounded Rust-valid recursive spec-function compute witnesses,
//! deterministic wrong-value counterexamples, parsed expected-case metadata,
//! upstream shape anchors, and fail-closed recursion/decreases/fuel boundaries
//! while the canonical manifest keeps `source/rust_verify_test/tests/recursion.rs`
//! classified as unsupported. Solver `Unknown` is not accepted as evidence.

mod common;

use std::{
    collections::{BTreeMap, BTreeSet},
    path::{Path, PathBuf},
};
use trust_vc_core::{
    extract_verification_conditions_with_file_context, verify_function_from_file, VerifyResult,
};

fn recursion_port_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/ported/recursion.rs")
}

fn pinned_upstream_recursion_path() -> PathBuf {
    common::pinned_verus_test_path("recursion.rs")
}

fn verus_manifest_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/verus-tests.json")
}

fn port_file() -> syn::File {
    let source =
        std::fs::read_to_string(recursion_port_path()).expect("recursion port should be readable");
    syn::parse_file(&source).expect("recursion port should parse as ordinary Rust syntax")
}

fn port_function<'a>(file: &'a syn::File, case: &str, upstream_case: &str) -> &'a syn::ItemFn {
    file.items
        .iter()
        .find_map(|item| match item {
            syn::Item::Fn(function) if function.sig.ident == case => Some(function),
            _ => None,
        })
        .unwrap_or_else(|| panic!("{case} ({upstream_case}) should exist in recursion port"))
}

fn referenced_array_const(file: &syn::File, const_name: &str) -> syn::ExprArray {
    let const_item = file
        .items
        .iter()
        .find_map(|item| match item {
            syn::Item::Const(item) if item.ident == const_name => Some(item),
            _ => None,
        })
        .unwrap_or_else(|| panic!("recursion port should define {const_name}"));

    let syn::Expr::Reference(reference) = const_item.expr.as_ref() else {
        panic!("{const_name} should be a referenced array");
    };
    let syn::Expr::Array(array) = reference.expr.as_ref() else {
        panic!("{const_name} should reference an array");
    };
    array.clone()
}

fn verify_case_with_obligations(case: &str, upstream_case: &str) -> (VerifyResult, usize) {
    let file = port_file();
    let function = port_function(&file, case, upstream_case);
    let vc = extract_verification_conditions_with_file_context(&file, function)
        .unwrap_or_else(|err| panic!("{case} ({upstream_case}) should extract VCs: {err}"));
    let obligations = vc.obligations().len();

    (vc.verify(), obligations)
}

fn reject_unknown(result: &VerifyResult, case: &str, upstream_case: &str) {
    if let VerifyResult::Unknown { reason, .. } = result {
        panic!(
            "{case} ({upstream_case}) returned solver Unknown, which is not stable evidence: {reason}"
        );
    }
}

fn fail_closed_message(path: &str, case: &str, upstream_case: &str) -> String {
    match verify_function_from_file(path, case) {
        Err(err) => err.to_string(),
        Ok(VerifyResult::Error { message }) => message,
        Ok(VerifyResult::Unknown { reason, .. }) => {
            panic!(
                "{case} ({upstream_case}) returned solver Unknown, which is not stable fail-closed evidence: {reason}"
            )
        }
        Ok(other) => {
            panic!("{case} ({upstream_case}) should fail closed with Error, got: {other:?}")
        }
    }
}

fn literal_string(expr: &syn::Expr) -> String {
    match expr {
        syn::Expr::Lit(syn::ExprLit {
            lit: syn::Lit::Str(lit),
            ..
        }) => lit.value(),
        _ => panic!("expected string literal in recursion metadata"),
    }
}

fn literal_usize(expr: &syn::Expr) -> usize {
    match expr {
        syn::Expr::Lit(syn::ExprLit {
            lit: syn::Lit::Int(lit),
            ..
        }) => lit
            .base10_parse::<usize>()
            .unwrap_or_else(|err| panic!("expected usize literal in recursion metadata: {err}")),
        _ => panic!("expected usize literal in recursion metadata"),
    }
}

#[derive(Debug, Eq, PartialEq)]
struct CaseMetadata {
    case_id: String,
    upstream_case_id: String,
    expected_verdict: String,
    min_obligations: usize,
    expected_error_patterns: Vec<String>,
}

fn parse_expected_error_patterns(file: &syn::File) -> BTreeMap<String, Vec<String>> {
    let array = referenced_array_const(file, "RECURSION_RS_EXPECTED_ERROR_PATTERNS");
    let mut entries = BTreeMap::new();

    for entry in &array.elems {
        let syn::Expr::Tuple(tuple) = entry else {
            panic!("expected tuple recursion error-pattern metadata entry");
        };
        assert_eq!(
            tuple.elems.len(),
            2,
            "error-pattern entries should have case and fragments"
        );
        let case_id = literal_string(&tuple.elems[0]);
        let syn::Expr::Reference(patterns_reference) = &tuple.elems[1] else {
            panic!("error patterns should be a referenced array");
        };
        let syn::Expr::Array(patterns_array) = patterns_reference.expr.as_ref() else {
            panic!("error patterns should reference an array");
        };
        let previous = entries.insert(
            case_id.clone(),
            patterns_array.elems.iter().map(literal_string).collect(),
        );
        assert!(
            previous.is_none(),
            "duplicate recursion error patterns for {case_id}"
        );
    }

    entries
}

fn parse_expected_case_metadata(file: &syn::File) -> Vec<CaseMetadata> {
    let array = referenced_array_const(file, "RECURSION_RS_EXPECTED_CASES");
    let mut error_patterns = parse_expected_error_patterns(file);
    let mut seen = BTreeSet::new();

    let entries = array
        .elems
        .iter()
        .map(|entry| {
            let syn::Expr::Tuple(tuple) = entry else {
                panic!("expected tuple recursion metadata entry");
            };
            assert_eq!(
                tuple.elems.len(),
                4,
                "metadata entries should have case, upstream case, status, and min obligations"
            );
            let case_id = literal_string(&tuple.elems[0]);
            assert!(
                seen.insert(case_id.clone()),
                "duplicate recursion metadata for {case_id}"
            );
            CaseMetadata {
                expected_error_patterns: error_patterns
                    .remove(case_id.as_str())
                    .unwrap_or_default(),
                case_id,
                upstream_case_id: literal_string(&tuple.elems[1]),
                expected_verdict: literal_string(&tuple.elems[2]),
                min_obligations: literal_usize(&tuple.elems[3]),
            }
        })
        .collect::<Vec<_>>();
    assert!(
        error_patterns.is_empty(),
        "error-pattern metadata should not contain orphan cases: {error_patterns:?}"
    );
    entries
}

const EXPECTED_CASE_METADATA: &[(&str, &str, &str, usize)] = &[
    (
        "basic_correctness_expr_small_compute_verified",
        "basic_correctness_expr",
        "verified",
        1,
    ),
    (
        "basic_correctness_expr_wrong_value_counterexample",
        "basic_correctness_expr",
        "counterexample",
        1,
    ),
    (
        "basic_decreases_by_int_guarded_compute_verified",
        "",
        "verified",
        1,
    ),
    (
        "basic_decreases_by_int_guarded_wrong_value_counterexample",
        "",
        "counterexample",
        1,
    ),
    (
        "multi_call_recursive_spec_small_compute_verified",
        "",
        "verified",
        1,
    ),
    (
        "multi_call_recursive_spec_wrong_value_counterexample",
        "",
        "counterexample",
        1,
    ),
    (
        "lexicographic_recursive_spec_small_compute_verified",
        "",
        "verified",
        1,
    ),
    (
        "lexicographic_recursive_spec_wrong_value_counterexample",
        "",
        "counterexample",
        1,
    ),
    // AUDITED FLIP (2026-07-08): error -> verified. The B5 mutual-recursion
    // defining-axiom feature (ad62cc3) removed the "recursive source spec
    // function dependency" rejection; compute now genuinely evaluates through
    // the a->b->a cycle. Soundness probed: TRUE claim a(2)==2 Verifies, FALSE
    // claim a(2)==3 is a Counterexample — not vacuous.
    (
        "mutually_recursive_expressions_currently_fail_closed",
        "mutually_recursive_expressions",
        "verified",
        1,
    ),
    (
        "recursive_reveal_with_fuel_currently_fail_closed",
        "",
        "error",
        0,
    ),
    (
        "multidecrease_decreases_to_currently_fail_closed",
        "",
        "error",
        0,
    ),
    ("decreases_by_clause_currently_fail_closed", "", "error", 0),
    ("recommends_by_clause_currently_fail_closed", "", "error", 0),
    // AUDITED FLIP 2026-07-09: slice B: old(value)==old(value) tautology now verifies; upstream rejects diagnostically - documented scout divergence
    (
        "mutable_reference_old_state_decreases_currently_fail_closed",
        "",
        "verified",
        1,
    ),
];

const FAIL_CLOSED_CASES: &[(&str, &str, &[&str])] = &[
    // mutually_recursive_expressions_currently_fail_closed removed 2026-07-08:
    // it now VERIFIES via the B5 mutual-recursion defining axioms (ad62cc3) —
    // see the audited flip in EXPECTED_CASES.
    (
        "recursive_reveal_with_fuel_currently_fail_closed",
        "",
        &[
            "Unsupported reveal_with_fuel!()",
            "unsupported macros are rejected",
        ],
    ),
    (
        "multidecrease_decreases_to_currently_fail_closed",
        "",
        &[
            "Unsupported decreases_to!()",
            "unsupported macros are rejected",
        ],
    ),
    (
        "decreases_by_clause_currently_fail_closed",
        "",
        &[
            "Unsupported decreases_by!()",
            "unsupported macros are rejected",
        ],
    ),
    (
        "recommends_by_clause_currently_fail_closed",
        "",
        &[
            "Unsupported recommends_by!()",
            "unsupported macros are rejected",
        ],
    ),
    // mutable_reference_old_state_decreases_currently_fail_closed removed 2026-07-09: audited slice-B flip.
];

fn expected_case_metadata() -> Vec<CaseMetadata> {
    let mut error_patterns = FAIL_CLOSED_CASES
        .iter()
        .map(|(case_id, _, patterns)| {
            (
                *case_id,
                patterns
                    .iter()
                    .map(|pattern| (*pattern).to_string())
                    .collect::<Vec<_>>(),
            )
        })
        .collect::<BTreeMap<_, _>>();

    let entries = EXPECTED_CASE_METADATA
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
        .collect::<Vec<_>>();
    assert!(
        error_patterns.is_empty(),
        "expected error-pattern inventory should not contain orphan cases: {error_patterns:?}"
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
            entry["upstream_path"].as_str() == Some("source/rust_verify_test/tests/recursion.rs")
        })
        .expect("Verus manifest should contain recursion.rs row");

    row["expected_cases"]
        .as_array()
        .expect("recursion.rs row should contain expected_cases")
        .iter()
        .map(|case| CaseMetadata {
            case_id: case["case_id"]
                .as_str()
                .expect("manifest case should contain case_id")
                .to_string(),
            upstream_case_id: case["upstream_case_id"]
                .as_str()
                .expect("manifest case should contain upstream_case_id")
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
            expected_error_patterns: case["expected_error_patterns"]
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
fn recursion_rs_port_file_is_rust_syntax() {
    let source =
        std::fs::read_to_string(recursion_port_path()).expect("recursion port should be readable");
    syn::parse_file(&source).expect("recursion port should parse as ordinary Rust syntax");
}

#[test]
fn recursion_rs_pinned_upstream_case_shapes_are_present() {
    let path = pinned_upstream_recursion_path();
    if !path.exists() {
        eprintln!(
            "skipping pinned upstream recursion.rs shape check; missing {}",
            path.display()
        );
        return;
    }

    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", path.display()));
    for expected in [
        "#[test] basic_correctness_expr",
        "#[test] basic_correctness_expr_fail",
        "#[test] basic_correctness_stmt",
        "#[test] basic_correctness_stmt_fail",
        "#[test] mutually_recursive_expressions",
        "#[test] mutually_recursive_expressions_insufficient_fuel",
        "#[test] mutually_recursive_statements",
        "#[test] expr_decrease_fail_1",
        "#[test] expr_wrong_decreases",
        "#[test] mutual_expr_decrease_fail",
        "#[test] multidecrease1",
        "#[test] termination_checked_before_definition1",
        "#[test] termination_checked_across_modules",
        "#[test] basic_decreases_by",
        "#[test] basic_decreases_by_int",
        "#[test] proof_decreases_when_ok",
        "#[test] proof_decreases_recommends_fail",
        "#[test] mutable_reference_decreases_2_fail",
        "#[test] decrease_through_seq",
        "#[test] height_intrinsic",
        "#[test] mutual_recursion_result_incompleteness_regression_564_1",
        "#[test] decreases_checks_assert_by",
        "#[test] recursive_through_struct_with_invariants_ok",
        "recursive function must have a decreases clause",
        "reveal_with_fuel(count_down_a, 2);",
        "decreases_by(check_arith_sum)",
        "decreases_when(i >= 0)",
        "recommends_by",
        "*old(s)",
        "decreases_to!(j, k => j, k - 1)",
    ] {
        assert!(
            source.contains(expected),
            "pinned upstream recursion.rs should still contain {expected}"
        );
    }
}

#[test]
fn recursion_rs_expected_case_metadata_is_exact_and_schema_valid() {
    let file = port_file();
    let actual = parse_expected_case_metadata(&file);
    assert_eq!(
        actual,
        expected_case_metadata(),
        "recursion port expected-case metadata should match the regression inventory"
    );

    let source =
        std::fs::read_to_string(recursion_port_path()).expect("recursion port should be readable");
    assert!(
        source.contains("UPSTREAM_RECURSION_RS_PINNED_CASES")
            && source.contains("upstream_recursion_rs_pinned_cases"),
        "recursion port should expose pinned upstream case metadata"
    );
    assert!(
        source.contains("RECURSION_RS_EXPECTED_CASES")
            && source.contains("recursion_rs_expected_cases"),
        "recursion port should expose expected-case metadata helpers"
    );
    assert!(
        source.contains("RECURSION_RS_EXPECTED_ERROR_PATTERNS")
            && source.contains("recursion_rs_expected_error_patterns"),
        "recursion port should expose fail-closed error-pattern metadata helpers"
    );

    for case in actual {
        assert!(
            matches!(
                case.expected_verdict.as_str(),
                "verified" | "counterexample" | "error"
            ),
            "recursion metadata for {} should use only verified/counterexample/error, got {}",
            case.case_id,
            case.expected_verdict
        );
        assert!(
            !case.expected_verdict.eq_ignore_ascii_case("unknown"),
            "recursion metadata must not accept Unknown as evidence for {}",
            case.case_id
        );
        assert!(
            case.upstream_case_id.is_empty()
                || case
                    .upstream_case_id
                    .chars()
                    .all(|c| c.is_ascii_alphanumeric() || c == '_'),
            "{} upstream_case_id should be empty or an exact upstream identifier, got {:?}",
            case.case_id,
            case.upstream_case_id
        );
        assert_eq!(
            case.expected_error_patterns.is_empty(),
            case.expected_verdict != "error",
            "{} should publish expected_error_patterns exactly for error cases only",
            case.case_id
        );
    }
}

#[test]
fn recursion_rs_expected_case_metadata_matches_manifest() {
    assert_eq!(
        parse_expected_case_metadata(&port_file()),
        manifest_expected_metadata(),
        "recursion.rs manifest expected_cases should match port metadata and fail-closed patterns exactly"
    );
}

#[test]
fn recursion_rs_non_error_expected_cases_match_statuses_and_obligation_counts() {
    let file = port_file();
    for case in parse_expected_case_metadata(&file)
        .into_iter()
        .filter(|case| case.expected_verdict != "error")
    {
        let (result, obligations) =
            verify_case_with_obligations(&case.case_id, &case.upstream_case_id);
        reject_unknown(&result, &case.case_id, &case.upstream_case_id);
        assert!(
            obligations >= case.min_obligations,
            "{} ({}) should collect at least {} obligation(s), got {obligations}",
            case.case_id,
            case.upstream_case_id,
            case.min_obligations
        );
        match case.expected_verdict.as_str() {
            "verified" => assert!(
                matches!(result, VerifyResult::Verified),
                "{} ({}) should verify, got: {result:?}",
                case.case_id,
                case.upstream_case_id
            ),
            "counterexample" => assert!(
                matches!(result, VerifyResult::Counterexample { .. }),
                "{} ({}) should be rejected, got: {result:?}",
                case.case_id,
                case.upstream_case_id
            ),
            other => panic!(
                "{} ({}) has unsupported non-error status {other}",
                case.case_id, case.upstream_case_id
            ),
        }
    }
}

#[test]
fn recursion_rs_error_expected_cases_fail_closed_from_file() {
    let path = recursion_port_path();
    let path = path.to_str().expect("recursion port path should be UTF-8");
    let metadata = parse_expected_case_metadata(&port_file());

    for (case, upstream_case, expected_fragments) in FAIL_CLOSED_CASES {
        let metadata_case = metadata
            .iter()
            .find(|metadata_case| metadata_case.case_id.as_str() == *case)
            .unwrap_or_else(|| panic!("{case} should be present in recursion expected metadata"));
        assert_eq!(
            metadata_case.expected_verdict.as_str(),
            "error",
            "{case} should be metadata status error"
        );
        assert_eq!(
            metadata_case.min_obligations, 0,
            "{case} error metadata should not claim extracted obligations"
        );
        assert_eq!(
            metadata_case.expected_error_patterns.as_slice(),
            expected_fragments
                .iter()
                .map(|fragment| (*fragment).to_string())
                .collect::<Vec<_>>()
                .as_slice(),
            "{case} should publish exact fail-closed fragments"
        );

        let message = fail_closed_message(path, case, upstream_case);

        for expected_fragment in *expected_fragments {
            assert!(
                message.contains(expected_fragment),
                "{case} ({upstream_case}) error should contain {expected_fragment:?}, got: {message}"
            );
        }
    }

    for case in metadata
        .iter()
        .filter(|case| case.expected_verdict.as_str() == "error")
    {
        assert!(
            FAIL_CLOSED_CASES
                .iter()
                .any(|(fail_closed_case, _, _)| *fail_closed_case == case.case_id.as_str()),
            "{} ({}) should have an explicit fail-closed fragment assertion",
            case.case_id,
            case.upstream_case_id
        );
    }
}
