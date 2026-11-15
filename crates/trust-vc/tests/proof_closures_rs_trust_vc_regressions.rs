// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Executable guards for the first upstream proof_closures.rs TrustVc scout.
//!
//! These tests intentionally keep the upstream file as an unsupported gap. They
//! prove only a Rust-valid TrustVc proof-function-contract subset that mirrors
//! the simplest proof closure pre/post obligations, including one-, two-, and
//! zero-argument contract shapes, a helper-call shape, and proof-call assignment
//! tracking. They reject false construction and call obligations, pin direct
//! proof-local closure/capture/subexpression boundaries as fail-closed
//! source-extraction boundaries, and reject solver `Unknown` as evidence.

mod common;

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use trust_vc_core::{
    extract_verification_conditions_with_file_context, verify_function_from_file, VerifyResult,
};

fn proof_closures_port_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/ported/proof_closures.rs")
}

fn verus_manifest_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/verus-tests.json")
}

fn proof_closures_upstream_path() -> PathBuf {
    common::pinned_verus_test_path("proof_closures.rs")
}

fn verify_port_case_with_obligations(case: &str, upstream_case: &str) -> (VerifyResult, usize) {
    let path = proof_closures_port_path();
    let path_str = path
        .to_str()
        .expect("proof_closures port path should be UTF-8");
    let result = verify_function_from_file(path_str, case)
        .unwrap_or_else(|err| panic!("{case} ({upstream_case}) should extract: {err}"));
    if let VerifyResult::Unknown { reason, .. } = &result {
        panic!(
            "{case} ({upstream_case}) returned solver Unknown, which is not stable evidence: {reason}"
        );
    }

    let source = std::fs::read_to_string(&path)
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
        .unwrap_or_else(|err| panic!("{case} ({upstream_case}) should extract: {err}"));

    (result, vc.obligations().len())
}

fn fail_closed_message(case: &str, upstream_case: &str) -> String {
    let path = proof_closures_port_path();
    let path = path
        .to_str()
        .expect("proof_closures port path should be UTF-8");

    match verify_function_from_file(path, case) {
        Err(err) => err.to_string(),
        Ok(VerifyResult::Error { message }) => message,
        Ok(VerifyResult::Unknown { reason, .. }) => {
            panic!("{case} ({upstream_case}) returned solver Unknown, which is not stable fail-closed evidence: {reason}")
        }
        Ok(other) => {
            panic!("{case} ({upstream_case}) should fail closed with Error, got: {other:?}")
        }
    }
}

const VERIFIED_CASES: &[(&str, &str, usize)] = &[
    (
        "proof_closure_one_arg_contract_verified",
        "basic_test / one-argument proof closure contract",
        1,
    ),
    (
        "proof_closure_two_arg_contract_verified",
        "basic_test_2_args / two-argument proof closure contract",
        1,
    ),
    (
        "proof_closure_zero_arg_return_contract_verified",
        "basic_test_0_args / zero-argument proof closure return surrogate",
        1,
    ),
    (
        "proof_closure_identity_call_contract_verified",
        "test_calls_in_assignments_to_mut_var / identity proof-call contract",
        1,
    ),
    (
        "proof_closure_helper_application_verified",
        "basic_test / valid proof closure call postcondition",
        1,
    ),
    (
        "proof_closure_calls_in_assignment_verified",
        "test_calls_in_assignments_to_mut_var / mutable assignment call subset",
        1,
    ),
    // 2026-09-11: direct proof-local closure application (one-arg, zero-arg, as a subexpression) verifies.
    (
        "proof_closure_local_application_verified",
        "basic_test / direct proof-local closure application",
        1,
    ),
    (
        "proof_closure_zero_arg_local_application_verified",
        "basic_test_0_args / direct zero-argument proof-local closure application",
        1,
    ),
    (
        "proof_closure_call_as_subexpression_verified",
        "test_call_as_subexpression / proof-local closure call as a comparison operand",
        1,
    ),
];

const COUNTEREXAMPLE_CASES: &[(&str, &str, usize)] = &[
    (
        "proof_closure_one_arg_bad_ensures_counterexample",
        "test_ensures_fail / false one-argument proof closure postcondition",
        1,
    ),
    (
        "proof_closure_two_arg_bad_ensures_counterexample",
        "test_ensures_fail_2_args / false two-argument proof closure postcondition",
        1,
    ),
    (
        "proof_closure_zero_arg_bad_ensures_counterexample",
        "test_ensures_fail_0_args / false zero-argument proof closure postcondition",
        1,
    ),
    (
        "proof_closure_helper_bad_call_requires_counterexample",
        "test_call_requires_fail / invalid proof closure call precondition",
        1,
    ),
    (
        "proof_closure_helper_bad_call_ensures_counterexample",
        "test_call_ensures_fail / invalid proof closure call post-use assertion",
        1,
    ),
    (
        "proof_closure_calls_in_assignment_false_tail_counterexample",
        "test_calls_in_assignments_to_mut_var_fail / false tail after assignment calls",
        1,
    ),
    (
        "proof_closure_local_application_liar_counterexample",
        "basic_test / direct proof-local closure application liar",
        1,
    ),
    (
        "proof_closure_zero_arg_local_application_liar_counterexample",
        "basic_test_0_args / zero-argument proof-local closure application liar",
        1,
    ),
    (
        "proof_closure_call_as_subexpression_liar_counterexample",
        "test_call_as_subexpression / closure call as operand liar",
        1,
    ),
];

const FAIL_CLOSED_CASES: &[(&str, &str, &[&str])] = &[
    (
        "proof_closure_move_capture_application_currently_errors",
        "closure_depends_on_type_param / direct move-capture proof-local closure",
        &[
            "unresolved variable `y`",
            "unknown return type for function 'f'",
            "standalone closure",
            "closure",
        ],
    ),
    (
        "proof_closure_mut_capture_application_currently_errors",
        "disallowed_mut_capture1 / mutable capture proof-local closure boundary",
        &[
            "unknown return type for function 'f'",
            "standalone closure",
            "assignment",
            "closure",
        ],
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

fn proof_closures_port_file() -> syn::File {
    let source =
        std::fs::read_to_string(proof_closures_port_path()).expect("proof_closures port readable");
    syn::parse_file(&source).expect("proof_closures port should parse as ordinary Rust syntax")
}

fn referenced_array_const(file: &syn::File, const_name: &str) -> syn::ExprArray {
    let const_item = file
        .items
        .iter()
        .find_map(|item| match item {
            syn::Item::Const(item) if item.ident == const_name => Some(item),
            _ => None,
        })
        .unwrap_or_else(|| panic!("proof_closures port should define {const_name}"));
    let syn::Expr::Reference(reference) = const_item.expr.as_ref() else {
        panic!("{const_name} should be a referenced array literal");
    };
    let syn::Expr::Array(array) = reference.expr.as_ref() else {
        panic!("{const_name} should be a referenced array literal");
    };

    array.clone()
}

fn literal_string(expr: &syn::Expr) -> String {
    let syn::Expr::Lit(syn::ExprLit {
        lit: syn::Lit::Str(lit),
        ..
    }) = expr
    else {
        panic!("expected string literal");
    };

    lit.value()
}

fn literal_usize(expr: &syn::Expr) -> usize {
    let syn::Expr::Lit(syn::ExprLit {
        lit: syn::Lit::Int(lit),
        ..
    }) = expr
    else {
        panic!("expected integer literal");
    };

    lit.base10_parse()
        .expect("integer literal should fit usize")
}

fn string_slice(expr: &syn::Expr) -> Vec<String> {
    let syn::Expr::Reference(reference) = expr else {
        panic!("expected referenced string-slice literal");
    };
    let syn::Expr::Array(array) = reference.expr.as_ref() else {
        panic!("expected referenced string-slice literal");
    };

    array.elems.iter().map(literal_string).collect()
}

fn expected_error_patterns_from_fail_closed_cases() -> Vec<(String, Vec<String>)> {
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

fn port_fail_closed_error_pattern_metadata() -> Vec<(String, Vec<String>)> {
    let file = proof_closures_port_file();
    let array = referenced_array_const(&file, "PROOF_CLOSURES_RS_EXPECTED_ERROR_PATTERNS");
    array
        .elems
        .iter()
        .map(|entry| {
            let syn::Expr::Tuple(tuple) = entry else {
                panic!("PROOF_CLOSURES_RS_EXPECTED_ERROR_PATTERNS entries should be tuples");
            };
            assert_eq!(
                tuple.elems.len(),
                2,
                "proof_closures expected-error-pattern tuple arity should stay fixed"
            );

            (
                literal_string(&tuple.elems[0]),
                string_slice(&tuple.elems[1]),
            )
        })
        .collect()
}

fn port_expected_metadata() -> Vec<CaseMetadata> {
    let file = proof_closures_port_file();
    let patterns_by_case: BTreeMap<String, Vec<String>> = port_fail_closed_error_pattern_metadata()
        .into_iter()
        .collect();
    let array = referenced_array_const(&file, "PROOF_CLOSURES_RS_EXPECTED_CASES");

    array
        .elems
        .iter()
        .map(|entry| {
            let syn::Expr::Tuple(tuple) = entry else {
                panic!("PROOF_CLOSURES_RS_EXPECTED_CASES entries should be tuples");
            };
            assert_eq!(
                tuple.elems.len(),
                4,
                "proof_closures expected-case tuple arity should stay fixed"
            );

            let case_id = literal_string(&tuple.elems[0]);
            CaseMetadata {
                expected_error_patterns: patterns_by_case
                    .get(&case_id)
                    .cloned()
                    .unwrap_or_default(),
                case_id,
                upstream_case_id: literal_string(&tuple.elems[1]),
                expected_verdict: literal_string(&tuple.elems[2]),
                min_obligations: literal_usize(&tuple.elems[3]),
            }
        })
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
            entry["upstream_path"].as_str()
                == Some("source/rust_verify_test/tests/proof_closures.rs")
        })
        .expect("Verus manifest should contain proof_closures.rs row");

    row["expected_cases"]
        .as_array()
        .expect("proof_closures.rs row should contain expected_cases")
        .iter()
        .map(|entry| CaseMetadata {
            case_id: entry["case_id"]
                .as_str()
                .expect("case_id should be a string")
                .to_string(),
            upstream_case_id: entry
                .get("upstream_case_id")
                .and_then(serde_json::Value::as_str)
                .unwrap_or("")
                .to_string(),
            expected_verdict: entry["expected_verdict"]
                .as_str()
                .expect("expected_verdict should be a string")
                .to_string(),
            min_obligations: entry["min_obligations"]
                .as_u64()
                .expect("min_obligations should be an integer")
                .try_into()
                .expect("min_obligations should fit usize"),
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
fn proof_closures_rs_port_file_is_rust_syntax() {
    let source =
        std::fs::read_to_string(proof_closures_port_path()).expect("proof_closures port readable");
    syn::parse_file(&source).expect("proof_closures port should parse as ordinary Rust syntax");
}

#[test]
fn proof_closures_rs_pinned_upstream_case_shapes_are_present() {
    let path = proof_closures_upstream_path();
    if !path.exists() {
        eprintln!(
            "skipping pinned upstream proof_closures.rs shape check; missing {}",
            path.display()
        );
        return;
    }

    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", path.display()));
    for expected in [
        "#[test] basic_test",
        "#[test] test_ensures_fail",
        "#[test] test_assert_requires_fail",
        "#[test] test_assert_not_ensures_fail",
        "#[test] test_call_requires_fail",
        "#[test] test_call_ensures_fail",
        "#[test] basic_test_2_args",
        "#[test] test_ensures_fail_2_args",
        "#[test] test_call_requires_fail_2_args",
        "#[test] basic_test_0_args",
        "#[test] test_ensures_fail_0_args",
        "#[test] pass_closure_via_typ_param",
        "#[test] pass_closure_via_typ_param_fn_once",
        "#[test] pass_closure_via_typ_param_fn_mut",
        "#[test] construct_exec_closure_in_spec_code_fail",
        "#[test] call_exec_closure_in_spec_code_fail",
        "#[test] mode_check_requires",
        "#[test] mode_check_ensures",
        "#[test] mode_check_return_value",
        "#[test] test_calls_in_assignments_to_mut_var",
        "#[test] test_calls_as_sub_expression",
        "#[test] old_works_for_params_from_outside_the_closure",
        "#[test] callee_is_computed_expression",
        "#[test] name_collisions",
        "#[test] return_unit",
        "#[test] disallowed_mut_capture1",
        "#[test] closure_depends_on_type_param",
        "#[test] right_decorations_for_tuple_arg",
        "#[test] ref_decoration_in_type_params_issue619",
        "#[test] usage2",
        "#[test] usage9",
        "#[test] reqens1",
        "#[test] tracked_args1",
        "#[test] tracked_recursive_type1",
        "proof_fn[Once]",
        "proof_fn[Mut]",
        "ProofFnReqEns",
        "tracked proof_fn",
    ] {
        assert!(
            source.contains(expected),
            "pinned upstream proof_closures.rs should still contain {expected}"
        );
    }
}

#[test]
fn proof_closures_rs_expected_case_metadata_is_exact() {
    let source =
        std::fs::read_to_string(proof_closures_port_path()).expect("proof_closures port readable");
    for expected in [
        "PROOF_CLOSURES_RS_EXPECTED_CASES",
        "proof_closures_rs_expected_cases",
        "PROOF_CLOSURES_RS_EXPECTED_ERROR_PATTERNS",
        "proof_closures_rs_expected_error_patterns",
    ] {
        assert!(
            source.contains(expected),
            "proof_closures port metadata should contain {expected}"
        );
    }

    let mut expected_case_names = port_expected_metadata()
        .into_iter()
        .map(|metadata| {
            assert_ne!(
                metadata.expected_verdict, "unknown",
                "proof_closures metadata must not accept Unknown as evidence for {}",
                metadata.case_id
            );
            metadata.case_id
        })
        .collect::<Vec<_>>();
    expected_case_names.sort_unstable();

    let mut categorized_case_names = VERIFIED_CASES
        .iter()
        .map(|(case, _, _)| *case)
        .chain(COUNTEREXAMPLE_CASES.iter().map(|(case, _, _)| *case))
        .chain(FAIL_CLOSED_CASES.iter().map(|(case, _, _)| *case))
        .collect::<Vec<_>>();
    categorized_case_names.sort_unstable();

    assert_eq!(
        expected_case_names, categorized_case_names,
        "every metadata case should have exactly one regression expectation"
    );
}

#[test]
fn proof_closures_rs_expected_error_pattern_metadata_is_exact() {
    assert_eq!(
        port_fail_closed_error_pattern_metadata(),
        expected_error_patterns_from_fail_closed_cases()
    );
}

#[test]
fn proof_closures_rs_expected_case_metadata_matches_manifest() {
    assert_eq!(port_expected_metadata(), manifest_expected_metadata());
}

#[test]
fn proof_closures_rs_error_cases_have_expected_error_patterns() {
    let mut patterns_by_case: BTreeMap<String, Vec<String>> =
        port_fail_closed_error_pattern_metadata()
            .into_iter()
            .collect();

    for expected_case in port_expected_metadata() {
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
                        "{} ({}) should declare expected_error_patterns",
                        expected_case.case_id, expected_case.upstream_case_id
                    )
                });
            assert!(
                !expected_patterns.is_empty(),
                "{} ({}) should declare at least one expected_error_patterns value",
                expected_case.case_id,
                expected_case.upstream_case_id
            );
            for expected_pattern in &expected_patterns {
                assert!(
                    !expected_pattern.trim().is_empty(),
                    "{} ({}) declares an empty expected_error_patterns value",
                    expected_case.case_id,
                    expected_case.upstream_case_id
                );
            }
        } else {
            assert!(
                !patterns_by_case.contains_key(&expected_case.case_id),
                "{} ({}) should not declare expected_error_patterns for {} evidence",
                expected_case.case_id,
                expected_case.upstream_case_id,
                expected_case.expected_verdict
            );
        }
    }

    assert!(
        patterns_by_case.is_empty(),
        "expected_error_patterns metadata should not contain orphan cases: {patterns_by_case:?}"
    );
}

#[test]
fn proof_closures_rs_verified_contract_subset_verifies_from_file() {
    for (case, upstream_case, min_obligations) in VERIFIED_CASES {
        let (result, obligations) = verify_port_case_with_obligations(case, upstream_case);
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
fn proof_closures_rs_counterexample_subset_is_rejected_from_file() {
    for (case, upstream_case, min_obligations) in COUNTEREXAMPLE_CASES {
        let (result, obligations) = verify_port_case_with_obligations(case, upstream_case);
        assert!(
            obligations >= *min_obligations,
            "{case} ({upstream_case}) should collect at least {min_obligations} obligation(s), got {obligations}"
        );
        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "{case} ({upstream_case}) should be rejected, got: {result:?}"
        );
    }
}

#[test]
fn proof_closures_rs_direct_proof_closure_application_fails_closed_from_file() {
    for (case, upstream_case, expected_fragments) in FAIL_CLOSED_CASES {
        let message = fail_closed_message(case, upstream_case);
        assert!(
            expected_fragments
                .iter()
                .any(|expected_fragment| message.contains(expected_fragment)),
            "{case} ({upstream_case}) error should contain one of {expected_fragments:?}, got: {message}"
        );
    }
}
