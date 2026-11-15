// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Executable guards for the first upstream prophecy.rs TrustVc scout slice.
//!
//! These tests intentionally keep `source/rust_verify_test/tests/prophecy.rs`
//! as an unsupported gap. They pin only stable verified surrogate cases, stable
//! counterexamples, and fail-closed prophecy/Ghost/Tracked/future boundaries;
//! solver Unknown outcomes are not accepted as evidence.

mod common;

use std::{
    collections::{BTreeMap, BTreeSet},
    path::{Path, PathBuf},
};
use trust_vc_core::{
    extract_verification_conditions_with_file_context, verify_function_from_file, VerifyResult,
};

#[derive(Debug, Eq, PartialEq, Ord, PartialOrd)]
struct ExpectedCaseMetadata {
    case_id: String,
    upstream_case_id: String,
    expected_verdict: String,
    min_obligations: usize,
    expected_error_patterns: Vec<String>,
}

fn prophecy_port_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/ported/prophecy.rs")
}

fn verus_manifest_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/verus-tests.json")
}

fn pinned_upstream_prophecy_path() -> PathBuf {
    common::pinned_verus_test_path("prophecy.rs")
}

fn port_file() -> syn::File {
    let source =
        std::fs::read_to_string(prophecy_port_path()).expect("prophecy port should be readable");
    syn::parse_file(&source).expect("prophecy port should parse as ordinary Rust syntax")
}

fn port_function<'a>(file: &'a syn::File, case: &str, upstream_case: &str) -> &'a syn::ItemFn {
    file.items
        .iter()
        .find_map(|item| match item {
            syn::Item::Fn(function) if function.sig.ident == case => Some(function),
            _ => None,
        })
        .unwrap_or_else(|| panic!("{case} ({upstream_case}) should exist in prophecy port"))
}

fn verify_case(path: &Path, case: &str, upstream_case: &str) -> (VerifyResult, usize) {
    let path = path.to_str().expect("prophecy port path should be UTF-8");
    let result = verify_function_from_file(path, case)
        .unwrap_or_else(|err| panic!("{case} ({upstream_case}) should extract: {err}"));

    if let VerifyResult::Unknown { reason, .. } = &result {
        panic!("{case} ({upstream_case}) returned solver Unknown, which is not stable evidence: {reason}");
    }

    let file = port_file();
    let function = port_function(&file, case, upstream_case);
    let vc = extract_verification_conditions_with_file_context(&file, function)
        .unwrap_or_else(|err| panic!("{case} ({upstream_case}) should extract VCs: {err}"));

    (result, vc.obligations().len())
}

fn expect_fail_closed(path: &Path, expected: &ExpectedCaseMetadata) {
    let path = path.to_str().expect("prophecy port path should be UTF-8");
    let message = match verify_function_from_file(path, &expected.case_id) {
        Err(err) => err.to_string(),
        Ok(VerifyResult::Error { message }) => message,
        Ok(VerifyResult::Unknown { reason, .. }) => {
            panic!(
                "{} ({}) returned solver Unknown, which is not stable evidence: {reason}",
                expected.case_id, expected.upstream_case_id
            )
        }
        Ok(result) => {
            panic!(
                "{} ({}) should fail closed with Error, got: {result:?}",
                expected.case_id, expected.upstream_case_id
            )
        }
    };

    for expected_fragment in &expected.expected_error_patterns {
        assert!(
            message.contains(expected_fragment),
            "{} ({}) error should contain {expected_fragment:?}, got: {message}",
            expected.case_id,
            expected.upstream_case_id
        );
    }
}

fn literal_string(expr: &syn::Expr) -> String {
    match expr {
        syn::Expr::Lit(syn::ExprLit {
            lit: syn::Lit::Str(lit),
            ..
        }) => lit.value(),
        _ => panic!("expected string literal in metadata"),
    }
}

fn literal_usize(expr: &syn::Expr) -> usize {
    match expr {
        syn::Expr::Lit(syn::ExprLit {
            lit: syn::Lit::Int(lit),
            ..
        }) => lit
            .base10_parse::<usize>()
            .unwrap_or_else(|err| panic!("expected usize literal in metadata: {err}")),
        _ => panic!("expected usize literal in metadata"),
    }
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

fn referenced_array_const<'a>(file: &'a syn::File, const_name: &str) -> &'a syn::ExprArray {
    let const_item = file
        .items
        .iter()
        .find_map(|item| match item {
            syn::Item::Const(item) if item.ident == const_name => Some(item),
            _ => None,
        })
        .unwrap_or_else(|| panic!("prophecy port should define {const_name}"));

    let syn::Expr::Reference(reference) = const_item.expr.as_ref() else {
        panic!("{const_name} should be a referenced array");
    };
    let syn::Expr::Array(array) = reference.expr.as_ref() else {
        panic!("{const_name} should reference an array");
    };

    array
}

fn error_pattern_entries(file: &syn::File) -> BTreeMap<String, Vec<String>> {
    let array = referenced_array_const(file, "PROPHECY_RS_FAIL_CLOSED_ERROR_PATTERNS");
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

fn parse_expected_case_metadata(file: &syn::File) -> Vec<ExpectedCaseMetadata> {
    let array = referenced_array_const(file, "PROPHECY_RS_EXPECTED_CASES");
    let mut error_patterns = error_pattern_entries(file);
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
        let patterns = error_patterns.remove(&case_id).unwrap_or_default();
        entries.push(ExpectedCaseMetadata {
            case_id,
            upstream_case_id: literal_string(&tuple.elems[1]),
            expected_verdict: literal_string(&tuple.elems[2]),
            min_obligations: literal_usize(&tuple.elems[3]),
            expected_error_patterns: patterns,
        });
    }

    assert!(
        error_patterns.is_empty(),
        "error-pattern metadata should not contain orphan cases: {error_patterns:?}"
    );
    entries
}

fn manifest_expected_case_metadata() -> Vec<ExpectedCaseMetadata> {
    let source =
        std::fs::read_to_string(verus_manifest_path()).expect("Verus manifest should be readable");
    let manifest: serde_json::Value =
        serde_json::from_str(&source).expect("Verus manifest should parse as JSON");
    let row = manifest["entries"]
        .as_array()
        .expect("Verus manifest should contain entries")
        .iter()
        .find(|entry| {
            entry["upstream_path"].as_str() == Some("source/rust_verify_test/tests/prophecy.rs")
        })
        .expect("Verus manifest should contain prophecy.rs row");

    row["expected_cases"]
        .as_array()
        .expect("prophecy manifest row should contain expected_cases")
        .iter()
        .map(|case| ExpectedCaseMetadata {
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

fn expected_metadata_from_tests() -> Vec<ExpectedCaseMetadata> {
    let mut metadata = Vec::new();
    for (case, upstream_case, min_obligations) in VERIFIED_CASES {
        metadata.push(ExpectedCaseMetadata {
            case_id: (*case).to_string(),
            upstream_case_id: (*upstream_case).to_string(),
            expected_verdict: "verified".to_string(),
            min_obligations: *min_obligations,
            expected_error_patterns: Vec::new(),
        });
    }
    for (case, upstream_case, min_obligations) in COUNTEREXAMPLE_CASES {
        metadata.push(ExpectedCaseMetadata {
            case_id: (*case).to_string(),
            upstream_case_id: (*upstream_case).to_string(),
            expected_verdict: "counterexample".to_string(),
            min_obligations: *min_obligations,
            expected_error_patterns: Vec::new(),
        });
    }
    for (case, upstream_case, expected_error_patterns) in FAIL_CLOSED_CASES {
        metadata.push(ExpectedCaseMetadata {
            case_id: (*case).to_string(),
            upstream_case_id: (*upstream_case).to_string(),
            expected_verdict: "error".to_string(),
            min_obligations: 0,
            expected_error_patterns: expected_error_patterns
                .iter()
                .map(|pattern| (*pattern).to_string())
                .collect(),
        });
    }
    metadata.sort();
    metadata
}

fn collect_port_function_names(file: &syn::File) -> BTreeSet<String> {
    file.items
        .iter()
        .filter_map(|item| match item {
            syn::Item::Fn(function) => {
                let name = function.sig.ident.to_string();
                if matches!(
                    name.as_str(),
                    "prophecy_rs_expected_cases" | "prophecy_rs_fail_closed_error_patterns"
                ) {
                    None
                } else {
                    Some(name)
                }
            }
            _ => None,
        })
        .collect()
}

fn schema_identifier(value: &str) -> bool {
    let mut chars = value.chars();
    let Some(first) = chars.next() else {
        return false;
    };

    (first.is_ascii_alphabetic() || first == '_')
        && chars.all(|ch| ch.is_ascii_alphanumeric() || ch == '_')
}

const VERIFIED_CASES: &[(&str, &str, usize)] = &[
    ("prophecy_once_flip_resolved_value_verified", "once_flip", 2),
    (
        "prophecy_dep2_value_binding_surrogate_verified",
        "proph_dep2",
        2,
    ),
    (
        "prophecy_trait_both_proph_surrogate_verified",
        "trait_and_impl_both_proph_ok",
        2,
    ),
    (
        "prophecy_trait_proph_nonprophetic_impl_surrogate_verified",
        "trait_proph_and_impl_not_proph_ok",
        2,
    ),
    (
        "prophecy_ghost_spec_wrapper_surrogate_verified",
        "ghost_ctor_okay_in_spec_code",
        2,
    ),
    (
        "prophecy_marked_location_reassign_verified",
        "proph_assign_to_proph_location_ok",
        2,
    ),
    (
        "prophecy_readonly_conditional_match_verified",
        "conditional_match3",
        1,
    ),
    ("prophecy_lemma_call_surrogate_verified", "lemma_call_ok", 3),
    (
        "prophecy_decls_in_conditional_verified",
        "decls_in_conditional",
        2,
    ),
    (
        "prophecy_resolution_state_transition_surrogate_verified",
        "once_flip",
        3,
    ),
];

const COUNTEREXAMPLE_CASES: &[(&str, &str, usize)] = &[
    (
        "prophecy_grandfather_paradox_counterexample",
        "grandfather_paradox",
        1,
    ),
    (
        "prophecy_calls_requires_ensures_counterexample",
        "calls_requires_ensures",
        1,
    ),
    (
        "prophecy_assign_to_nonproph_location_counterexample",
        "proph_assign_to_nonproph_location_bad",
        1,
    ),
    (
        "prophecy_assign_to_nonproph_location_exec_counterexample",
        "proph_assign_to_nonproph_location_bad2",
        1,
    ),
    (
        "prophecy_conditional_assignment_counterexample",
        "prophecy_conditional_assign",
        1,
    ),
    (
        "prophecy_conditional_assignment_else_counterexample",
        "prophecy_conditional_assign_else",
        1,
    ),
    (
        "prophecy_conditional_call_counterexample",
        "prophecy_conditional_call",
        1,
    ),
    (
        "prophecy_conditional_return_counterexample",
        "prophecy_conditional_return",
        1,
    ),
    (
        "prophecy_conditional_loop_counterexample",
        "prophecy_conditional_loop",
        1,
    ),
    (
        "prophecy_short_circuit_and_counterexample",
        "conditional_short_circuit_and",
        1,
    ),
    (
        "prophecy_short_circuit_or_counterexample",
        "conditional_short_circuit_or",
        1,
    ),
    (
        "prophecy_short_circuit_implies_counterexample",
        "conditional_short_circuit_implies",
        1,
    ),
    (
        "prophecy_conditional_match0_counterexample",
        "conditional_match0",
        1,
    ),
    (
        "prophecy_conditional_match1_counterexample",
        "conditional_match1",
        1,
    ),
    (
        "prophecy_conditional_match2_counterexample",
        "conditional_match2",
        1,
    ),
    (
        "prophecy_lemma_call_propagate_counterexample",
        "lemma_call_propagate",
        1,
    ),
    (
        "prophecy_return_value_flow_counterexample",
        "lemma_return_fail",
        1,
    ),
    (
        "prophecy_return_value_flow_explicit_counterexample",
        "lemma_return_fail2",
        1,
    ),
    (
        "prophecy_conditional_expression_counterexample",
        "conditional_expression_propagate",
        1,
    ),
    (
        "prophecy_conditional_expression_left_counterexample",
        "conditional_expression_propagate1",
        1,
    ),
    (
        "prophecy_conditional_expression_right_counterexample",
        "conditional_expression_propagate2",
        1,
    ),
    (
        "prophecy_double_resolve_state_counterexample",
        "grandfather_paradox",
        1,
    ),
];

const FAIL_CLOSED_CASES: &[(&str, &str, &[&str])] = &[
    (
        "prophecy_direct_value_currently_blocked",
        "proph_dep1",
        &[
            "Failed to lower obligation 'assertion_0'",
            "unsupported method `value() on type `Prophecy<bool>`",
            "method is not available in specification context",
        ],
    ),
    (
        "prophecy_trait_impl_prophetic_attr_currently_blocked",
        "trait_not_proph_impl_proph_err",
        &[
            "Failed to lower obligation 'assertion_0'",
            "unsupported method `value() on type `Prophecy<bool>`",
            "method is not available in specification context",
        ],
    ),
    (
        "prophecy_trait_body_nonprophetic_direct_value_currently_blocked",
        "trait_and_impl_both_proph_err",
        &[
            "Failed to lower obligation 'assertion_0'",
            "unknown return type for function 'trait_body_nonprophetic_direct_value'",
            "register it in TypeEnv via prepare_context",
        ],
    ),
    (
        "prophecy_trait_proph_general_call_currently_blocked",
        "trait_proph_err",
        &[
            "Failed to lower obligation 'assertion_0'",
            "unknown return type for function 'trait_proph_general_call'",
            "register it in TypeEnv via prepare_context",
        ],
    ),
    (
        "prophecy_trait_nonprophetic_impl_direct_value_currently_blocked",
        "trait_proph_and_impl_not_proph_err",
        &[
            "Failed to lower obligation 'assertion_0'",
            "unknown return type for function 'trait_nonprophetic_impl_direct_value'",
            "register it in TypeEnv via prepare_context",
        ],
    ),
    (
        "prophecy_decreases_proof_clause_currently_blocked",
        "decreases_clause_proof_fn_cannot_be_prophetic",
        &[
            "Failed to lower obligation 'assertion_0'",
            "unknown return type for function 'prophetic_rank'",
            "register it in TypeEnv via prepare_context",
        ],
    ),
    (
        "prophecy_decreases_exec_clause_currently_blocked",
        "decreases_clause_exec_fn_cannot_be_prophetic",
        &[
            "Failed to lower obligation 'assertion_0'",
            "unknown return type for function 'prophetic_rank'",
            "register it in TypeEnv via prepare_context",
        ],
    ),
    (
        "prophecy_decreases_loop_clause_currently_blocked",
        "decreases_clause_loop_cannot_be_prophetic",
        &[
            "Failed to lower obligation 'assertion_0'",
            "unknown return type for function 'prophetic_rank'",
            "register it in TypeEnv via prepare_context",
        ],
    ),
    (
        "prophecy_tracked_ghost_wrapper_currently_blocked",
        "ghost_ctor_fail_in_tracked_code",
        &[
            "Failed to lower obligation 'assertion_0'",
            "unknown return type for function 'Ghost'",
            "register it in TypeEnv via prepare_context",
        ],
    ),
    (
        "prophecy_ghost_wrapper_currently_blocked",
        "ghost_ctor_fail",
        &[
            "Failed to lower obligation 'assertion_0'",
            "unknown return type for function 'Ghost'",
            "register it in TypeEnv via prepare_context",
        ],
    ),
    (
        "prophecy_prophetic_decl_ghost_boundary_currently_blocked",
        "prophetic_decl_fail",
        &[
            "Failed to lower obligation 'assertion_0'",
            "unknown return type for function 'verifier_prophetic'",
            "register it in TypeEnv via prepare_context",
        ],
    ),
    (
        "prophecy_proof_tracked_argument_currently_blocked",
        "prophetic_func_fail",
        &[
            "Failed to lower obligation 'assertion_0'",
            "unknown return type for function 'Tracked'",
            "register it in TypeEnv via prepare_context",
        ],
    ),
    (
        "prophecy_proof_tracked_return_currently_blocked",
        "prophetic_func_fail_ret",
        &[
            "Failed to lower obligation 'assertion_0'",
            "unknown return type for function 'proof_tracked_return'",
            "register it in TypeEnv via prepare_context",
        ],
    ),
    (
        "prophecy_proof_tracked_argument_from_value_currently_blocked",
        "prophetic_func_fail2",
        &[
            "Failed to lower obligation 'assertion_0'",
            "unsupported method `value() on type `Prophecy<bool>`",
            "method is not available in specification context",
        ],
    ),
    (
        "prophecy_loop_condition_currently_blocked",
        "loop_condition_prophetic",
        &[
            "Failed to lower obligation 'assertion_0'",
            "unknown return type for function 'prophecy_loop_condition'",
            "register it in TypeEnv via prepare_context",
        ],
    ),
    (
        "prophecy_loop_break_currently_blocked",
        "loop_break_prophetic",
        &[
            "Failed to lower obligation 'assertion_0'",
            "unknown return type for function 'prophecy_loop_condition'",
            "register it in TypeEnv via prepare_context",
        ],
    ),
    (
        "prophecy_loop_continue_currently_blocked",
        "loop_continue_prophetic",
        &[
            "Failed to lower obligation 'assertion_0'",
            "unknown return type for function 'prophecy_loop_condition'",
            "register it in TypeEnv via prepare_context",
        ],
    ),
    (
        "prophecy_conditional_let_else_currently_blocked",
        "prophecy_conditional_let_else",
        &[
            "Failed to lower obligation 'assertion_0'",
            "unresolved variable `value`",
        ],
    ),
    (
        "prophecy_let_else_scrutinee_currently_blocked",
        "let_else_prophetic_scrutinee",
        &[
            "Failed to lower obligation 'assertion_0'",
            "unresolved variable `value`",
        ],
    ),
    (
        "prophecy_fn_spec_closure_currently_blocked",
        "use_prophetic_fn_as_fn_spec_closure",
        &[
            "Failed to lower obligation 'assertion_0'",
            "unknown return type for function 'g'",
            "register it in TypeEnv via prepare_context",
        ],
    ),
    (
        "prophecy_fn_spec_value_currently_blocked",
        "use_prophetic_fn_as_fn_spec",
        &[
            "application of a function value whose precondition is not modelled",
            "`g` is a local bound to `prophetic_rank`",
            "rejected rather than trusted",
        ],
    ),
    (
        "prophecy_may_resolve_currently_blocked",
        "once_flip",
        &[
            "Failed to lower obligation 'assertion_0'",
            "unsupported method `may_resolve() on type `Prophecy<bool>`",
            "method is not available in specification context",
        ],
    ),
    (
        "prophecy_resolve_mut_ref_future_currently_blocked",
        "grandfather_paradox",
        &[
            "Failed to lower obligation 'assertion_0'",
            "unsupported method `resolve() on type `Prophecy<bool>`",
            "method is not available in specification context",
        ],
    ),
    (
        "prophecy_tracked_wrapper_currently_blocked",
        "once_flip",
        &[
            "Failed to lower obligation 'assertion_0'",
            "unknown return type for function 'Prophecy::new'",
            "register it in TypeEnv via prepare_context",
        ],
    ),
    (
        "prophecy_tracked_borrow_mut_future_currently_blocked",
        "once_flip",
        &[
            "Failed to lower obligation 'assertion_0'",
            "unsupported method `borrow_mut() on type `Prophecy<bool>`",
            "method is not available in specification context",
        ],
    ),
    (
        "prophecy_mut_ref_future_currently_blocked",
        "once_flip",
        &[
            "Failed to lower obligation 'assertion_0'",
            "unknown return type for function 'future'",
            "register it in TypeEnv via prepare_context",
        ],
    ),
];

#[test]
fn prophecy_rs_port_file_is_rust_syntax() {
    let source =
        std::fs::read_to_string(prophecy_port_path()).expect("prophecy port should be readable");
    syn::parse_file(&source).expect("prophecy port should parse as ordinary Rust syntax");
}

#[test]
fn prophecy_rs_pinned_upstream_case_shapes_are_present() {
    let path = pinned_upstream_prophecy_path();
    if !path.exists() {
        eprintln!(
            "skipping pinned upstream prophecy.rs shape check; missing {}",
            path.display()
        );
        return;
    }

    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", path.display()));
    for expected in [
        "#[test] once_flip",
        "#[test] grandfather_paradox",
        "may_resolve",
        "resolve",
        "#[test] proph_dep1",
        "#[test] proph_dep2",
        "#[test] trait_not_proph_impl_proph_err",
        "#[test] trait_and_impl_both_proph_ok",
        "#[test] trait_and_impl_both_proph_err",
        "#[test] trait_proph_err",
        "#[test] trait_proph_and_impl_not_proph_ok",
        "#[test] trait_proph_and_impl_not_proph_err",
        "#[test] calls_requires_ensures",
        "#[test] decreases_clause_proof_fn_cannot_be_prophetic",
        "#[test] decreases_clause_exec_fn_cannot_be_prophetic",
        "#[test] decreases_clause_loop_cannot_be_prophetic",
        "#[test] ghost_ctor_okay_in_spec_code",
        "#[test] ghost_ctor_fail_in_tracked_code",
        "#[test] ghost_ctor_fail",
        "#[test] prophetic_decl_fail",
        "#[test] prophetic_func_fail",
        "#[test] prophetic_func_fail_ret",
        "#[test] prophetic_func_fail2",
        "#[test] proph_assign_to_proph_location_ok",
        "#[test] proph_assign_to_nonproph_location_bad",
        "#[test] proph_assign_to_nonproph_location_bad2",
        "#[test] prophecy_conditional_assign",
        "#[test] prophecy_conditional_assign_else",
        "#[test] prophecy_conditional_call",
        "#[test] prophecy_conditional_return",
        "#[test] prophecy_conditional_loop",
        "#[test] loop_condition_prophetic",
        "#[test] loop_break_prophetic",
        "#[test] loop_continue_prophetic",
        "#[test] prophecy_conditional_let_else",
        "#[test] let_else_prophetic_scrutinee",
        "#[test] conditional_short_circuit_and",
        "#[test] conditional_short_circuit_or",
        "#[test] conditional_short_circuit_implies",
        "#[test] conditional_match0",
        "#[test] conditional_match1",
        "#[test] conditional_match2",
        "#[test] conditional_match3",
        "#[test] lemma_call_ok",
        "#[test] lemma_call_propagate",
        "#[test] lemma_return_fail",
        "#[test] lemma_return_fail2",
        "#[test] conditional_expression_propagate",
        "#[test] conditional_expression_propagate1",
        "#[test] conditional_expression_propagate2",
        "#[test] decls_in_conditional",
        "#[test] use_prophetic_fn_as_fn_spec_closure",
        "#[test] use_prophetic_fn_as_fn_spec",
    ] {
        assert!(
            source.contains(expected),
            "pinned upstream prophecy.rs should still contain {expected}"
        );
    }
}

#[test]
fn prophecy_rs_expected_case_metadata_is_exact_and_schema_valid() {
    let mut actual = parse_expected_case_metadata(&port_file());
    actual.sort();

    let expected = expected_metadata_from_tests();

    assert_eq!(actual, expected);

    let mut seen_case_ids = BTreeSet::new();
    for case in &actual {
        assert!(
            seen_case_ids.insert(case.case_id.clone()),
            "duplicate metadata case_id {}",
            case.case_id
        );
        assert!(
            schema_identifier(&case.case_id),
            "{} should be a schema-valid case_id",
            case.case_id
        );
        assert!(
            schema_identifier(&case.upstream_case_id),
            "{} ({}) should be a schema-valid upstream_case_id",
            case.case_id,
            case.upstream_case_id
        );
        assert!(
            matches!(
                case.expected_verdict.as_str(),
                "verified" | "counterexample" | "error"
            ),
            "{} ({}) has non-schema evidence verdict {}",
            case.case_id,
            case.upstream_case_id,
            case.expected_verdict
        );
        assert_ne!(
            case.expected_verdict.to_ascii_lowercase(),
            "unknown",
            "{} ({}) must not inventory Unknown as evidence",
            case.case_id,
            case.upstream_case_id
        );

        match case.expected_verdict.as_str() {
            "verified" | "counterexample" => {
                assert!(
                    case.min_obligations >= 1,
                    "{} ({}) should have positive obligations for {} evidence",
                    case.case_id,
                    case.upstream_case_id,
                    case.expected_verdict
                );
                assert!(
                    case.expected_error_patterns.is_empty(),
                    "{} ({}) should not carry error fragments for {} evidence",
                    case.case_id,
                    case.upstream_case_id,
                    case.expected_verdict
                );
            }
            "error" => {
                assert_eq!(
                    case.min_obligations, 0,
                    "{} ({}) should have zero obligations for error evidence",
                    case.case_id, case.upstream_case_id
                );
                assert!(
                    !case.expected_error_patterns.is_empty(),
                    "{} ({}) should carry precise fail-closed error fragments",
                    case.case_id,
                    case.upstream_case_id
                );
            }
            _ => unreachable!("verdict schema checked above"),
        }
    }

    for required_status in ["verified", "counterexample", "error"] {
        assert!(
            actual
                .iter()
                .any(|case| case.expected_verdict == required_status),
            "metadata should include at least one {required_status} case"
        );
    }
}

#[test]
fn prophecy_rs_expected_case_metadata_matches_manifest() {
    assert_eq!(
        manifest_expected_case_metadata(),
        parse_expected_case_metadata(&port_file()),
        "prophecy manifest expected_cases should match port metadata exactly"
    );
}

#[test]
fn prophecy_rs_expected_case_metadata_names_all_port_functions() {
    let file = port_file();
    let metadata_case_ids = parse_expected_case_metadata(&file)
        .into_iter()
        .map(|case| case.case_id)
        .collect::<BTreeSet<_>>();
    assert_eq!(collect_port_function_names(&file), metadata_case_ids);
}

#[test]
fn prophecy_rs_verified_subset_verifies_from_file() {
    let path = prophecy_port_path();

    for (case, upstream_case, min_obligations) in VERIFIED_CASES {
        let (result, obligations) = verify_case(&path, case, upstream_case);
        assert!(
            matches!(result, VerifyResult::Verified),
            "{case} ({upstream_case}) should verify, got: {result:?}"
        );
        assert!(
            obligations >= *min_obligations,
            "{case} ({upstream_case}) should expose at least {min_obligations} obligations, got {obligations}"
        );
    }
}

#[test]
fn prophecy_rs_counterexample_subset_is_rejected_from_file() {
    let path = prophecy_port_path();

    for (case, upstream_case, min_obligations) in COUNTEREXAMPLE_CASES {
        let (result, obligations) = verify_case(&path, case, upstream_case);
        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "{case} ({upstream_case}) should be rejected, got: {result:?}"
        );
        assert!(
            obligations >= *min_obligations,
            "{case} ({upstream_case}) should expose at least {min_obligations} obligations, got {obligations}"
        );
    }
}

#[test]
fn prophecy_rs_unsupported_boundaries_fail_closed_from_file() {
    let path = prophecy_port_path();
    let file = port_file();
    let metadata = parse_expected_case_metadata(&file);

    for expected in metadata
        .iter()
        .filter(|case| case.expected_verdict == "error")
    {
        expect_fail_closed(&path, expected);
    }
}
