// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Executable guards for the current upstream seqs.rs scout slice.
//!
//! These tests do not claim full Verus seq parity. They prove the current
//! len/index/update/push/subrange/extensionality-adjacent subset, named-source
//! to_set/source-contains equivalence, `Seq::new(len, generator)`, small
//! filter-to-set cases, and small filter subset while documenting fail-closed
//! Seq boundaries. Solver
//! `Unknown` is rejected as unsupported-gap evidence.

mod common;

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};
use trust_vc_core::{
    extract_verification_conditions_with_file_context, verify_function_from_file, VerifyResult,
};

type ExpectedCase = (&'static str, &'static str, &'static str, usize);

const EXPECTED_CASES: &[ExpectedCase] = &[
    (
        "test1_empty_and_single_push_len_exact_subset",
        "test1",
        "verified",
        1,
    ),
    ("test1_finite_push_len_and_index", "test1", "verified", 1),
    ("test1_push_index_last_element", "test1", "verified", 1),
    (
        "test1_push_extensional_adjacent_exact_subset",
        "test1",
        "verified",
        1,
    ),
    ("test1_seq_map_index", "test1", "verified", 1),
    ("test1_bool_and_repeat_literals", "test1", "verified", 1),
    ("test1_seq_to_set_contains", "test1", "verified", 1),
    (
        "test1_seq_to_set_contains_matches_source_contains",
        "test1",
        "verified",
        1,
    ),
    (
        "test1_seq_to_set_contains_matches_source_contains_variable",
        "test1",
        "verified",
        1,
    ),
    ("test1_subrange_add_len", "test1", "verified", 1),
    (
        "test1_seq_new_generator_exact_subset",
        "test1",
        "verified",
        1,
    ),
    (
        "test1_update_len_and_indices_exact_subset",
        "test1",
        "verified",
        1,
    ),
    (
        "test1_update_extensional_adjacent_exact_subset",
        "test1",
        "verified",
        1,
    ),
    (
        "test1_subrange_empty_and_zero_offset_exact_subset",
        "test1",
        "verified",
        1,
    ),
    (
        "test1_subrange_extensional_adjacent_exact_subset",
        "test1",
        "verified",
        1,
    ),
    (
        "test1_subrange_indices_and_add_exact_subset",
        "test1",
        "verified",
        1,
    ),
    (
        "test1_seq_to_set_three_element_membership_exact_subset",
        "test1",
        "verified",
        1,
    ),
    (
        "test1_seq_to_set_five_element_membership_exact_subset",
        "test1",
        "verified",
        1,
    ),
    (
        "test1_seq_to_set_finite_exact_subset",
        "test1",
        "verified",
        1,
    ),
    (
        "filter_lemmas_length_bound_exact_subset",
        "filter_lemmas",
        "verified",
        1,
    ),
    (
        "filter_lemmas_small_retained_membership_exact_subset",
        "filter_lemmas",
        "verified",
        1,
    ),
    (
        "filter_lemmas_small_len_and_index_exact_subset",
        "filter_lemmas",
        "verified",
        1,
    ),
    (
        "filter_lemmas_small_drop_then_pack_exact_subset",
        "filter_lemmas",
        "verified",
        1,
    ),
    (
        "filter_lemmas_small_all_retained_indices_exact_subset",
        "filter_lemmas",
        "verified",
        1,
    ),
    (
        "filter_lemmas_small_all_excluded_len_exact_subset",
        "filter_lemmas",
        "verified",
        1,
    ),
    (
        "filter_lemmas_small_filter_to_set_retained_membership_exact_subset",
        "filter_lemmas",
        "verified",
        1,
    ),
    (
        "filter_lemmas_add_then_push_last_index_exact_subset",
        "filter_lemmas",
        "verified",
        1,
    ),
    (
        "auto_extensionality_syntax1",
        "auto_extensionality_syntax1",
        "verified",
        1,
    ),
    (
        "auto_extensionality_syntax2",
        "auto_extensionality_syntax2",
        "verified",
        1,
    ),
    (
        "test1_subrange_wrong_index_counterexample",
        "test1",
        "counterexample",
        1,
    ),
    (
        "test1_seq_new_wrong_index_counterexample",
        "test1",
        "counterexample",
        1,
    ),
    (
        "test1_update_wrong_value_counterexample",
        "test1",
        "counterexample",
        1,
    ),
    (
        "test1_update_wrong_len_counterexample",
        "test1",
        "counterexample",
        1,
    ),
    (
        "test1_push_wrong_len_counterexample",
        "test1",
        "counterexample",
        1,
    ),
    (
        "test1_extensional_wrong_length_counterexample",
        "test1",
        "counterexample",
        1,
    ),
    (
        "test1_extensional_wrong_value_counterexample",
        "test1",
        "counterexample",
        1,
    ),
    (
        "test1_seq_to_set_five_element_absent_member_counterexample",
        "test1",
        "counterexample",
        1,
    ),
    (
        "test1_seq_to_set_absent_member_counterexample",
        "test1",
        "counterexample",
        1,
    ),
    (
        "test1_subrange_to_set_absent_member_counterexample",
        "test1",
        "counterexample",
        1,
    ),
    ("test1_fails1", "test1_fails1", "counterexample", 1),
    (
        "test1_push_index_wrong_value_fails",
        "test1_fails1",
        "counterexample",
        1,
    ),
    ("test1_fails2", "test1_fails2", "counterexample", 1),
    (
        "seq_flat_map_binder_dependent_take_currently_blocked",
        "broader vstd::Seq::flat_map",
        "error",
        0,
    ),
    (
        "seq_fold_left_collection_accumulator_currently_blocked",
        "broader vstd::Seq::fold_left",
        "error",
        0,
    ),
    (
        "seq_empty_macro_type_inference_currently_blocked",
        "broader vstd::seq! empty literal",
        "error",
        0,
    ),
];

const ERROR_CASES: &[(&str, &str, &[&str])] = &[
    (
        "seq_flat_map_binder_dependent_take_currently_blocked",
        "broader vstd::Seq::flat_map",
        &["Seq::flat_map currently supports binder-dependent bodies"],
    ),
    (
        "seq_fold_left_collection_accumulator_currently_blocked",
        "broader vstd::Seq::fold_left",
        &["Seq::fold_left currently supports non-collection accumulator/result types only"],
    ),
    (
        "seq_empty_macro_type_inference_currently_blocked",
        "broader vstd::seq! empty literal",
        &["seq![] requires an element type"],
    ),
];

fn seqs_port_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/ported/seqs.rs")
}

fn verus_manifest_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/verus-tests.json")
}

fn pinned_upstream_seqs_path() -> PathBuf {
    common::pinned_verus_test_path("seqs.rs")
}

fn port_source_and_ast() -> (String, syn::File) {
    let source = std::fs::read_to_string(seqs_port_path()).expect("seqs port should be readable");
    let ast = syn::parse_file(&source).expect("seqs port should parse as ordinary Rust syntax");
    (source, ast)
}

fn find_port_function<'a>(ast: &'a syn::File, case: &str, upstream_case: &str) -> &'a syn::ItemFn {
    ast.items
        .iter()
        .find_map(|item| match item {
            syn::Item::Fn(function) if function.sig.ident == case => Some(function),
            _ => None,
        })
        .unwrap_or_else(|| panic!("{case} ({upstream_case}) should exist in seqs port"))
}

fn verify_case(path: &Path, case: &str, upstream_case: &str) -> (VerifyResult, usize) {
    let path = path.to_str().expect("seqs port path should be UTF-8");
    let result = verify_function_from_file(path, case)
        .unwrap_or_else(|err| panic!("{case} ({upstream_case}) should extract: {err}"));

    if let VerifyResult::Unknown { reason, .. } = &result {
        panic!("{case} ({upstream_case}) returned solver Unknown, which is not stable evidence: {reason}");
    }

    let (_source, ast) = port_source_and_ast();
    let function = find_port_function(&ast, case, upstream_case);
    let vc = extract_verification_conditions_with_file_context(&ast, function)
        .unwrap_or_else(|err| panic!("{case} ({upstream_case}) should extract VCs: {err}"));

    (result, vc.obligations().len())
}

fn expect_error_contains_any(path: &Path, case: &str, upstream_case: &str, expected: &[&str]) {
    let path = path.to_str().expect("seqs port path should be UTF-8");
    let message = match verify_function_from_file(path, case) {
        Err(err) => err.to_string(),
        Ok(VerifyResult::Error { message }) => message,
        Ok(VerifyResult::Unknown { reason, .. }) => {
            panic!("{case} ({upstream_case}) returned solver Unknown, which is not stable fail-closed evidence: {reason}")
        }
        Ok(other) => {
            panic!("{case} ({upstream_case}) should fail closed with Error, got: {other:?}")
        }
    };

    assert!(
        expected.iter().any(|needle| message.contains(needle)),
        "{case} ({upstream_case}) error should contain one of {expected:?}, got: {message}"
    );
}

fn literal_string(expr: &syn::Expr) -> String {
    match expr {
        syn::Expr::Lit(syn::ExprLit {
            lit: syn::Lit::Str(lit),
            ..
        }) => lit.value(),
        _ => panic!("expected string literal in seqs metadata"),
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
        _ => panic!("expected integer literal in seqs metadata"),
    }
}

fn parse_expected_cases_from_source(source: &str) -> Vec<(String, String, String, usize)> {
    let ast = syn::parse_file(source).expect("seqs port should parse");
    let item = ast
        .items
        .iter()
        .find_map(|item| match item {
            syn::Item::Const(item) if item.ident == "SEQS_RS_EXPECTED_CASES" => Some(item),
            _ => None,
        })
        .expect("seqs port should define SEQS_RS_EXPECTED_CASES");

    let array = match item.expr.as_ref() {
        syn::Expr::Reference(reference) => match reference.expr.as_ref() {
            syn::Expr::Array(array) => array,
            _ => panic!("SEQS_RS_EXPECTED_CASES should reference an array literal"),
        },
        _ => panic!("SEQS_RS_EXPECTED_CASES should be a referenced array literal"),
    };

    array
        .elems
        .iter()
        .map(|elem| match elem {
            syn::Expr::Tuple(tuple) if tuple.elems.len() == 4 => (
                literal_string(&tuple.elems[0]),
                literal_string(&tuple.elems[1]),
                literal_string(&tuple.elems[2]),
                literal_usize(&tuple.elems[3]),
            ),
            _ => panic!("seqs metadata entries should be four-tuples"),
        })
        .collect()
}

fn expected_cases_as_owned() -> Vec<(String, String, String, usize)> {
    EXPECTED_CASES
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

fn error_pattern_metadata() -> BTreeMap<String, Vec<String>> {
    ERROR_CASES
        .iter()
        .map(|(case, _, expected_fragments)| {
            (
                (*case).to_string(),
                expected_fragments
                    .iter()
                    .map(|fragment| (*fragment).to_string())
                    .collect(),
            )
        })
        .collect()
}

fn attach_error_patterns(
    cases: Vec<(String, String, String, usize)>,
) -> Vec<(String, String, String, usize, Vec<String>)> {
    let patterns = error_pattern_metadata();
    cases
        .into_iter()
        .map(|(case, upstream_case, status, min_obligations)| {
            let expected_patterns = patterns.get(&case).cloned().unwrap_or_default();
            (
                case,
                upstream_case,
                status,
                min_obligations,
                expected_patterns,
            )
        })
        .collect()
}

fn manifest_expected_case_metadata() -> Vec<(String, String, String, usize, Vec<String>)> {
    let source =
        std::fs::read_to_string(verus_manifest_path()).expect("Verus manifest should be readable");
    let manifest: serde_json::Value =
        serde_json::from_str(&source).expect("Verus manifest should parse as JSON");
    let row = manifest["entries"]
        .as_array()
        .expect("Verus manifest should contain entries")
        .iter()
        .find(|entry| {
            entry["upstream_path"].as_str() == Some("source/rust_verify_test/tests/seqs.rs")
        })
        .expect("Verus manifest should contain seqs.rs row");

    row["expected_cases"]
        .as_array()
        .expect("seqs manifest row should contain expected_cases")
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
                case["expected_error_patterns"]
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
            )
        })
        .collect()
}

#[test]
fn seqs_rs_port_file_is_parseable_rust_syntax() {
    let (_source, _ast) = port_source_and_ast();
}

#[test]
fn seqs_rs_pinned_upstream_case_shapes_are_present() {
    let path = pinned_upstream_seqs_path();
    if !path.exists() {
        eprintln!(
            "skipping pinned upstream seqs.rs shape check; missing {}",
            path.display()
        );
        return;
    }

    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", path.display()));
    for expected in [
        "#[test] test1 verus_code!",
        "let s1 = Seq::new(5, |i: int| 10 * i);",
        "assert(s1 =~= s2);",
        "assert(s1 === s2);",
        "let s3 = s2.subrange(1, 4);",
        "let s6 = s4.map(|i: int, a: int| 2 * i + a);",
        "seq_to_set_is_finite(s1);",
        "#[test] auto_extensionality_syntax1",
        "#[test] auto_extensionality_syntax2",
        "#[test] filter_lemmas",
        "assert(forall|i: nat| i < s2.len() ==> s2[i as int] < 40);",
        "assert((s1 + s3).filter(|x: int| x < 40) == (s2 + s4));",
        "assert((s2 + s4).push(120) == s2 + s4.push(120));",
    ] {
        assert!(
            source.contains(expected),
            "pinned upstream seqs.rs should still contain {expected}"
        );
    }
}

#[test]
fn seqs_rs_expected_case_metadata_is_exact_and_schema_valid() {
    let (source, ast) = port_source_and_ast();
    assert!(
        source.contains("pub fn seqs_rs_expected_cases"),
        "seqs port should expose expected-case metadata"
    );
    assert_eq!(
        parse_expected_cases_from_source(&source),
        expected_cases_as_owned()
    );

    let function_names = ast
        .items
        .iter()
        .filter_map(|item| match item {
            syn::Item::Fn(function) => Some(function.sig.ident.to_string()),
            _ => None,
        })
        .collect::<BTreeSet<_>>();
    let mut case_names = BTreeSet::new();
    for (case, _upstream_case, status, _min_obligations) in EXPECTED_CASES {
        assert!(
            case_names.insert(*case),
            "seqs metadata should not duplicate case id {case}"
        );
        assert!(
            matches!(*status, "verified" | "counterexample" | "error"),
            "{case} should use a schema-valid status, got {status}"
        );
        assert_ne!(*status, "unknown", "{case} must not use Unknown evidence");
        assert!(
            function_names.contains(*case),
            "seqs metadata case {case} should have a matching function"
        );
    }

    let metadata_error_cases = EXPECTED_CASES
        .iter()
        .filter_map(|(case, upstream_case, status, _)| {
            (*status == "error").then_some((*case, *upstream_case))
        })
        .collect::<Vec<_>>();
    let error_pattern_cases = ERROR_CASES
        .iter()
        .map(|(case, upstream_case, _)| (*case, *upstream_case))
        .collect::<Vec<_>>();
    assert_eq!(metadata_error_cases, error_pattern_cases);
    for (case, upstream_case, status, min_obligations) in EXPECTED_CASES {
        if *status == "error" {
            assert_eq!(
                *min_obligations, 0,
                "{case} ({upstream_case}) error metadata should not count obligations"
            );
        } else {
            assert!(
                *min_obligations > 0,
                "{case} ({upstream_case}) {status} metadata should require obligations"
            );
        }
    }
}

#[test]
fn seqs_rs_expected_case_metadata_matches_manifest() {
    let (source, _ast) = port_source_and_ast();

    assert_eq!(
        manifest_expected_case_metadata(),
        attach_error_patterns(parse_expected_cases_from_source(&source)),
        "seqs manifest expected_cases should match port metadata and fail-closed patterns exactly"
    );
}

#[test]
fn seqs_rs_verified_expected_cases_verify_from_file() {
    let path = seqs_port_path();

    for (case, upstream_case, _status, min_obligations) in EXPECTED_CASES
        .iter()
        .filter(|(_case, _upstream_case, status, _)| *status == "verified")
    {
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
fn seqs_rs_counterexample_expected_cases_reject_wrong_claims_from_file() {
    let path = seqs_port_path();

    for (case, upstream_case, _status, min_obligations) in EXPECTED_CASES
        .iter()
        .filter(|(_case, _upstream_case, status, _)| *status == "counterexample")
    {
        let (result, obligations) = verify_case(&path, case, upstream_case);
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
fn seqs_rs_unsupported_seq_boundaries_fail_closed_with_errors_from_file() {
    let path = seqs_port_path();

    for (case, upstream_case, expected_fragments) in ERROR_CASES {
        expect_error_contains_any(&path, case, upstream_case, expected_fragments);
    }
}
