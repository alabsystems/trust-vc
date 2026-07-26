// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Executable guards for the first upstream consts.rs TrustVc scout slice.
//!
//! These tests intentionally do not claim full Verus consts.rs parity. They
//! pin the currently executable constant-expression/spec-constant subset and
//! top-level scalar const reads/array lengths, plus the fail-closed static item
//! gap while the manifest remains unsupported-gap.

mod common;

use std::{
    collections::{BTreeMap, BTreeSet},
    path::{Path, PathBuf},
};
use trust_vc_core::{
    extract_verification_conditions_with_file_context, verify_function_from_file, VerifyResult,
};

fn consts_port_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/ported/consts.rs")
}

fn verus_manifest_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/verus-tests.json")
}

fn pinned_upstream_consts_path() -> PathBuf {
    common::pinned_verus_test_path("consts.rs")
}

fn verify_case_with_obligations(
    path: &Path,
    case: &str,
    upstream_case: &str,
) -> (VerifyResult, usize) {
    let source = std::fs::read_to_string(path)
        .unwrap_or_else(|err| panic!("consts port should be readable: {err}"));
    let file =
        syn::parse_file(&source).unwrap_or_else(|err| panic!("consts port should parse: {err}"));
    let func = file
        .items
        .iter()
        .find_map(|item| match item {
            syn::Item::Fn(func) if func.sig.ident == case => Some(func),
            _ => None,
        })
        .unwrap_or_else(|| panic!("{case} ({upstream_case}) should exist in consts port"));

    let vc = extract_verification_conditions_with_file_context(&file, func)
        .unwrap_or_else(|err| panic!("{case} ({upstream_case}) should extract: {err}"));
    let obligations = vc.obligations().len();
    (vc.verify(), obligations)
}

fn verify_error_message(path: &str, case: &str, upstream_case: &str) -> String {
    match verify_function_from_file(path, case) {
        Err(err) => err.to_string(),
        Ok(VerifyResult::Error { message }) => message,
        Ok(other) => {
            panic!("{case} ({upstream_case}) should fail closed with Error, got: {other:?}")
        }
    }
}

fn verify_fail_closed(path: &str, case: &str, _upstream_case: &str) -> VerifyResult {
    verify_function_from_file(path, case).unwrap_or_else(|err| VerifyResult::Error {
        message: err.to_string(),
    })
}

const VERIFIED_CASES: &[(&str, &str, usize)] = &[
    ("const_arithmetic_value_verified", "test1", 1),
    ("const_fn_return_contract_verified", "test1 const fn e", 1),
    ("spec_constant_surrogate_verified", "test1 spec const S", 1),
    ("const_array_literal_exec_index_verified", "arrays", 1),
    ("const_item_value_read_verified", "test1", 2),
    (
        "const_item_array_length_verified",
        "test_generic_const_eval2",
        2,
    ),
];

const COUNTEREXAMPLE_CASES: &[(&str, &str, usize)] = &[
    (
        "const_arithmetic_wrong_value_counterexample",
        "test1_fails1",
        1,
    ),
    (
        "const_fn_return_contract_wrong_counterexample",
        "test1 const fn e false return contract",
        1,
    ),
    (
        "spec_constant_surrogate_wrong_counterexample",
        "test1_fails1 spec const S",
        1,
    ),
    (
        "const_array_literal_wrong_value_counterexample",
        "array_incorrect_value",
        1,
    ),
    (
        "const_array_literal_out_of_bounds_counterexample",
        "array_out_of_bounds",
        1,
    ),
    (
        "const_item_value_read_wrong_counterexample",
        "test1_fails1",
        2,
    ),
];

const ERROR_CASES: &[(&str, &str, &[&str])] = &[];

const FAIL_CLOSED_CASES: &[(&str, &str, &[&str])] = &[(
    "static_item_value_read_currently_fails_closed",
    "statics_get_type_invariants",
    &[
        "unresolved variable `TOP_LEVEL_STATIC_VALUE`",
        "function parameter, let-binding, or quantifier-bound variable",
    ],
)];

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
        .unwrap_or_else(|| panic!("consts port should define {const_name}"));

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
    let array = referenced_array_const(file, "CONSTS_RS_FAIL_CLOSED_ERROR_PATTERNS");
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
    let array = referenced_array_const(file, "CONSTS_RS_EXPECTED_CASES");
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
            "duplicate consts metadata for {case_id}"
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
    let verified =
        VERIFIED_CASES.iter().map(
            |(case_id, upstream_case_id, min_obligations)| CaseMetadata {
                case_id: (*case_id).to_string(),
                upstream_case_id: (*upstream_case_id).to_string(),
                expected_verdict: "verified".to_string(),
                min_obligations: *min_obligations,
                expected_error_patterns: Vec::new(),
            },
        );
    let counterexamples =
        COUNTEREXAMPLE_CASES
            .iter()
            .map(
                |(case_id, upstream_case_id, min_obligations)| CaseMetadata {
                    case_id: (*case_id).to_string(),
                    upstream_case_id: (*upstream_case_id).to_string(),
                    expected_verdict: "counterexample".to_string(),
                    min_obligations: *min_obligations,
                    expected_error_patterns: Vec::new(),
                },
            );
    let errors = FAIL_CLOSED_CASES
        .iter()
        .map(
            |(case_id, upstream_case_id, expected_fragments)| CaseMetadata {
                case_id: (*case_id).to_string(),
                upstream_case_id: (*upstream_case_id).to_string(),
                expected_verdict: "error".to_string(),
                min_obligations: 0,
                expected_error_patterns: expected_fragments
                    .iter()
                    .map(|fragment| (*fragment).to_string())
                    .collect(),
            },
        );

    verified.chain(counterexamples).chain(errors).collect()
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
            entry["upstream_path"].as_str() == Some("source/rust_verify_test/tests/consts.rs")
        })
        .expect("Verus manifest should contain consts.rs row");

    row["expected_cases"]
        .as_array()
        .expect("consts.rs row should contain expected_cases")
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
fn consts_rs_port_file_is_rust_syntax() {
    let source =
        std::fs::read_to_string(consts_port_path()).expect("consts port should be readable");
    syn::parse_file(&source).expect("consts port should parse as ordinary Rust syntax");
}

#[test]
fn consts_rs_expected_case_metadata_is_exact() {
    let source =
        std::fs::read_to_string(consts_port_path()).expect("consts port should be readable");
    let file = syn::parse_file(&source).expect("consts port should parse as ordinary Rust syntax");
    assert_eq!(metadata_entries(&file), expected_metadata());
    assert!(
        source.contains("consts_rs_fail_closed_error_patterns"),
        "consts port should export fail-closed error-pattern metadata"
    );
}

#[test]
fn consts_rs_expected_case_metadata_matches_manifest() {
    let source =
        std::fs::read_to_string(consts_port_path()).expect("consts port should be readable");
    let file = syn::parse_file(&source).expect("consts port should parse as ordinary Rust syntax");
    assert_eq!(metadata_entries(&file), manifest_expected_metadata());
}

#[test]
fn consts_rs_pinned_upstream_case_shapes_are_present() {
    let path = pinned_upstream_consts_path();
    if !path.exists() {
        eprintln!(
            "skipping pinned upstream consts.rs shape check; missing {}",
            path.display()
        );
        return;
    }

    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", path.display()));
    for expected in [
        "#[test] test1",
        "#[test] test1_fails1",
        "#[test] test_generic_const_eval2",
        "#[test] statics_get_type_invariants",
        "#[test] arrays",
        "#[test] array_incorrect_value",
        "#[test] array_out_of_bounds",
        "const fn e()",
    ] {
        assert!(
            source.contains(expected),
            "pinned upstream consts.rs should still contain {expected}"
        );
    }
}

#[test]
fn consts_rs_verified_subset_verifies_from_file() {
    let path = consts_port_path();

    for (case, upstream_case, min_obligations) in VERIFIED_CASES {
        let (result, obligations) = verify_case_with_obligations(&path, case, upstream_case);
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
fn consts_rs_counterexample_subset_is_rejected_from_file() {
    let path = consts_port_path();

    for (case, upstream_case, min_obligations) in COUNTEREXAMPLE_CASES {
        let (result, obligations) = verify_case_with_obligations(&path, case, upstream_case);
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
fn consts_rs_error_subset_fails_closed_from_file() {
    let path = consts_port_path();
    let path = path.to_str().expect("consts port path should be UTF-8");

    for (case, upstream_case, expected_patterns) in ERROR_CASES {
        let message = verify_error_message(path, case, upstream_case);
        for expected in *expected_patterns {
            assert!(
                message.contains(expected),
                "{case} ({upstream_case}) error should contain {expected:?}, got: {message}"
            );
        }
    }
}

#[test]
fn consts_rs_top_level_const_and_static_reads_fail_closed_from_file() {
    let path = consts_port_path();
    let path = path.to_str().expect("consts port path should be UTF-8");

    for (case, upstream_case, expected_patterns) in FAIL_CLOSED_CASES {
        let result = verify_fail_closed(path, case, upstream_case);
        let message = match result {
            VerifyResult::Error { message } => message,
            other => {
                panic!("{case} ({upstream_case}) should fail closed with Error, got: {other:?}")
            }
        };
        for expected in *expected_patterns {
            assert!(
                message.contains(expected),
                "{case} ({upstream_case}) error should contain {expected:?}, got: {message}"
            );
        }
    }
}
