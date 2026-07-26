// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Executable guards for the first upstream when_used_as_spec.rs scout slice.
//!
//! These tests intentionally keep the upstream file as an unsupported gap. They
//! prove only the current TrustVc contract/spec-helper surface, a narrow
//! `allow_in_spec` marker and a narrow `when_used_as_spec` marker for direct
//! executable-helper calls in target specification clauses, while executable
//! value contexts and unmarked helpers remain fail-closed.

use std::{
    collections::BTreeMap,
    path::{Path, PathBuf},
};
use trust_vc_core::{verify_function_from_file, VerifyResult};

type ExpectedErrorPatterns = (&'static str, &'static [&'static str]);

fn when_used_as_spec_port_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/ported/when_used_as_spec.rs")
}

fn verus_manifest_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/verus-tests.json")
}

const VERIFIED_CASES: &[(&str, &str)] = &[
    (
        "when_used_as_spec_contract_call_verified",
        "test1 closest explicit contract/spec-helper surface",
    ),
    (
        "allow_in_spec_contract_call_verified",
        "allow_in_spec closest explicit executable contract surface",
    ),
    (
        "allow_in_spec_select_u64_contract_surface",
        "allow_in_spec generic true/false branch monomorphic contract surrogate",
    ),
    (
        "allow_in_spec_direct_exec_spec_term_verified",
        "allow_in_spec direct exec helper in a specification term",
    ),
    (
        "allow_in_spec_select_u64_direct_exec_spec_term_verified",
        "allow_in_spec generic branch surrogate direct exec helper in a specification term",
    ),
    (
        "when_used_as_spec_direct_exec_spec_term_verified",
        "test1 direct exec helper mapped to a spec target in a specification term",
    ),
];

const COUNTEREXAMPLE_CASES: &[(&str, &str)] = &[
    (
        "when_used_as_spec_exec_body_counterexample",
        "fail_exec_false executable result is not rewritten as the spec function",
    ),
    (
        "allow_in_spec_negate_body_counterexample",
        "allow_in_spec false executable contract body",
    ),
    (
        "allow_in_spec_select_u64_false_branch_counterexample",
        "allow_in_spec generic false-branch surrogate with wrong executable body",
    ),
];

const EXPECTED_CASES: &[(&str, &str, &str, usize)] = &[
    (
        "when_used_as_spec_contract_call_verified",
        "test1",
        "verified",
        1,
    ),
    (
        "allow_in_spec_contract_call_verified",
        "allow_in_spec",
        "verified",
        1,
    ),
    (
        "allow_in_spec_select_u64_contract_surface",
        "allow_in_spec",
        "verified",
        1,
    ),
    (
        "when_used_as_spec_exec_body_counterexample",
        "fail_exec_false",
        "counterexample",
        1,
    ),
    (
        "allow_in_spec_select_u64_false_branch_counterexample",
        "allow_in_spec",
        "counterexample",
        1,
    ),
    (
        "allow_in_spec_negate_body_counterexample",
        "allow_in_spec",
        "counterexample",
        1,
    ),
    (
        "allow_in_spec_direct_exec_spec_term_verified",
        "allow_in_spec",
        "verified",
        1,
    ),
    (
        "allow_in_spec_select_u64_direct_exec_spec_term_verified",
        "allow_in_spec",
        "verified",
        1,
    ),
    (
        "when_used_as_spec_direct_exec_spec_term_fails_closed",
        "test1",
        "error",
        0,
    ),
    (
        "when_used_as_spec_direct_exec_spec_term_verified",
        "test1",
        "verified",
        1,
    ),
    (
        "when_used_as_spec_exec_value_context_fails_closed",
        "fail_exec_false",
        "error",
        0,
    ),
];

const FAIL_CLOSED_CASES: &[(&str, &str, &str)] = &[
    (
        "when_used_as_spec_direct_exec_spec_term_fails_closed",
        "test1 unmarked direct exec helper in a specification term",
        "Unsupported call to sibling helper",
    ),
    (
        "when_used_as_spec_exec_value_context_fails_closed",
        "fail_exec_false executable value context is not rewritten as the spec function",
        "unknown return type for function 'when_used_as_spec_direct_exec_helper'",
    ),
];

const EXPECTED_ERROR_PATTERNS: &[ExpectedErrorPatterns] = &[
    (
        "when_used_as_spec_direct_exec_spec_term_fails_closed",
        &["Unsupported call to sibling helper"],
    ),
    (
        "when_used_as_spec_exec_value_context_fails_closed",
        &["unknown return type for function 'when_used_as_spec_direct_exec_helper'"],
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

fn port_file() -> syn::File {
    let source = std::fs::read_to_string(when_used_as_spec_port_path())
        .expect("when_used_as_spec port should be readable");
    syn::parse_file(&source).expect("when_used_as_spec port should parse as ordinary Rust syntax")
}

fn referenced_array_const(file: &syn::File, const_name: &str) -> syn::ExprArray {
    let const_item = file
        .items
        .iter()
        .find_map(|item| match item {
            syn::Item::Const(item) if item.ident == const_name => Some(item),
            _ => None,
        })
        .unwrap_or_else(|| panic!("when_used_as_spec port should define {const_name}"));

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

fn error_pattern_entries(file: &syn::File) -> Vec<(String, Vec<String>)> {
    let array = referenced_array_const(file, "WHEN_USED_AS_SPEC_RS_EXPECTED_ERROR_PATTERNS");
    let mut seen = BTreeMap::new();
    let mut entries = Vec::new();

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
            seen.insert(case_id.clone(), ()).is_none(),
            "duplicate error-pattern metadata for {case_id}"
        );
        entries.push((case_id, patterns));
    }

    entries
}

fn metadata_entries(file: &syn::File) -> Vec<CaseMetadata> {
    let array = referenced_array_const(file, "WHEN_USED_AS_SPEC_RS_EXPECTED_CASES");
    let mut error_patterns: BTreeMap<String, Vec<String>> =
        error_pattern_entries(file).into_iter().collect();
    let mut seen = BTreeMap::new();
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
            seen.insert(case_id.clone(), ()).is_none(),
            "duplicate when_used_as_spec metadata for {case_id}"
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
    let mut error_patterns: BTreeMap<&str, Vec<String>> = EXPECTED_ERROR_PATTERNS
        .iter()
        .map(|(case, patterns)| {
            (
                *case,
                patterns
                    .iter()
                    .map(|pattern| (*pattern).to_string())
                    .collect(),
            )
        })
        .collect();

    EXPECTED_CASES
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

fn expected_error_pattern_metadata() -> Vec<(String, Vec<String>)> {
    EXPECTED_ERROR_PATTERNS
        .iter()
        .map(|(case, patterns)| {
            (
                (*case).to_string(),
                patterns
                    .iter()
                    .map(|pattern| (*pattern).to_string())
                    .collect(),
            )
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
                == Some("source/rust_verify_test/tests/when_used_as_spec.rs")
        })
        .expect("Verus manifest should contain when_used_as_spec.rs row");

    row["expected_cases"]
        .as_array()
        .expect("when_used_as_spec.rs row should contain expected_cases")
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
fn when_used_as_spec_rs_expected_case_metadata_is_exact() {
    let source = std::fs::read_to_string(when_used_as_spec_port_path())
        .expect("when_used_as_spec port should be readable");
    let file = syn::parse_file(&source)
        .expect("when_used_as_spec port should parse as ordinary Rust syntax");
    assert_eq!(metadata_entries(&file), expected_metadata());
    assert!(
        source.contains("when_used_as_spec_rs_expected_cases")
            && source.contains("when_used_as_spec_rs_expected_error_patterns"),
        "when_used_as_spec port should export expected-case and error-pattern metadata"
    );
}

#[test]
fn when_used_as_spec_rs_expected_error_pattern_metadata_is_exact() {
    let file = port_file();
    assert_eq!(
        error_pattern_entries(&file),
        expected_error_pattern_metadata()
    );
}

#[test]
fn when_used_as_spec_rs_expected_case_metadata_matches_manifest() {
    let file = port_file();
    assert_eq!(metadata_entries(&file), manifest_expected_metadata());
}

#[test]
fn when_used_as_spec_rs_error_cases_have_expected_error_patterns() {
    let mut patterns_by_case: BTreeMap<&str, &[&str]> =
        EXPECTED_ERROR_PATTERNS.iter().copied().collect();

    for expected_case in EXPECTED_CASES {
        let (case, upstream_case, verdict, min_obligations) = *expected_case;
        if verdict == "error" {
            assert_eq!(
                min_obligations, 0,
                "{case} ({upstream_case}) error evidence should not declare obligations"
            );
            let expected_patterns = patterns_by_case.remove(case).unwrap_or_else(|| {
                panic!("{case} ({upstream_case}) should declare expected_error_patterns")
            });
            assert!(
                !expected_patterns.is_empty(),
                "{case} ({upstream_case}) should declare at least one expected_error_patterns value"
            );
            for expected_pattern in expected_patterns {
                assert!(
                    !expected_pattern.trim().is_empty(),
                    "{case} ({upstream_case}) declares an empty expected_error_patterns value"
                );
            }
        } else {
            assert!(
                !patterns_by_case.contains_key(case),
                "{case} ({upstream_case}) should not declare expected_error_patterns for {verdict} evidence"
            );
        }
    }

    assert!(
        patterns_by_case.is_empty(),
        "expected_error_patterns metadata should not contain orphan cases: {patterns_by_case:?}"
    );
}

#[test]
fn when_used_as_spec_rs_contract_surface_verifies_from_file() {
    let path = when_used_as_spec_port_path();
    let path = path
        .to_str()
        .expect("when_used_as_spec port path should be UTF-8");

    for (case, upstream_case) in VERIFIED_CASES {
        let result = verify_function_from_file(path, case)
            .unwrap_or_else(|err| panic!("{case} ({upstream_case}) should extract: {err}"));
        assert!(
            matches!(result, VerifyResult::Verified),
            "{case} ({upstream_case}) should verify, got: {result:?}"
        );
    }
}

#[test]
fn when_used_as_spec_rs_counterexample_subset_is_rejected_from_file() {
    let path = when_used_as_spec_port_path();
    let path = path
        .to_str()
        .expect("when_used_as_spec port path should be UTF-8");

    for (case, upstream_case) in COUNTEREXAMPLE_CASES {
        let result = verify_function_from_file(path, case)
            .unwrap_or_else(|err| panic!("{case} ({upstream_case}) should extract: {err}"));
        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "{case} ({upstream_case}) should be rejected, got: {result:?}"
        );
    }
}

#[test]
fn when_used_as_spec_rs_exec_helper_spec_terms_fail_closed_from_file() {
    let path = when_used_as_spec_port_path();
    let path = path
        .to_str()
        .expect("when_used_as_spec port path should be UTF-8");

    for (case, upstream_case, expected_fragment) in FAIL_CLOSED_CASES {
        let message = match verify_function_from_file(path, case) {
            Ok(VerifyResult::Error { message }) => message,
            Ok(result) => {
                panic!("{case} ({upstream_case}) should fail closed with Error, got: {result:?}")
            }
            Err(err) => err.to_string(),
        };

        assert!(
            message.contains(expected_fragment),
            "{case} ({upstream_case}) error should contain {expected_fragment:?}, got: {message}"
        );
    }
}
