// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Executable guards for the first upstream async_functions.rs TrustVc scout slice.
//!
//! These tests intentionally do not claim full Verus async_functions.rs parity.
//! They pin Rust-valid async result-contract witnesses, wrong-result
//! counterexamples, and the fail-closed `.await` boundary while the manifest
//! keeps `source/rust_verify_test/tests/async_functions.rs` as `unsupported-gap`.

use std::{
    collections::{BTreeMap, BTreeSet},
    path::PathBuf,
};
use trust_vc_core::{verify_function_from_file, VerifyResult};

fn async_functions_port_path() -> PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../evals/verus/ported/async_functions.rs")
}

fn verus_manifest_path() -> PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/verus-tests.json")
}

fn verify_case(path: &str, case: &str, upstream_case: &str) -> VerifyResult {
    verify_function_from_file(path, case)
        .unwrap_or_else(|err| panic!("{case} ({upstream_case}) should extract: {err}"))
}

fn verify_fail_closed(path: &str, case: &str) -> VerifyResult {
    verify_function_from_file(path, case).unwrap_or_else(|err| VerifyResult::Error {
        message: err.to_string(),
    })
}

const VERIFIED_CASES: &[(&str, &str)] = &[
    (
        "async_basic_result_verified",
        "test_basic_async_function_ensures_pass",
    ),
    (
        "async_external_spec_bool_contract_surrogate_verified",
        "test_async_function_external_specification bool contract surrogate",
    ),
];

const COUNTEREXAMPLE_CASES: &[(&str, &str)] = &[
    (
        "async_basic_wrong_result_counterexample",
        "test_basic_async_function_ensures_fail",
    ),
    (
        "async_external_spec_bool_contract_wrong_counterexample",
        "test_async_function_external_specification wrong bool body",
    ),
];

const FAIL_CLOSED_CASES: &[(&str, &str, &str)] = &[(
    "async_await_boundary_currently_blocked",
    "test_basic_async_function_and_await",
    "await",
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
        .unwrap_or_else(|| panic!("async_functions port should define {const_name}"));

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
    let array = referenced_array_const(file, "ASYNC_FUNCTIONS_RS_FAIL_CLOSED_ERROR_PATTERNS");
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
    let array = referenced_array_const(file, "ASYNC_FUNCTIONS_RS_EXPECTED_CASES");
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
            "duplicate async_functions metadata for {case_id}"
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
            case_id: VERIFIED_CASES[0].0.to_string(),
            upstream_case_id: VERIFIED_CASES[0].1.to_string(),
            expected_verdict: "verified".to_string(),
            min_obligations: 1,
            expected_error_patterns: Vec::new(),
        },
        CaseMetadata {
            case_id: COUNTEREXAMPLE_CASES[0].0.to_string(),
            upstream_case_id: COUNTEREXAMPLE_CASES[0].1.to_string(),
            expected_verdict: "counterexample".to_string(),
            min_obligations: 1,
            expected_error_patterns: Vec::new(),
        },
        CaseMetadata {
            case_id: VERIFIED_CASES[1].0.to_string(),
            upstream_case_id: VERIFIED_CASES[1].1.to_string(),
            expected_verdict: "verified".to_string(),
            min_obligations: 1,
            expected_error_patterns: Vec::new(),
        },
        CaseMetadata {
            case_id: COUNTEREXAMPLE_CASES[1].0.to_string(),
            upstream_case_id: COUNTEREXAMPLE_CASES[1].1.to_string(),
            expected_verdict: "counterexample".to_string(),
            min_obligations: 1,
            expected_error_patterns: Vec::new(),
        },
        CaseMetadata {
            case_id: FAIL_CLOSED_CASES[0].0.to_string(),
            upstream_case_id: FAIL_CLOSED_CASES[0].1.to_string(),
            expected_verdict: "error".to_string(),
            min_obligations: 0,
            expected_error_patterns: vec![FAIL_CLOSED_CASES[0].2.to_string()],
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
                == Some("source/rust_verify_test/tests/async_functions.rs")
        })
        .expect("Verus manifest should contain async_functions.rs row");

    row["expected_cases"]
        .as_array()
        .expect("async_functions.rs row should contain expected_cases")
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
fn async_functions_rs_expected_case_metadata_is_exact() {
    let source = std::fs::read_to_string(async_functions_port_path())
        .expect("async_functions port should be readable");
    let file = syn::parse_file(&source)
        .expect("async_functions port should parse as ordinary Rust syntax");
    assert_eq!(metadata_entries(&file), expected_metadata());
    assert!(
        source.contains("async_functions_rs_fail_closed_error_patterns"),
        "async_functions port should export fail-closed error-pattern metadata"
    );
}

#[test]
fn async_functions_rs_expected_case_metadata_matches_manifest() {
    let source = std::fs::read_to_string(async_functions_port_path())
        .expect("async_functions port should be readable");
    let file = syn::parse_file(&source)
        .expect("async_functions port should parse as ordinary Rust syntax");
    assert_eq!(metadata_entries(&file), manifest_expected_metadata());
}

#[test]
fn async_functions_rs_port_file_is_rust_syntax() {
    let source = std::fs::read_to_string(async_functions_port_path())
        .expect("async_functions port should be readable");
    syn::parse_file(&source).expect("async_functions port should parse as ordinary Rust syntax");
}

#[test]
fn async_functions_rs_verified_subset_verifies_from_file() {
    let path = async_functions_port_path();
    let path = path
        .to_str()
        .expect("async_functions port path should be UTF-8");

    for (case, upstream_case) in VERIFIED_CASES {
        let result = verify_case(path, case, upstream_case);
        assert!(
            matches!(result, VerifyResult::Verified),
            "{case} ({upstream_case}) should verify, got: {result:?}"
        );
    }
}

#[test]
fn async_functions_rs_counterexample_subset_is_rejected_from_file() {
    let path = async_functions_port_path();
    let path = path
        .to_str()
        .expect("async_functions port path should be UTF-8");

    for (case, upstream_case) in COUNTEREXAMPLE_CASES {
        let result = verify_case(path, case, upstream_case);
        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "{case} ({upstream_case}) should be rejected, got: {result:?}"
        );
    }
}

#[test]
fn async_functions_rs_await_boundary_fails_closed_from_file() {
    let path = async_functions_port_path();
    let path = path
        .to_str()
        .expect("async_functions port path should be UTF-8");

    for (case, upstream_case, expected_message) in FAIL_CLOSED_CASES {
        let result = verify_fail_closed(path, case);
        let message = match result {
            VerifyResult::Error { message } => message,
            other => {
                panic!("{case} ({upstream_case}) should fail closed with Error, got: {other:?}")
            }
        };
        assert!(
            message.contains(expected_message),
            "{case} ({upstream_case}) should report {expected_message:?}, got: {message}"
        );
    }
}
