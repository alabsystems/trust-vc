// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Executable guards for the first upstream contrib.rs TrustVc scout slice.
//!
//! These tests intentionally keep `source/rust_verify_test/tests/contrib.rs`
//! classified as an unsupported gap. They prove only a manual spec/helper
//! contract shape comparable to `vstd::contrib::auto_spec`, a generated-helper
//! chain surrogate, false executable bodies, and current fail-closed boundaries
//! for using an exec helper as a spec term and mutating through `&mut`.

use std::{
    collections::{BTreeMap, BTreeSet},
    path::PathBuf,
};
use trust_vc_core::{verify_function_from_file, VerifyResult};

fn contrib_port_path() -> PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/ported/contrib.rs")
}

fn verus_manifest_path() -> PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/verus-tests.json")
}

const VERIFIED_CASES: &[(&str, &str)] = &[
    (
        "contrib_auto_spec_manual_contract_verified",
        "test_auto_spec::f manual generated-spec wrapper",
    ),
    (
        "contrib_auto_spec_u32_add_fixup_verified",
        "test_auto_spec::f u32 add generated-spec wrapper",
    ),
    (
        "contrib_auto_spec_helper_chain_verified",
        "test_auto_spec::f2 generated helper chain",
    ),
];

const COUNTEREXAMPLE_CASES: &[(&str, &str)] = &[
    (
        "contrib_auto_spec_manual_contract_counterexample",
        "test_auto_spec false generated-spec wrapper body",
    ),
    (
        "contrib_auto_spec_helper_chain_counterexample",
        "test_auto_spec false generated helper-chain body",
    ),
];

const FAIL_CLOSED_CASES: &[(&str, &str, &[&str])] = &[
    (
        "contrib_auto_spec_exec_call_in_contract_fails_closed",
        "test_auto_spec executable auto_spec function used as spec term",
        &["Unsupported call to sibling helper"],
    ),
    (
        "contrib_auto_spec_mut_ref_body_fails_closed",
        "test_auto_spec_unsupported_body",
        &["dereference expressions are not supported in verification syntax"],
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
        .unwrap_or_else(|| panic!("contrib port should define {const_name}"));

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
    let array = referenced_array_const(file, "CONTRIB_RS_FAIL_CLOSED_ERROR_PATTERNS");
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
    let array = referenced_array_const(file, "CONTRIB_RS_EXPECTED_CASES");
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
            "duplicate contrib metadata for {case_id}"
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
    let verified = VERIFIED_CASES
        .iter()
        .map(|(case_id, upstream_case_id)| CaseMetadata {
            case_id: (*case_id).to_string(),
            upstream_case_id: (*upstream_case_id).to_string(),
            expected_verdict: "verified".to_string(),
            min_obligations: 1,
            expected_error_patterns: Vec::new(),
        });
    let counterexamples = COUNTEREXAMPLE_CASES
        .iter()
        .map(|(case_id, upstream_case_id)| CaseMetadata {
            case_id: (*case_id).to_string(),
            upstream_case_id: (*upstream_case_id).to_string(),
            expected_verdict: "counterexample".to_string(),
            min_obligations: 1,
            expected_error_patterns: Vec::new(),
        });
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
            entry["upstream_path"].as_str() == Some("source/rust_verify_test/tests/contrib.rs")
        })
        .expect("Verus manifest should contain contrib.rs row");

    row["expected_cases"]
        .as_array()
        .expect("contrib.rs row should contain expected_cases")
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
fn contrib_rs_expected_case_metadata_is_exact() {
    let source =
        std::fs::read_to_string(contrib_port_path()).expect("contrib port should be readable");
    let file = syn::parse_file(&source).expect("contrib port should parse as ordinary Rust syntax");
    assert_eq!(metadata_entries(&file), expected_metadata());
    assert!(
        source.contains("contrib_rs_fail_closed_error_patterns"),
        "contrib port should export fail-closed error-pattern metadata"
    );
}

#[test]
fn contrib_rs_expected_case_metadata_matches_manifest() {
    let source =
        std::fs::read_to_string(contrib_port_path()).expect("contrib port should be readable");
    let file = syn::parse_file(&source).expect("contrib port should parse as ordinary Rust syntax");
    assert_eq!(metadata_entries(&file), manifest_expected_metadata());
}

fn verify_case(path: &str, case: &str, upstream_case: &str) -> VerifyResult {
    verify_function_from_file(path, case)
        .unwrap_or_else(|err| panic!("{case} ({upstream_case}) should extract: {err}"))
}

fn fail_closed_message(path: &str, case: &str, upstream_case: &str) -> String {
    match verify_function_from_file(path, case) {
        Err(err) => err.to_string(),
        Ok(VerifyResult::Error { message }) => message,
        Ok(other) => {
            panic!("{case} ({upstream_case}) should fail closed with Error, got: {other:?}")
        }
    }
}

#[test]
fn contrib_rs_verified_subset_verifies_from_file() {
    let path = contrib_port_path();
    let path = path.to_str().expect("contrib port path should be UTF-8");

    for (case, upstream_case) in VERIFIED_CASES {
        let result = verify_case(path, case, upstream_case);
        assert!(
            matches!(result, VerifyResult::Verified),
            "{case} ({upstream_case}) should verify, got: {result:?}"
        );
    }
}

#[test]
fn contrib_rs_counterexample_subset_is_rejected_from_file() {
    let path = contrib_port_path();
    let path = path.to_str().expect("contrib port path should be UTF-8");

    for (case, upstream_case) in COUNTEREXAMPLE_CASES {
        let result = verify_case(path, case, upstream_case);
        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "{case} ({upstream_case}) should be rejected, got: {result:?}"
        );
    }
}

#[test]
fn contrib_rs_unsupported_boundaries_fail_closed_from_file() {
    let path = contrib_port_path();
    let path = path.to_str().expect("contrib port path should be UTF-8");

    for (case, upstream_case, expected_fragments) in FAIL_CLOSED_CASES {
        let message = fail_closed_message(path, case, upstream_case);

        for expected_fragment in *expected_fragments {
            assert!(
                message.contains(expected_fragment),
                "{case} ({upstream_case}) error should contain {expected_fragment:?}, got: {message}"
            );
        }
    }
}
