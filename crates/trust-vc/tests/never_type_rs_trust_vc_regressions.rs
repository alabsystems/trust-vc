// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Executable guards for the first upstream never_type.rs TrustVc scout slice.
//!
//! These tests intentionally do not claim full Verus never_type.rs parity. They
//! pin the currently executable `loop {}` never-expression behavior in
//! diverging let-else control flow and keep upstream-shaped match/helper `!`
//! coercions fail-closed while proof/spec-mode never values and Verus
//! diagnostic parity remain unsupported.

use std::{collections::BTreeSet, path::PathBuf};
use trust_vc_core::{verify_function_from_file, VerifyResult};

fn never_type_port_path() -> PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/ported/never_type.rs")
}

fn verus_manifest_path() -> PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/verus-tests.json")
}

const VERIFIED_CASES: &[(&str, &str)] = &[(
    "never_expression_let_else_some_path_verified",
    "coercion_in_exec direct loop fallback, reduced to let-else control flow",
)];

const COUNTEREXAMPLE_CASES: &[(&str, &str)] = &[(
    "never_expression_let_else_some_path_wrong_value_counterexample",
    "coercion_in_exec/stuff_fails direct loop fallback, reduced to let-else control flow",
)];

const FAIL_CLOSED_CASES: &[(&str, &str, &[&str])] = &[
    (
        "never_expression_match_some_arm_fails_closed",
        "coercion_in_exec/stuff direct match loop fallback",
        &["unsupported expression `loop`", "specification context"],
    ),
    (
        "never_expression_match_some_arm_wrong_value_fails_closed",
        "coercion_in_exec/stuff_fails direct match loop fallback",
        &["unsupported expression `loop`", "specification context"],
    ),
    (
        "never_returning_helper_match_arm_fails_closed",
        "coercion_in_exec/never_returns helper arm",
        &["unknown return type", "never_returns_loop"],
    ),
    (
        "never_expression_let_else_value_assert_verified",
        "coercion_in_exec value binding after direct loop fallback",
        &["unresolved variable", "value"],
    ),
    (
        "never_expression_let_else_wrong_value_counterexample",
        "coercion_in_exec/stuff_fails value binding after direct loop fallback",
        &["unresolved variable", "value"],
    ),
    (
        "never_expression_custom_option_match_helper_fails_closed",
        "coercion_in_exec upstream-shaped custom Option helper arm",
        &["unknown return type", "never_returns_loop"],
    ),
    (
        "never_value_in_assert_spec_context_fails_closed",
        "test_coercion_not_allowed_in_spec/spec never caught as assertion expression",
        &["unknown return type", "never_returns_loop"],
    ),
    (
        "never_value_in_ensures_spec_context_fails_closed",
        "test_spec_never_caught3/spec never caught as postcondition expression",
        &["unknown return type", "never_returns_loop"],
    ),
];

#[derive(Debug, Eq, PartialEq)]
struct CaseMetadata {
    case_id: String,
    upstream_case_id: String,
    expected_verdict: String,
    min_obligations: usize,
}

fn referenced_array_const(file: &syn::File, const_name: &str) -> syn::ExprArray {
    let const_item = file
        .items
        .iter()
        .find_map(|item| match item {
            syn::Item::Const(item) if item.ident == const_name => Some(item),
            _ => None,
        })
        .unwrap_or_else(|| panic!("never_type port should define {const_name}"));

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

fn metadata_entries(file: &syn::File) -> Vec<CaseMetadata> {
    let array = referenced_array_const(file, "NEVER_TYPE_RS_EXPECTED_CASES");
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
            "duplicate never_type metadata for {case_id}"
        );
        entries.push(CaseMetadata {
            case_id,
            upstream_case_id: literal_string(&tuple.elems[1]),
            expected_verdict: literal_string(&tuple.elems[2]),
            min_obligations: literal_usize(&tuple.elems[3]),
        });
    }

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
        });
    let counterexamples = COUNTEREXAMPLE_CASES
        .iter()
        .map(|(case_id, upstream_case_id)| CaseMetadata {
            case_id: (*case_id).to_string(),
            upstream_case_id: (*upstream_case_id).to_string(),
            expected_verdict: "counterexample".to_string(),
            min_obligations: 1,
        });
    let errors = FAIL_CLOSED_CASES
        .iter()
        .map(|(case_id, upstream_case_id, _)| CaseMetadata {
            case_id: (*case_id).to_string(),
            upstream_case_id: (*upstream_case_id).to_string(),
            expected_verdict: "error".to_string(),
            min_obligations: 0,
        });

    verified.chain(counterexamples).chain(errors).collect()
}

fn fail_closed_error_patterns_as_owned() -> Vec<(String, Vec<String>)> {
    FAIL_CLOSED_CASES
        .iter()
        .map(|(case, _, patterns)| {
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

fn manifest_row() -> serde_json::Value {
    let source =
        std::fs::read_to_string(verus_manifest_path()).expect("Verus manifest should be readable");
    let manifest: serde_json::Value =
        serde_json::from_str(&source).expect("Verus manifest should parse as JSON");
    manifest["entries"]
        .as_array()
        .expect("Verus manifest should contain entries")
        .iter()
        .find(|entry| {
            entry["upstream_path"].as_str() == Some("source/rust_verify_test/tests/never_type.rs")
        })
        .expect("Verus manifest should contain never_type.rs row")
        .clone()
}

fn manifest_expected_case_metadata() -> Vec<CaseMetadata> {
    manifest_row()["expected_cases"]
        .as_array()
        .expect("never_type manifest row should contain expected_cases")
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
        })
        .collect()
}

fn manifest_fail_closed_error_pattern_metadata() -> Vec<(String, Vec<String>)> {
    manifest_row()["expected_cases"]
        .as_array()
        .expect("never_type manifest row should contain expected_cases")
        .iter()
        .filter_map(|case| {
            let patterns = case["expected_error_patterns"].as_array()?;
            Some((
                case["case_id"]
                    .as_str()
                    .expect("manifest case should contain case_id")
                    .to_string(),
                patterns
                    .iter()
                    .map(|pattern| {
                        pattern
                            .as_str()
                            .expect("expected_error_patterns entries should be strings")
                            .to_string()
                    })
                    .collect(),
            ))
        })
        .collect()
}

#[test]
fn never_type_rs_expected_case_metadata_is_exact() {
    let source = std::fs::read_to_string(never_type_port_path())
        .expect("never_type port should be readable");
    let file =
        syn::parse_file(&source).expect("never_type port should parse as ordinary Rust syntax");
    assert_eq!(metadata_entries(&file), expected_metadata());
}

#[test]
fn never_type_rs_expected_case_metadata_matches_manifest() {
    assert_eq!(
        manifest_expected_case_metadata(),
        expected_metadata(),
        "never_type manifest should match the port evidence/fail-closed inventory exactly"
    );
    assert_eq!(
        manifest_fail_closed_error_pattern_metadata(),
        fail_closed_error_patterns_as_owned(),
        "never_type manifest expected_error_patterns should match focused fail-closed guards exactly"
    );
}

#[test]
fn never_type_rs_verified_subset_verifies_from_file() {
    let path = never_type_port_path();
    let path = path.to_str().expect("never_type port path should be UTF-8");

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
fn never_type_rs_counterexample_subset_is_rejected_from_file() {
    let path = never_type_port_path();
    let path = path.to_str().expect("never_type port path should be UTF-8");

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
fn never_type_rs_helper_never_coercion_fails_closed_from_file() {
    let path = never_type_port_path();
    let path = path.to_str().expect("never_type port path should be UTF-8");

    for (case, upstream_case, expected_fragments) in FAIL_CLOSED_CASES {
        let message = match verify_function_from_file(path, case) {
            Err(err) => err.to_string(),
            Ok(VerifyResult::Error { message }) => message,
            Ok(other) => {
                panic!("{case} ({upstream_case}) should fail closed with Error, got: {other:?}")
            }
        };

        for fragment in *expected_fragments {
            assert!(
                message.contains(fragment),
                "{case} ({upstream_case}) error should contain {fragment:?}, got: {message}"
            );
        }
    }
}
