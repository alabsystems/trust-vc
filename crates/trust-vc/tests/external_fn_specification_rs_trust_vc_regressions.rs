// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Executable guards for the first upstream external_fn_specification.rs scout.
//!
//! These tests intentionally keep the upstream file as an unsupported gap. They
//! prove the Rust-valid same-crate external-function contract slice, reject
//! failing requires/ensures uses, exercise a file-local `external_spec!`
//! declaration, and pin unsupported proxy/lookup shapes as closed errors.

mod common;

use std::{
    collections::{BTreeMap, BTreeSet},
    path::PathBuf,
};
use trust_vc_core::verification_bridge::VerificationPipeline;
use trust_vc_core::{
    register_extern_spec_from_manifest_scope_for_call, verify_function_from_file, VerifyResult,
};

fn external_fn_specification_port_path() -> PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../evals/verus/ported/external_fn_specification.rs")
}

fn verus_manifest_path() -> PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/verus-tests.json")
}

const VERIFIED_CASES: &[(&str, &str)] = &[
    (
        "external_fn_spec_same_crate_call_verified",
        "test_basics::test1",
    ),
    (
        "external_fn_spec_same_crate_requires_forwarded_verified",
        "test_basics::test1 caller precondition forwarding",
    ),
    (
        "external_fn_spec_returns_clause_verified",
        "test_allow_in_spec returns-clause contract surrogate",
    ),
];

const COUNTEREXAMPLE_CASES: &[(&str, &str)] = &[
    (
        "external_fn_spec_requires_violation_counterexample",
        "test_basics::test2",
    ),
    (
        "external_fn_spec_postcondition_use_counterexample",
        "test_basics::test3",
    ),
    (
        "external_fn_spec_returns_clause_counterexample",
        "test_allow_in_spec wrong returns-clause use",
    ),
];

const FAIL_CLOSED_CASES: &[(&str, &str, &[&str])] = &[(
    "external_fn_spec_proxy_contract_call_fails_closed",
    "test_call_proxy / proxy specification surface",
    &["Unsupported call to sibling helper"],
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
        .unwrap_or_else(|| panic!("external_fn_specification port should define {const_name}"));

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
    let array =
        referenced_array_const(file, "EXTERNAL_FN_SPECIFICATION_RS_EXPECTED_ERROR_PATTERNS");
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
    let array = referenced_array_const(file, "EXTERNAL_FN_SPECIFICATION_RS_EXPECTED_CASES");
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
            "duplicate external_fn_specification metadata for {case_id}"
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
    let errors =
        FAIL_CLOSED_CASES
            .iter()
            .map(
                |(case_id, upstream_case_id, expected_error_patterns)| CaseMetadata {
                    case_id: (*case_id).to_string(),
                    upstream_case_id: (*upstream_case_id).to_string(),
                    expected_verdict: "error".to_string(),
                    min_obligations: 0,
                    expected_error_patterns: expected_error_patterns
                        .iter()
                        .map(|pattern| (*pattern).to_string())
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
            entry["upstream_path"].as_str()
                == Some("source/rust_verify_test/tests/external_fn_specification.rs")
        })
        .expect("Verus manifest should contain external_fn_specification.rs row");

    row["expected_cases"]
        .as_array()
        .expect("external_fn_specification.rs row should contain expected_cases")
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

fn external_fn_specification_port_path_str() -> String {
    external_fn_specification_port_path()
        .to_str()
        .expect("external_fn_specification port path should be UTF-8")
        .to_owned()
}

fn register_u8_default_external_spec_from_port(result_var: &str) {
    let path = external_fn_specification_port_path_str();
    register_extern_spec_from_manifest_scope_for_call(
        &path,
        env!("CARGO_MANIFEST_DIR"),
        "u8::default",
        "u8::default()",
        Some(result_var),
    )
    .unwrap_or_else(|err| panic!("u8::default external_spec should register from port: {err}"));
}

#[test]
fn external_fn_specification_rs_expected_case_metadata_is_exact() {
    let source = std::fs::read_to_string(external_fn_specification_port_path())
        .expect("external_fn_specification port should be readable");
    let file = syn::parse_file(&source)
        .expect("external_fn_specification port should parse as ordinary Rust syntax");
    assert_eq!(metadata_entries(&file), expected_metadata());
}

#[test]
fn external_fn_specification_rs_expected_case_metadata_matches_manifest() {
    let source = std::fs::read_to_string(external_fn_specification_port_path())
        .expect("external_fn_specification port should be readable");
    let file = syn::parse_file(&source)
        .expect("external_fn_specification port should parse as ordinary Rust syntax");
    assert_eq!(metadata_entries(&file), manifest_expected_metadata());
}

#[test]
fn external_fn_specification_rs_verified_subset_verifies_from_file() {
    let path = external_fn_specification_port_path();
    let path = path
        .to_str()
        .expect("external_fn_specification port path should be UTF-8");

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
fn external_fn_specification_rs_counterexamples_are_rejected_from_file() {
    let path = external_fn_specification_port_path();
    let path = path
        .to_str()
        .expect("external_fn_specification port path should be UTF-8");

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
fn external_fn_specification_rs_proxy_contract_fails_closed_from_file() {
    let path = external_fn_specification_port_path();
    let path = path
        .to_str()
        .expect("external_fn_specification port path should be UTF-8");

    for (case, upstream_case, expected_fragments) in FAIL_CLOSED_CASES {
        let message = match verify_function_from_file(path, case) {
            Ok(VerifyResult::Error { message }) => message,
            Ok(result) => {
                panic!("{case} ({upstream_case}) should fail closed with Error, got: {result:?}")
            }
            Err(err) => err.to_string(),
        };

        for expected_fragment in *expected_fragments {
            assert!(
                message.contains(expected_fragment),
                "{case} ({upstream_case}) error should contain {expected_fragment:?}, got: {message}"
            );
        }
    }
}

#[test]
fn external_fn_specification_rs_external_spec_u8_default_verifies_from_port_source() {
    common::with_clean_verification(|| {
        let observed = "external_fn_spec_u8_default_observed";
        register_u8_default_external_spec_from_port(observed);

        let mut pipeline = VerificationPipeline::collect_from_macros();
        pipeline.context_mut().declare_var_parsed(observed, "u8");
        pipeline.context_mut().push_assert(
            "u8_default_external_spec_value",
            &format!("{observed} == 0u8"),
        );

        let result = pipeline.verify();
        assert!(
            matches!(result, VerifyResult::Verified),
            "foreign_trait1 u8::default external_spec should prove result == 0u8, got: {result:?}"
        );
    });
}

#[test]
fn external_fn_specification_rs_external_spec_u8_default_counterexample_from_port_source() {
    common::with_clean_verification(|| {
        let observed = "external_fn_spec_u8_default_bad_observed";
        register_u8_default_external_spec_from_port(observed);

        let mut pipeline = VerificationPipeline::collect_from_macros();
        pipeline.context_mut().declare_var_parsed(observed, "u8");
        pipeline.context_mut().push_assert(
            "u8_default_external_spec_wrong_value",
            &format!("{observed} == 1u8"),
        );

        let result = pipeline.verify();
        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "foreign_trait1 u8::default external_spec should reject result == 1u8, got: {result:?}"
        );
    });
}

#[test]
fn external_fn_specification_rs_external_spec_lookup_fails_closed_from_port_source() {
    common::with_clean_verification(|| {
        let path = external_fn_specification_port_path_str();
        let error = register_extern_spec_from_manifest_scope_for_call(
            &path,
            env!("CARGO_MANIFEST_DIR"),
            "core::primitive::u8::default",
            "u8::default()",
            Some("external_fn_spec_u8_default_observed"),
        )
        .expect_err("lexically mismatched external_spec target should fail closed")
        .to_string();

        assert!(
            error.contains("no extern_spec for `core::primitive::u8::default`"),
            "lookup error should name the missing target, got: {error}"
        );
        assert!(
            error.contains("dependency crates are not searched"),
            "lookup error should explain the closed dependency-crate boundary, got: {error}"
        );
    });
}
