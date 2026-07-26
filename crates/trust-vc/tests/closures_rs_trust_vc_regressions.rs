// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Executable guards for the closures.rs partial port.
//!
//! These tests intentionally keep `source/rust_verify_test/tests/closures.rs`
//! fail-closed in the corpus manifest. The port records supported typed
//! `SpecFn::new` closure equality, direct unary `SpecFn::call`, typed closure
//! captures, a concrete `SpecFn` argument helper, rejected false assertions, and
//! Rust-valid closure surfaces that TrustVc does not lower directly yet.

mod common;

use std::{
    collections::{BTreeMap, BTreeSet},
    path::{Path, PathBuf},
};
use trust_vc_core::{verify_function_from_file, VerifyResult};

fn closures_port_path() -> PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/ported/closures.rs")
}

fn closures_upstream_path() -> PathBuf {
    common::pinned_verus_test_path("closures.rs")
}

fn verus_manifest_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/verus-tests.json")
}

fn verify_port_case(case: &str, upstream_case: &str) -> VerifyResult {
    let path = closures_port_path();
    let path = path.to_str().expect("closures.rs path should be UTF-8");
    verify_function_from_file(path, case)
        .unwrap_or_else(|err| panic!("{case} ({upstream_case}) should extract: {err}"))
}

fn fail_closed_message(case: &str, upstream_case: &str) -> String {
    let path = closures_port_path();
    let path = path.to_str().expect("closures.rs path should be UTF-8");

    match verify_function_from_file(path, case) {
        Err(err) => err.to_string(),
        Ok(VerifyResult::Error { message }) => message,
        Ok(other) => {
            panic!("{case} ({upstream_case}) should fail closed with Error, got: {other:?}")
        }
    }
}

const VERIFIED_CASES: &[(&str, &str)] = &[
    ("spec_fn_closure_add_one_extensional", "test1"),
    ("spec_fn_two_arg_bool_extensional", "test1"),
    ("spec_fn_tuple_binder_extensional", ""),
    ("spec_fn_closure_capture_arithmetic_extensional", ""),
    ("spec_fn_value_call_reflexive_verified", ""),
    // FLIP (bare-closure inline): `let f = |x| x + 1; assert!(f(10) == 11)` now
    // inlines `f(10)` -> `10 + 1` and verifies. Historical `_currently_errors`
    // case-id retained for stable upstream/manifest mapping.
    ("local_closure_application_currently_errors", "test1"),
];

const COUNTEREXAMPLE_CASES: &[(&str, &str)] = &[
    (
        "spec_fn_closure_add_one_wrong_counterexample",
        "test1_fails4",
    ),
    ("spec_fn_two_arg_bool_wrong_counterexample", "test1_fails1"),
    ("spec_fn_tuple_binder_wrong_counterexample", ""),
    ("spec_fn_closure_capture_wrong_counterexample", ""),
    ("spec_fn_value_call_wrong_counterexample", ""),
];

const FAIL_CLOSED_CASES: &[(&str, &str, &[&str])] = &[
    (
        "spec_fn_direct_call_currently_errors",
        "",
        &[
            "SpecFn::new(...) closures cannot be encoded directly",
            "higher-order combinator",
        ],
    ),
    (
        "spec_fn_argument_apply_to_one_currently_errors",
        "",
        &[
            "SpecFn::new(...) closures cannot be encoded directly",
            "higher-order combinator",
        ],
    ),
    (
        "spec_fn_closure_parameter_inference_currently_errors",
        "",
        &[
            "requires an explicit type annotation",
            "spec closure parameter",
        ],
    ),
    (
        "return_in_spec_fn_closure_currently_errors",
        "return_in_closure",
        &[
            "return",
            "block expression",
            "unsupported expression",
            "SpecFn::new(...) closures cannot be encoded directly",
        ],
    ),
];

const EXPECTED_CASES: &[(&str, &str, &str, usize)] = &[
    (
        "spec_fn_closure_add_one_extensional",
        "test1",
        "verified",
        1,
    ),
    (
        "spec_fn_closure_add_one_wrong_counterexample",
        "test1_fails4",
        "counterexample",
        1,
    ),
    ("spec_fn_two_arg_bool_extensional", "test1", "verified", 1),
    (
        "spec_fn_two_arg_bool_wrong_counterexample",
        "test1_fails1",
        "counterexample",
        1,
    ),
    ("spec_fn_tuple_binder_extensional", "", "verified", 1),
    (
        "spec_fn_tuple_binder_wrong_counterexample",
        "",
        "counterexample",
        1,
    ),
    (
        "spec_fn_closure_capture_arithmetic_extensional",
        "",
        "verified",
        1,
    ),
    (
        "spec_fn_closure_capture_wrong_counterexample",
        "",
        "counterexample",
        1,
    ),
    ("spec_fn_value_call_reflexive_verified", "", "verified", 1),
    (
        "spec_fn_value_call_wrong_counterexample",
        "",
        "counterexample",
        1,
    ),
    ("spec_fn_direct_call_currently_errors", "", "error", 0),
    (
        "spec_fn_argument_apply_to_one_currently_errors",
        "",
        "error",
        0,
    ),
    (
        "local_closure_application_currently_errors",
        "test1",
        "verified",
        1,
    ),
    (
        "spec_fn_closure_parameter_inference_currently_errors",
        "",
        "error",
        0,
    ),
    (
        "return_in_spec_fn_closure_currently_errors",
        "return_in_closure",
        "error",
        0,
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
        .unwrap_or_else(|| panic!("closures port should define {const_name}"));

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
    let array = referenced_array_const(file, "CLOSURES_RS_FAIL_CLOSED_ERROR_PATTERNS");
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
    let array = referenced_array_const(file, "CLOSURES_RS_EXPECTED_CASES");
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
            "duplicate closures metadata for {case_id}"
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
    let mut error_patterns = BTreeMap::new();
    for (case, _, expected_fragments) in FAIL_CLOSED_CASES {
        assert!(
            error_patterns
                .insert(
                    *case,
                    expected_fragments
                        .iter()
                        .map(|fragment| (*fragment).to_string())
                        .collect::<Vec<_>>(),
                )
                .is_none(),
            "duplicate fail-closed metadata for {case}"
        );
    }

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
            entry["upstream_path"].as_str() == Some("source/rust_verify_test/tests/closures.rs")
        })
        .expect("Verus manifest should contain closures.rs row");

    row["expected_cases"]
        .as_array()
        .expect("closures.rs row should contain expected_cases")
        .iter()
        .map(|case| CaseMetadata {
            case_id: case["case_id"]
                .as_str()
                .expect("manifest case should contain case_id")
                .to_string(),
            upstream_case_id: case
                .get("upstream_case_id")
                .and_then(serde_json::Value::as_str)
                .unwrap_or("")
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
            expected_error_patterns: case
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
fn closures_rs_port_file_is_rust_syntax() {
    let source =
        std::fs::read_to_string(closures_port_path()).expect("closures port should be readable");
    syn::parse_file(&source).expect("closures port should parse as ordinary Rust syntax");
}

#[test]
fn closures_rs_pinned_upstream_case_shapes_are_present() {
    let path = closures_upstream_path();
    if !path.exists() {
        eprintln!(
            "skipping pinned upstream closures.rs shape check; missing {}",
            path.display()
        );
        return;
    }

    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", path.display()));
    for expected in [
        "#[test] test1",
        "proof fn testfun1()",
        "proof fn takefun(f: spec_fn(u32, u64) -> bool)",
        "proof fn test_specf(p: u32)",
        "proof fn test_specf_inference(p: u32)",
        "test1_fails4",
        "#[test] test_fn_spec_type",
        "#[test] return_in_closure",
        "return is not allowed in pure context",
    ] {
        assert!(
            source.contains(expected),
            "pinned upstream closures.rs should still contain {expected}"
        );
    }
}

#[test]
fn closures_rs_expected_case_metadata_is_exact() {
    let source =
        std::fs::read_to_string(closures_port_path()).expect("closures port should be readable");
    let file =
        syn::parse_file(&source).expect("closures port should parse as ordinary Rust syntax");
    assert_eq!(metadata_entries(&file), expected_metadata());
    assert!(
        source.contains("closures_rs_fail_closed_error_patterns"),
        "closures port should export fail-closed error-pattern metadata"
    );
}

#[test]
fn closures_rs_expected_case_metadata_matches_manifest() {
    let source =
        std::fs::read_to_string(closures_port_path()).expect("closures port should be readable");
    let file =
        syn::parse_file(&source).expect("closures port should parse as ordinary Rust syntax");
    assert_eq!(
        metadata_entries(&file),
        manifest_expected_metadata(),
        "closures.rs manifest expected_cases should match port metadata and error patterns exactly"
    );
}

#[test]
fn closures_rs_verified_subset_verifies_from_file() {
    for (case, upstream_case) in VERIFIED_CASES {
        let result = verify_port_case(case, upstream_case);
        assert!(
            matches!(result, VerifyResult::Verified),
            "{case} ({upstream_case}) should verify, got: {result:?}"
        );
    }
}

#[test]
fn closures_rs_false_claims_are_rejected_from_file() {
    for (case, upstream_case) in COUNTEREXAMPLE_CASES {
        let result = verify_port_case(case, upstream_case);
        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "{case} ({upstream_case}) should produce a counterexample, got: {result:?}"
        );
    }
}

#[test]
fn closures_rs_unsupported_surfaces_fail_closed_from_file() {
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
