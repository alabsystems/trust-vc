// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Executable guards for the first upstream traits_dyn.rs TrustVc scout slice.
//!
//! These tests intentionally keep the upstream file as an unsupported gap. They
//! pin only a small Rust-valid trait/dyn boundary: generic static dispatch over
//! trait method contracts, a bad assertion against a `Self: Sized` default
//! method contract, and direct reference/boxed/Sized-only/generic-method dyn
//! trait-object dispatch boundaries that must fail closed.

mod common;

use std::{
    collections::{BTreeMap, BTreeSet},
    path::{Path, PathBuf},
};
use trust_vc_core::{verify_function_from_file, VerifyResult};

fn traits_dyn_port_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/ported/traits_dyn.rs")
}

fn verus_manifest_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/verus-tests.json")
}

fn pinned_upstream_traits_dyn_path() -> PathBuf {
    common::pinned_verus_test_path("traits_dyn.rs")
}

fn verify_case(path: &str, case: &str, upstream_case: &str) -> VerifyResult {
    verify_function_from_file(path, case)
        .unwrap_or_else(|err| panic!("{case} ({upstream_case}) should extract: {err}"))
}

fn expect_fail_closed(path: &str, case: &str, upstream_case: &str, expected_fragment: &str) {
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

const VERIFIED_CASES: &[(&str, &str)] = &[
    (
        "traits_dyn_trait_bound_static_dispatch_verified",
        "test_dyn_generic",
    ),
    (
        "traits_dyn_sized_only_static_dispatch_verified",
        "Self: Sized trait method static-dispatch boundary",
    ),
];

const COUNTEREXAMPLE_CASES: &[(&str, &str)] = &[(
    "traits_dyn_sized_default_false_assert_counterexample",
    "dyn_proof_must_be_inhabited_sized",
)];

const FAIL_CLOSED_CASES: &[(&str, &str, &str)] = &[
    (
        "traits_dyn_trait_object_dispatch_currently_blocked",
        "test_dyn",
        "dyn",
    ),
    (
        "traits_dyn_boxed_trait_object_dispatch_currently_blocked",
        "test_dyn2",
        "dyn",
    ),
    (
        "traits_dyn_sized_only_trait_object_dispatch_currently_blocked",
        "Self: Sized trait method dyn-dispatch boundary",
        "unsupported method",
    ),
    (
        "traits_dyn_generic_method_trait_object_not_object_safe_currently_blocked",
        "object-safety diagnostic for generic methods on dyn traits",
        "unsupported method",
    ),
];

const EXPECTED_CASES: &[(&str, &str, &str, usize)] = &[
    (
        "traits_dyn_trait_bound_static_dispatch_verified",
        "test_dyn_generic",
        "verified",
        1,
    ),
    (
        "traits_dyn_sized_only_static_dispatch_verified",
        "test_dyn_generic",
        "verified",
        1,
    ),
    (
        "traits_dyn_sized_default_false_assert_counterexample",
        "dyn_proof_must_be_inhabited_sized",
        "counterexample",
        1,
    ),
    (
        "traits_dyn_trait_object_dispatch_currently_blocked",
        "test_dyn",
        "error",
        0,
    ),
    (
        "traits_dyn_boxed_trait_object_dispatch_currently_blocked",
        "test_dyn2",
        "error",
        0,
    ),
    (
        "traits_dyn_sized_only_trait_object_dispatch_currently_blocked",
        "test_dyn_generic",
        "error",
        0,
    ),
    (
        "traits_dyn_generic_method_trait_object_not_object_safe_currently_blocked",
        "test_dyn_generic",
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
        .unwrap_or_else(|| panic!("traits_dyn port should define {const_name}"));

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
    let array = referenced_array_const(file, "TRAITS_DYN_RS_EXPECTED_ERROR_PATTERNS");
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
    let array = referenced_array_const(file, "TRAITS_DYN_RS_EXPECTED_CASES");
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
            "duplicate traits_dyn metadata for {case_id}"
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
    EXPECTED_CASES
        .iter()
        .map(
            |(case_id, upstream_case_id, expected_verdict, min_obligations)| CaseMetadata {
                case_id: (*case_id).to_string(),
                upstream_case_id: (*upstream_case_id).to_string(),
                expected_verdict: (*expected_verdict).to_string(),
                min_obligations: *min_obligations,
                expected_error_patterns: FAIL_CLOSED_CASES
                    .iter()
                    .find(|(fail_case_id, _, _)| fail_case_id == case_id)
                    .map(|(_, _, pattern)| vec![(*pattern).to_string()])
                    .unwrap_or_default(),
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
            entry["upstream_path"].as_str() == Some("source/rust_verify_test/tests/traits_dyn.rs")
        })
        .expect("Verus manifest should contain traits_dyn.rs row");

    row["expected_cases"]
        .as_array()
        .expect("traits_dyn.rs row should contain expected_cases")
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
fn traits_dyn_rs_expected_case_metadata_is_exact() {
    let source = std::fs::read_to_string(traits_dyn_port_path())
        .expect("traits_dyn port should be readable");
    let file = syn::parse_file(&source).expect("traits_dyn port should parse as ordinary Rust");
    assert_eq!(metadata_entries(&file), expected_metadata());
    assert!(
        source.contains("traits_dyn_rs_expected_cases"),
        "traits_dyn port should export expected-case metadata"
    );
    assert!(
        source.contains("traits_dyn_rs_expected_error_patterns"),
        "traits_dyn port should export fail-closed error-pattern metadata"
    );
}

#[test]
fn traits_dyn_rs_expected_case_metadata_matches_manifest() {
    let source = std::fs::read_to_string(traits_dyn_port_path())
        .expect("traits_dyn port should be readable");
    let file = syn::parse_file(&source).expect("traits_dyn port should parse as ordinary Rust");
    assert_eq!(metadata_entries(&file), manifest_expected_metadata());
}

#[test]
fn traits_dyn_rs_port_file_is_rust_syntax() {
    let source = std::fs::read_to_string(traits_dyn_port_path())
        .expect("traits_dyn port should be readable");
    syn::parse_file(&source).expect("traits_dyn port should parse as ordinary Rust syntax");
}

#[test]
fn traits_dyn_rs_pinned_upstream_case_shapes_are_present() {
    let path = pinned_upstream_traits_dyn_path();
    if !path.exists() {
        eprintln!(
            "skipping pinned upstream traits_dyn.rs shape check; missing {}",
            path.display()
        );
        return;
    }

    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", path.display()));
    for expected in [
        "test_dyn",
        "test_dyn_generic",
        "dyn_in_struct",
        "dyn_unsupported1",
        "test_dyn2",
    ] {
        assert!(
            source.contains(expected),
            "pinned upstream traits_dyn.rs should still contain {expected}"
        );
    }
}

#[test]
fn traits_dyn_rs_verified_subset_verifies_from_file() {
    let path = traits_dyn_port_path();
    let path = path.to_str().expect("traits_dyn port path should be UTF-8");

    for (case, upstream_case) in VERIFIED_CASES {
        let result = verify_case(path, case, upstream_case);
        assert!(
            matches!(result, VerifyResult::Verified),
            "{case} ({upstream_case}) should verify, got: {result:?}"
        );
    }
}

#[test]
fn traits_dyn_rs_counterexample_subset_is_rejected_from_file() {
    let path = traits_dyn_port_path();
    let path = path.to_str().expect("traits_dyn port path should be UTF-8");

    for (case, upstream_case) in COUNTEREXAMPLE_CASES {
        let result = verify_case(path, case, upstream_case);
        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "{case} ({upstream_case}) should be rejected, got: {result:?}"
        );
    }
}

#[test]
fn traits_dyn_rs_dyn_dispatch_boundaries_fail_closed_from_file() {
    let path = traits_dyn_port_path();
    let path = path.to_str().expect("traits_dyn port path should be UTF-8");

    for (case, upstream_case, expected_fragment) in FAIL_CLOSED_CASES {
        expect_fail_closed(path, case, upstream_case, expected_fragment);
    }
}
