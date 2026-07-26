// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Executable guards for the first upstream traits_modules_pub_crate.rs TrustVc
//! scout slice.
//!
//! These tests intentionally keep the upstream file as an unsupported gap. They
//! pin only a small Rust-valid pub(crate) trait/module subset: a module-split
//! trait declaration, impl, and generic caller that verifies; bad module-split
//! trait impl bodies that must not verify; a receiver-method Self boundary that
//! fails closed; and current impl-contract boundaries that fail closed.

mod common;

use std::{
    collections::{BTreeMap, BTreeSet},
    path::{Path, PathBuf},
};
use trust_vc_core::{verify_function_from_file, VerifyResult};

fn traits_modules_pub_crate_port_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../evals/verus/ported/traits_modules_pub_crate.rs")
}

fn verus_manifest_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/verus-tests.json")
}

fn pinned_upstream_traits_modules_pub_crate_path() -> PathBuf {
    common::pinned_verus_test_path("traits_modules_pub_crate.rs")
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

const VERIFIED_CASES: &[(&str, &str)] = &[(
    "pub_crate_module_trait_bound_dispatch_verified",
    "test_supported_9 pub(crate) module-scoped trait dispatch",
)];

const COUNTEREXAMPLE_CASES: &[(&str, &str)] = &[
    (
        "pub_crate_module_false_assert_counterexample",
        "test_verify_2 inherited pub(crate) trait postcondition",
    ),
    // The pub(crate) receiver-method `Self` boundary now ENCODES: its `&self`
    // method body `trust_vc::assert!(false)` is properly refuted (model-less
    // Counterexample) rather than fail-closing to an "unrecognized types"
    // Unknown. `assert!(false)` is unconditionally false, so refutation is the
    // sound verdict — the case graduates from the unknown-boundary list.
    (
        "pub_crate_module_self_false_assert_counterexample",
        "test_verify_2 pub(crate) receiver-method Self boundary",
    ),
];

// The self-receiver `Self` boundary case moved to COUNTEREXAMPLE_CASES (it now
// refutes rather than failing to encode); no remaining unknown-boundary cases.
const UNKNOWN_FAIL_CLOSED_CASES: &[(&str, &str, &str)] = &[];

const FAIL_CLOSED_CASES: &[(&str, &str, &str)] = &[
    (
        "pub_crate_module_impl_requires_currently_blocked",
        "test_ill_formed_8 direct impl-side requires diagnostic boundary",
        "trait method implementation cannot declare requires",
    ),
    (
        "pub_crate_module_grouped_impl_requires_currently_blocked",
        "test_ill_formed_8 grouped impl-side requires diagnostic boundary",
        "trait method implementation cannot declare requires",
    ),
    (
        "pub_crate_module_conflicting_returns_clause_currently_blocked",
        "test_ill_formed_8 trait method/impl contract diagnostic boundary",
        "a `returns` clause cannot be declared on both a trait method impl and its declaration",
    ),
];

const EXPECTED_CASES: &[(&str, &str, &str, usize)] = &[
    (
        "pub_crate_module_trait_bound_dispatch_verified",
        "test_supported_9",
        "verified",
        1,
    ),
    (
        "pub_crate_module_false_assert_counterexample",
        "test_verify_2",
        "counterexample",
        1,
    ),
    (
        "pub_crate_module_impl_requires_currently_blocked",
        "test_ill_formed_8",
        "error",
        0,
    ),
    (
        "pub_crate_module_grouped_impl_requires_currently_blocked",
        "test_ill_formed_8",
        "error",
        0,
    ),
    (
        "pub_crate_module_conflicting_returns_clause_currently_blocked",
        "test_ill_formed_8",
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
        .unwrap_or_else(|| panic!("traits_modules_pub_crate port should define {const_name}"));

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
    let array = referenced_array_const(file, "TRAITS_MODULES_PUB_CRATE_RS_EXPECTED_ERROR_PATTERNS");
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
    let array = referenced_array_const(file, "TRAITS_MODULES_PUB_CRATE_RS_EXPECTED_CASES");
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
            "duplicate traits_modules_pub_crate metadata for {case_id}"
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
            entry["upstream_path"].as_str()
                == Some("source/rust_verify_test/tests/traits_modules_pub_crate.rs")
        })
        .expect("Verus manifest should contain traits_modules_pub_crate.rs row");

    row["expected_cases"]
        .as_array()
        .expect("traits_modules_pub_crate.rs row should contain expected_cases")
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
fn traits_modules_pub_crate_rs_expected_case_metadata_is_exact() {
    let source = std::fs::read_to_string(traits_modules_pub_crate_port_path())
        .expect("traits_modules_pub_crate port should be readable");
    let file = syn::parse_file(&source)
        .expect("traits_modules_pub_crate port should parse as ordinary Rust syntax");
    assert_eq!(metadata_entries(&file), expected_metadata());
}

#[test]
fn traits_modules_pub_crate_rs_expected_case_metadata_matches_manifest() {
    let source = std::fs::read_to_string(traits_modules_pub_crate_port_path())
        .expect("traits_modules_pub_crate port should be readable");
    let file = syn::parse_file(&source)
        .expect("traits_modules_pub_crate port should parse as ordinary Rust syntax");
    assert_eq!(metadata_entries(&file), manifest_expected_metadata());
}

#[test]
fn traits_modules_pub_crate_rs_port_file_is_rust_syntax() {
    let source = std::fs::read_to_string(traits_modules_pub_crate_port_path())
        .expect("traits_modules_pub_crate port should be readable");
    syn::parse_file(&source)
        .expect("traits_modules_pub_crate port should parse as ordinary Rust syntax");
}

#[test]
fn traits_modules_pub_crate_rs_pinned_upstream_case_shapes_are_present() {
    let path = pinned_upstream_traits_modules_pub_crate_path();
    if !path.exists() {
        eprintln!(
            "skipping pinned upstream traits_modules_pub_crate.rs shape check; missing {}",
            path.display()
        );
        return;
    }

    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", path.display()));
    for expected in [
        "Note: this file is simply traits_modules.rs with pub replaced with pub(crate)",
        "test_supported_8",
        "test_supported_9",
        "test_ill_formed_8",
        "test_verify_2",
        "test_multiple",
        "pub(crate) trait T",
    ] {
        assert!(
            source.contains(expected),
            "pinned upstream traits_modules_pub_crate.rs should still contain {expected}"
        );
    }
}

#[test]
fn traits_modules_pub_crate_rs_verified_subset_verifies_from_file() {
    let path = traits_modules_pub_crate_port_path();
    let path = path
        .to_str()
        .expect("traits_modules_pub_crate port path should be UTF-8");

    for (case, upstream_case) in VERIFIED_CASES {
        let result = verify_case(path, case, upstream_case);
        assert!(
            matches!(result, VerifyResult::Verified),
            "{case} ({upstream_case}) should verify, got: {result:?}"
        );
    }
}

#[test]
fn traits_modules_pub_crate_rs_counterexample_subset_is_rejected_from_file() {
    let path = traits_modules_pub_crate_port_path();
    let path = path
        .to_str()
        .expect("traits_modules_pub_crate port path should be UTF-8");

    for (case, upstream_case) in COUNTEREXAMPLE_CASES {
        let result = verify_case(path, case, upstream_case);
        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "{case} ({upstream_case}) should be rejected, got: {result:?}"
        );
    }
}

#[test]
fn traits_modules_pub_crate_rs_self_receiver_boundary_fails_closed_from_file() {
    let path = traits_modules_pub_crate_port_path();
    let path = path
        .to_str()
        .expect("traits_modules_pub_crate port path should be UTF-8");

    for (case, upstream_case, expected_fragment) in UNKNOWN_FAIL_CLOSED_CASES {
        let result = verify_case(path, case, upstream_case);
        assert!(
            matches!(result, VerifyResult::Unknown { ref reason, .. } if reason.contains(expected_fragment)),
            "{case} ({upstream_case}) should fail closed as Unknown containing {expected_fragment:?}, got: {result:?}"
        );
    }
}

#[test]
fn traits_modules_pub_crate_rs_conflicting_impl_contract_fails_closed_from_file() {
    let path = traits_modules_pub_crate_port_path();
    let path = path
        .to_str()
        .expect("traits_modules_pub_crate port path should be UTF-8");

    for (case, upstream_case, expected_fragment) in FAIL_CLOSED_CASES {
        expect_fail_closed(path, case, upstream_case, expected_fragment);
    }
}
