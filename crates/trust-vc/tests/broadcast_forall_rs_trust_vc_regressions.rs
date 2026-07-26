// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Executable guards for the first upstream broadcast_forall.rs TrustVc scout.
//!
//! These tests intentionally keep the upstream file classified as an
//! unsupported gap. They prove only a grouped-broadcast activation subset that
//! TrustVc can execute today, including named bundles of grouped broadcasts and
//! quantified trigger use, reject an adjacent false universal, and pin the
//! current source-extraction boundary for `broadcast_use!` as fail-closed.

mod common;

use std::{collections::BTreeSet, path::PathBuf};
use trust_vc_core::{verify_function_from_file, verify_macro, VerifyResult};

#[path = "../../../evals/verus/ported/broadcast_forall.rs"]
mod broadcast_forall_port;

fn broadcast_forall_port_path() -> PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../evals/verus/ported/broadcast_forall.rs")
}

fn verus_manifest_path() -> PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/verus-tests.json")
}

fn verify_runtime_case(case: fn()) -> VerifyResult {
    common::verify_and_get_result(|| {
        verify_macro::set_proof_mode(true);
        case();
        verify_macro::set_proof_mode(false);
    })
}

fn verify_source_case(path: &str, case: &str, upstream_case: &str) -> VerifyResult {
    verify_function_from_file(path, case)
        .unwrap_or_else(|err| panic!("{case} ({upstream_case}) should extract: {err}"))
}

const VERIFIED_CASES: &[(&str, fn(), &str)] = &[
    (
        "broadcast_forall_grouped_axiom_verified",
        broadcast_forall_port::broadcast_forall_grouped_axiom_verified,
        "test_ring_algebra_basic/test_ring_algebra_mod_level_2 grouped broadcast activation scout",
    ),
    (
        "broadcast_forall_named_bundle_verified",
        broadcast_forall_port::broadcast_forall_named_bundle_verified,
        "test_ring_algebra_basic grouped-broadcast bundle activation scout",
    ),
    (
        "broadcast_forall_quantified_grouped_axiom_verified",
        broadcast_forall_port::broadcast_forall_quantified_grouped_axiom_verified,
        "test_ring_algebra_broadcast_use_stmt_1 quantified grouped broadcast activation scout",
    ),
];

const COUNTEREXAMPLE_CASES: &[(&str, &str)] = &[(
    "broadcast_forall_false_universal_counterexample",
    "test_fails_by_broadcast_forall_2 false universal scout",
)];

const EXPECTED_CASES: &[(&str, &str, &str, usize)] = &[
    (
        "broadcast_forall_grouped_axiom_verified",
        "test_ring_algebra_broadcast_use_stmt_1",
        "verified",
        1,
    ),
    (
        "broadcast_forall_quantified_grouped_axiom_verified",
        "test_ring_algebra_broadcast_use_stmt_1",
        "verified",
        1,
    ),
    (
        "broadcast_forall_named_bundle_verified",
        "test_ring_algebra_basic",
        "verified",
        2,
    ),
    (
        "broadcast_forall_false_universal_counterexample",
        "test_fails_by_broadcast_forall_2",
        "counterexample",
        1,
    ),
    (
        "broadcast_forall_source_broadcast_use_verified",
        "test_ring_algebra_broadcast_use_stmt_1",
        "verified",
        1,
    ),
    (
        "broadcast_forall_source_broadcast_use_local_macro_verified",
        "test_ring_algebra_broadcast_use_stmt_1",
        "verified",
        1,
    ),
];

const EXPECTED_ERROR_PATTERNS: &[(&str, &[&str])] = &[];

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
        .unwrap_or_else(|| panic!("broadcast_forall port should define {const_name}"));

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

fn metadata_entries(file: &syn::File) -> Vec<CaseMetadata> {
    let array = referenced_array_const(file, "BROADCAST_FORALL_RS_EXPECTED_CASES");
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
            "duplicate broadcast_forall metadata for {case_id}"
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

fn error_pattern_entries(file: &syn::File) -> Vec<(String, Vec<String>)> {
    let array = referenced_array_const(file, "BROADCAST_FORALL_RS_EXPECTED_ERROR_PATTERNS");

    array
        .elems
        .iter()
        .map(|entry| {
            let syn::Expr::Tuple(tuple) = entry else {
                panic!("expected tuple error-pattern metadata entry");
            };
            assert_eq!(
                tuple.elems.len(),
                2,
                "error-pattern entries should have case and expected patterns"
            );

            (
                literal_string(&tuple.elems[0]),
                string_slice(&tuple.elems[1]),
            )
        })
        .collect()
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
            },
        )
        .collect()
}

fn expected_error_patterns() -> Vec<(String, Vec<String>)> {
    EXPECTED_ERROR_PATTERNS
        .iter()
        .map(|(case_id, patterns)| {
            (
                (*case_id).to_string(),
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
            entry["upstream_path"].as_str()
                == Some("source/rust_verify_test/tests/broadcast_forall.rs")
        })
        .expect("Verus manifest should contain broadcast_forall.rs row")
        .clone()
}

fn manifest_expected_metadata() -> Vec<CaseMetadata> {
    manifest_row()["expected_cases"]
        .as_array()
        .expect("broadcast_forall.rs row should contain expected_cases")
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

fn manifest_error_patterns() -> Vec<(String, Vec<String>)> {
    manifest_row()["expected_cases"]
        .as_array()
        .expect("broadcast_forall.rs row should contain expected_cases")
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
fn broadcast_forall_rs_expected_case_metadata_is_exact() {
    let source = std::fs::read_to_string(broadcast_forall_port_path())
        .expect("broadcast_forall port should be readable");
    let file = syn::parse_file(&source)
        .expect("broadcast_forall port should parse as ordinary Rust syntax");
    assert_eq!(metadata_entries(&file), expected_metadata());
    assert_eq!(
        broadcast_forall_port::broadcast_forall_rs_expected_cases(),
        EXPECTED_CASES
    );
    assert_eq!(error_pattern_entries(&file), expected_error_patterns());
    assert_eq!(
        broadcast_forall_port::broadcast_forall_rs_expected_error_patterns(),
        EXPECTED_ERROR_PATTERNS
    );
}

#[test]
fn broadcast_forall_rs_expected_case_metadata_matches_manifest() {
    let source = std::fs::read_to_string(broadcast_forall_port_path())
        .expect("broadcast_forall port should be readable");
    let file = syn::parse_file(&source)
        .expect("broadcast_forall port should parse as ordinary Rust syntax");

    assert_eq!(
        metadata_entries(&file),
        manifest_expected_metadata(),
        "broadcast_forall manifest expected_cases should match port metadata exactly"
    );
    assert_eq!(
        error_pattern_entries(&file),
        manifest_error_patterns(),
        "broadcast_forall manifest expected_error_patterns should match port metadata exactly"
    );
}

#[test]
fn broadcast_forall_rs_grouped_broadcast_subset_verifies() {
    for (case_name, case, upstream_case) in VERIFIED_CASES {
        let result = verify_runtime_case(*case);
        assert!(
            matches!(result, VerifyResult::Verified),
            "{case_name} ({upstream_case}) should verify, got: {result:?}"
        );
    }
}

#[test]
fn broadcast_forall_rs_false_universal_counterexample_from_file() {
    let path = broadcast_forall_port_path();
    let path = path
        .to_str()
        .expect("broadcast_forall port path should be UTF-8");

    for (case, upstream_case) in COUNTEREXAMPLE_CASES {
        let result = verify_source_case(path, case, upstream_case);
        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "{case} ({upstream_case}) should be rejected with a counterexample, got: {result:?}"
        );
    }
}

#[test]
fn broadcast_forall_rs_source_broadcast_use_activates_from_file() {
    // REINSTATED (un-quarantine #4): file-path `broadcast_use!` now ACTIVATES the
    // grouped broadcast (both a direct statement and a local macro-expanded one),
    // so the activated grouped axiom discharges the opaque-predicate assertion on
    // the file path exactly as it does at runtime. Previously both fell to the
    // coarse `Unsupported broadcast_use!()` extraction error.
    let path = broadcast_forall_port_path();
    let path = path
        .to_str()
        .expect("broadcast_forall port path should be UTF-8");

    for (case, upstream_case) in [
        (
            "broadcast_forall_source_broadcast_use_verified",
            "statement-level broadcast_use! source activation",
        ),
        (
            "broadcast_forall_source_broadcast_use_local_macro_verified",
            "local macro-expanded broadcast_use! source activation",
        ),
    ] {
        let result = verify_source_case(path, case, upstream_case);
        assert!(
            matches!(result, VerifyResult::Verified),
            "{case} ({upstream_case}) should VERIFY via file-path broadcast_use! activation, got: {result:?}"
        );
    }
}
