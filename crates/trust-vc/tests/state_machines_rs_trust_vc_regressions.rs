// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Executable guards for the first upstream state_machines.rs TrustVc scout
//! slice.
//!
//! These tests intentionally keep
//! `source/rust_verify_test/tests/state_machines.rs` classified as an
//! unsupported gap. They pin only Rust-valid relation/token surrogates, stable
//! adjacent counterexamples, and fail-closed boundaries for direct
//! `state_machine!` and `tokenized_state_machine!` macro extraction.

mod common;

use std::{
    collections::{BTreeMap, BTreeSet},
    path::{Path, PathBuf},
};
use trust_vc_core::{verify_function_from_file, VerifyResult};

fn state_machines_port_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/ported/state_machines.rs")
}

fn verus_manifest_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/verus-tests.json")
}

fn pinned_upstream_state_machines_path() -> PathBuf {
    common::pinned_verus_test_path("state_machines.rs")
}

fn verify_case(path: &str, case: &str, upstream_case: &str) -> VerifyResult {
    verify_function_from_file(path, case)
        .unwrap_or_else(|err| panic!("{case} ({upstream_case}) should extract: {err}"))
}

fn expect_fail_closed(path: &str, case: &str, upstream_case: &str, expected_fragments: &[&str]) {
    let message = match verify_function_from_file(path, case) {
        Err(err) => err.to_string(),
        Ok(VerifyResult::Error { message }) => message,
        Ok(result) => {
            panic!("{case} ({upstream_case}) should fail closed with Error, got: {result:?}")
        }
    };

    for expected_fragment in expected_fragments {
        assert!(
            message.contains(expected_fragment),
            "{case} ({upstream_case}) error should contain {expected_fragment:?}, got: {message}"
        );
    }
}

const EXPECTED_CASE_METADATA: &[(&str, &str, &str, usize)] = &[
    (
        "state_machine_relation_codegen_tr1_verified",
        "relation_codegen",
        "verified",
        4,
    ),
    (
        "state_machine_init_branch_relation_verified",
        "relation_codegen",
        "verified",
        3,
    ),
    (
        "tokenized_bool_add_remove_surrogate_verified",
        "bool_codegen",
        "verified",
        4,
    ),
    (
        "state_machine_relation_wrong_post_counterexample",
        "relation_codegen",
        "counterexample",
        1,
    ),
    (
        "tokenized_bool_have_missing_counterexample",
        "bool_codegen",
        "counterexample",
        1,
    ),
    (
        "state_machine_macro_surface_currently_blocked",
        "state_machine! macro surface",
        "error",
        0,
    ),
    (
        "tokenized_state_machine_macro_surface_currently_blocked",
        "tokenized_state_machine! macro surface",
        "error",
        0,
    ),
];

const VERIFIED_CASES: &[(&str, &str)] = &[
    (
        "state_machine_relation_codegen_tr1_verified",
        "relation_codegen tr1",
    ),
    (
        "state_machine_init_branch_relation_verified",
        "relation_codegen initialize",
    ),
    (
        "tokenized_bool_add_remove_surrogate_verified",
        "bool_codegen add/have/remove token flow",
    ),
];

const COUNTEREXAMPLE_CASES: &[(&str, &str)] = &[
    (
        "state_machine_relation_wrong_post_counterexample",
        "relation_codegen false post-state relation",
    ),
    (
        "tokenized_bool_have_missing_counterexample",
        "bool_codegen test_inst1_fail",
    ),
];

const FAIL_CLOSED_CASES: &[(&str, &str, &[&str])] = &[
    (
        "state_machine_macro_surface_currently_blocked",
        "state_machine! macro surface",
        &["unsupported macro", "state_machine"],
    ),
    (
        "tokenized_state_machine_macro_surface_currently_blocked",
        "tokenized_state_machine! macro surface",
        &["unsupported macro", "tokenized_state_machine"],
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
        .unwrap_or_else(|| panic!("state_machines port should define {const_name}"));

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
    let array = referenced_array_const(file, "STATE_MACHINES_RS_EXPECTED_ERROR_PATTERNS");
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
    let array = referenced_array_const(file, "STATE_MACHINES_RS_EXPECTED_CASES");
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
            "duplicate state_machines metadata for {case_id}"
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

fn expected_error_pattern_entries() -> BTreeMap<String, Vec<String>> {
    FAIL_CLOSED_CASES
        .iter()
        .map(|&(case, _, patterns)| {
            (
                case.to_string(),
                patterns
                    .iter()
                    .map(|pattern| (*pattern).to_string())
                    .collect(),
            )
        })
        .collect()
}

fn expected_metadata_from_tests() -> Vec<CaseMetadata> {
    let mut patterns_by_case = expected_error_pattern_entries();

    EXPECTED_CASE_METADATA
        .iter()
        .map(
            |(case_id, upstream_case_id, expected_verdict, min_obligations)| CaseMetadata {
                case_id: (*case_id).to_string(),
                upstream_case_id: (*upstream_case_id).to_string(),
                expected_verdict: (*expected_verdict).to_string(),
                min_obligations: *min_obligations,
                expected_error_patterns: patterns_by_case.remove(*case_id).unwrap_or_default(),
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
                == Some("source/rust_verify_test/tests/state_machines.rs")
        })
        .expect("Verus manifest should contain state_machines.rs row");

    row["expected_cases"]
        .as_array()
        .expect("state_machines.rs row should contain expected_cases")
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
fn state_machines_rs_port_file_is_rust_syntax() {
    let source = std::fs::read_to_string(state_machines_port_path())
        .expect("state_machines port should be readable");
    syn::parse_file(&source).expect("state_machines port should parse as ordinary Rust syntax");
}

#[test]
fn state_machines_rs_pinned_upstream_case_shapes_are_present() {
    let path = pinned_upstream_state_machines_path();
    if !path.exists() {
        eprintln!(
            "skipping pinned upstream state_machines.rs shape check; missing {}",
            path.display()
        );
        return;
    }

    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", path.display()));
    for expected in [
        "dupe_name_fail",
        "test_birds_eye_init_error",
        "relation_codegen",
        "relation_codegen_special",
        "nondet_tokenizing",
        "test_let_pattern",
        "bool_codegen",
        "persistent_bool_codegen",
    ] {
        assert!(
            source.contains(expected),
            "pinned upstream state_machines.rs should still contain {expected}"
        );
    }
}

#[test]
fn state_machines_rs_expected_case_metadata_is_exact() {
    let source = std::fs::read_to_string(state_machines_port_path())
        .expect("state_machines port should be readable");
    let file =
        syn::parse_file(&source).expect("state_machines port should parse as ordinary Rust syntax");

    assert_eq!(
        metadata_entries(&file),
        expected_metadata_from_tests(),
        "state_machines port expected-case metadata should match the regression inventory"
    );
    assert_eq!(
        error_pattern_entries(&file),
        expected_error_pattern_entries(),
        "state_machines port error-pattern metadata should match fail-closed cases"
    );
    assert!(
        source.contains("state_machines_rs_expected_cases")
            && source.contains("state_machines_rs_expected_error_patterns"),
        "state_machines port should expose expected-case and error-pattern metadata accessors"
    );
}

#[test]
fn state_machines_rs_expected_case_metadata_matches_manifest() {
    let source = std::fs::read_to_string(state_machines_port_path())
        .expect("state_machines port should be readable");
    let file =
        syn::parse_file(&source).expect("state_machines port should parse as ordinary Rust syntax");

    assert_eq!(
        metadata_entries(&file),
        manifest_expected_metadata(),
        "state_machines manifest expected_cases should match port metadata exactly"
    );
}

#[test]
fn state_machines_rs_error_cases_have_expected_error_patterns() {
    let source = std::fs::read_to_string(state_machines_port_path())
        .expect("state_machines port should be readable");
    let file =
        syn::parse_file(&source).expect("state_machines port should parse as ordinary Rust syntax");
    let mut patterns_by_case = error_pattern_entries(&file);

    for expected_case in metadata_entries(&file) {
        if expected_case.expected_verdict == "error" {
            assert_eq!(
                expected_case.min_obligations, 0,
                "{} ({}) error evidence should not declare obligations",
                expected_case.case_id, expected_case.upstream_case_id
            );
            let expected_patterns = patterns_by_case
                .remove(&expected_case.case_id)
                .unwrap_or_else(|| {
                    panic!(
                        "{} ({}) should have expected_error_patterns metadata",
                        expected_case.case_id, expected_case.upstream_case_id
                    )
                });
            assert!(
                !expected_patterns.is_empty(),
                "{} ({}) expected_error_patterns should not be empty",
                expected_case.case_id,
                expected_case.upstream_case_id
            );
        } else {
            assert!(
                !patterns_by_case.contains_key(&expected_case.case_id),
                "{} ({}) non-error metadata should not declare expected_error_patterns",
                expected_case.case_id,
                expected_case.upstream_case_id
            );
        }
    }

    assert!(
        patterns_by_case.is_empty(),
        "expected_error_patterns should not contain orphan cases: {patterns_by_case:?}"
    );
}

#[test]
fn state_machines_rs_verified_subset_verifies_from_file() {
    let path = state_machines_port_path();
    let path = path
        .to_str()
        .expect("state_machines port path should be UTF-8");

    for (case, upstream_case) in VERIFIED_CASES {
        let result = verify_case(path, case, upstream_case);
        assert!(
            matches!(result, VerifyResult::Verified),
            "{case} ({upstream_case}) should verify, got: {result:?}"
        );
    }
}

#[test]
fn state_machines_rs_counterexample_subset_is_rejected_from_file() {
    let path = state_machines_port_path();
    let path = path
        .to_str()
        .expect("state_machines port path should be UTF-8");

    for (case, upstream_case) in COUNTEREXAMPLE_CASES {
        let result = verify_case(path, case, upstream_case);
        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "{case} ({upstream_case}) should produce a counterexample, got: {result:?}"
        );
    }
}

#[test]
fn state_machines_rs_macro_surfaces_fail_closed_from_file() {
    let path = state_machines_port_path();
    let path = path
        .to_str()
        .expect("state_machines port path should be UTF-8");

    for (case, upstream_case, expected_fragments) in FAIL_CLOSED_CASES {
        expect_fail_closed(path, case, upstream_case, expected_fragments);
    }
}
