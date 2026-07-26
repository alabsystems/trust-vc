// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Executable guards for the first upstream summer_school.rs TrustVc scout slice.
//!
//! These tests intentionally keep upstream summer_school.rs as an unsupported
//! gap. They prove only stable assertion/spec-function/Set-model witnesses
//! plus a small `set!` smoke test, and reject adjacent false claims with
//! concrete counterexamples.

mod common;

use std::{
    collections::BTreeSet,
    path::{Path, PathBuf},
};
use trust_vc_core::{verify_function_from_file, VerifyResult};

fn summer_school_port_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/ported/summer_school.rs")
}

fn verus_manifest_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/verus-tests.json")
}

fn pinned_upstream_summer_school_path() -> PathBuf {
    common::pinned_verus_test_path("summer_school.rs")
}

fn verify_case(path: &str, case: &str, upstream_case: &str) -> VerifyResult {
    verify_function_from_file(path, case)
        .unwrap_or_else(|err| panic!("{case} ({upstream_case}) should extract: {err}"))
}

const VERIFIED_CASES: &[(&str, &str)] = &[
    ("e01_assertion_verified", "e01_pass"),
    ("e02_implication_verified", "e02_pass"),
    ("e03_double_literal_arithmetic_verified", "e03_pass"),
    ("e04_four_times_nonnegative_verified", "e04_pass"),
    ("e05_set_membership_model_verified", "e05_pass"),
    ("e05_verus_set_literal_macro_verified", "e05_pass"),
];

const COUNTEREXAMPLE_CASES: &[(&str, &str)] = &[
    ("e01_assertion_counterexample", "e01_fail"),
    ("e02_implication_counterexample", "e02_fail"),
    ("e03_double_wrong_literal_counterexample", "e03_fail"),
    ("e04_four_times_unconstrained_counterexample", "e04_fail"),
    (
        "e05_set_membership_false_followup_counterexample",
        "e05_fail",
    ),
];

const EXPECTED_CASES: &[(&str, &str, &str, usize)] = &[
    ("e01_assertion_verified", "e01_pass", "verified", 1),
    (
        "e01_assertion_counterexample",
        "e01_fail",
        "counterexample",
        1,
    ),
    ("e02_implication_verified", "e02_pass", "verified", 1),
    (
        "e02_implication_counterexample",
        "e02_fail",
        "counterexample",
        1,
    ),
    (
        "e03_double_literal_arithmetic_verified",
        "e03_pass",
        "verified",
        1,
    ),
    (
        "e03_double_wrong_literal_counterexample",
        "e03_fail",
        "counterexample",
        1,
    ),
    (
        "e04_four_times_nonnegative_verified",
        "e04_pass",
        "verified",
        1,
    ),
    (
        "e04_four_times_unconstrained_counterexample",
        "e04_fail",
        "counterexample",
        1,
    ),
    (
        "e05_set_membership_model_verified",
        "e05_pass",
        "verified",
        1,
    ),
    (
        "e05_set_membership_false_followup_counterexample",
        "e05_fail",
        "counterexample",
        1,
    ),
    (
        "e05_verus_set_literal_macro_verified",
        "e05_pass",
        "verified",
        1,
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
        .unwrap_or_else(|| panic!("summer_school port should define {const_name}"));

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
    let array = referenced_array_const(file, "SUMMER_SCHOOL_RS_EXPECTED_CASES");
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
            "duplicate summer_school metadata for {case_id}"
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
                == Some("source/rust_verify_test/tests/summer_school.rs")
        })
        .expect("Verus manifest should contain summer_school.rs row");

    row["expected_cases"]
        .as_array()
        .expect("summer_school.rs row should contain expected_cases")
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
        })
        .collect()
}

#[test]
fn summer_school_rs_expected_case_metadata_is_exact() {
    let source = std::fs::read_to_string(summer_school_port_path())
        .expect("summer_school port should be readable");
    let file =
        syn::parse_file(&source).expect("summer_school port should parse as ordinary Rust syntax");
    assert_eq!(metadata_entries(&file), expected_metadata());
}

#[test]
fn summer_school_rs_expected_case_metadata_matches_manifest() {
    let source = std::fs::read_to_string(summer_school_port_path())
        .expect("summer_school port should be readable");
    let file =
        syn::parse_file(&source).expect("summer_school port should parse as ordinary Rust syntax");
    assert_eq!(metadata_entries(&file), manifest_expected_metadata());
}

#[test]
fn summer_school_rs_port_file_is_rust_syntax() {
    let source = std::fs::read_to_string(summer_school_port_path())
        .expect("summer_school port should be readable");
    syn::parse_file(&source).expect("summer_school port should parse as ordinary Rust syntax");
}

#[test]
fn summer_school_rs_pinned_upstream_case_shapes_are_present() {
    let path = pinned_upstream_summer_school_path();
    if !path.exists() {
        eprintln!(
            "skipping pinned upstream summer_school.rs shape check; missing {}",
            path.display()
        );
        return;
    }

    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", path.display()));
    for expected in [
        "#[test] e01_pass",
        "#[test] e01_fail",
        "#[test] e02_pass",
        "#[test] e02_fail",
        "#[test] e03_pass",
        "#[test] e03_fail",
        "#[test] e04_pass",
        "#[test] e04_fail",
        "#[test] e05_pass",
        "#[test] e05_fail",
        "set![7, 6, 5]",
        "set![7, 9]",
    ] {
        assert!(
            source.contains(expected),
            "pinned upstream summer_school.rs should still contain {expected}"
        );
    }
}

#[test]
fn summer_school_rs_verified_subset_verifies_from_file() {
    let path = summer_school_port_path();
    let path = path
        .to_str()
        .expect("summer_school port path should be UTF-8");

    for (case, upstream_case) in VERIFIED_CASES {
        let result = verify_case(path, case, upstream_case);
        assert!(
            matches!(result, VerifyResult::Verified),
            "{case} ({upstream_case}) should verify, got: {result:?}"
        );
    }
}

#[test]
fn summer_school_rs_counterexample_subset_is_rejected_from_file() {
    let path = summer_school_port_path();
    let path = path
        .to_str()
        .expect("summer_school port path should be UTF-8");

    for (case, upstream_case) in COUNTEREXAMPLE_CASES {
        let result = verify_case(path, case, upstream_case);
        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "{case} ({upstream_case}) should be rejected, got: {result:?}"
        );
    }
}
