// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Executable guards for the first upstream btree.rs TrustVc scout slice.
//!
//! These tests intentionally do not claim full Verus btree.rs parity. They pin
//! exact std runtime behavior for a small BTreeMap/BTreeSet slice, verify stable
//! TrustVc Map/Set view-model obligations, and verify direct std BTreeMap/BTreeSet
//! view observations while the manifest remains `unsupported-gap`.

mod common;

use std::{
    collections::BTreeSet,
    path::{Path, PathBuf},
};
use trust_vc_core::{verify_function_from_file, VerifyResult};

#[path = "../../../evals/verus/ported/btree.rs"]
mod btree_port;

fn btree_port_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/ported/btree.rs")
}

fn verus_manifest_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/verus-tests.json")
}

fn pinned_upstream_btree_path() -> PathBuf {
    common::pinned_verus_test_path("btree.rs")
}

fn assert_panics(f: impl FnOnce() + std::panic::UnwindSafe, label: &str) {
    let previous_hook = std::panic::take_hook();
    std::panic::set_hook(Box::new(|_| {}));
    let result = std::panic::catch_unwind(f);
    std::panic::set_hook(previous_hook);
    assert!(result.is_err(), "{label} should panic at runtime");
}

fn verify_case(path: &str, case: &str, upstream_case: &str) -> VerifyResult {
    verify_function_from_file(path, case)
        .unwrap_or_else(|err| panic!("{case} ({upstream_case}) should extract: {err}"))
}

const VERIFIED_CASES: &[(&str, &str)] = &[
    (
        "btree_map_view_model_insert_lookup_verified",
        "test_btree_map",
    ),
    (
        "btree_set_view_model_insert_membership_verified",
        "test_btree_set",
    ),
    ("std_btree_map_direct_view_verified", "test_btree_map"),
    ("std_btree_set_direct_view_verified", "test_btree_set"),
];

const COUNTEREXAMPLE_CASES: &[(&str, &str)] = &[
    (
        "btree_map_view_model_wrong_lookup_counterexample",
        "test_btree_map",
    ),
    (
        "btree_set_view_model_wrong_membership_counterexample",
        "test_btree_set",
    ),
];

const EXPECTED_CASES: &[(&str, &str, &str, usize)] = &[
    (
        "btree_map_view_model_insert_lookup_verified",
        "test_btree_map",
        "verified",
        4,
    ),
    (
        "btree_set_view_model_insert_membership_verified",
        "test_btree_set",
        "verified",
        4,
    ),
    (
        "btree_map_view_model_wrong_lookup_counterexample",
        "test_btree_map",
        "counterexample",
        1,
    ),
    (
        "btree_set_view_model_wrong_membership_counterexample",
        "test_btree_set",
        "counterexample",
        1,
    ),
    (
        "std_btree_map_direct_view_verified",
        "test_btree_map",
        "verified",
        1,
    ),
    (
        "std_btree_set_direct_view_verified",
        "test_btree_set",
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
        .unwrap_or_else(|| panic!("btree port should define {const_name}"));

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
    let array = referenced_array_const(file, "BTREE_RS_EXPECTED_CASES");
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
            "duplicate btree metadata for {case_id}"
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
            entry["upstream_path"].as_str() == Some("source/rust_verify_test/tests/btree.rs")
        })
        .expect("Verus manifest should contain btree.rs row");

    row["expected_cases"]
        .as_array()
        .expect("btree.rs row should contain expected_cases")
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
fn btree_rs_port_file_is_rust_syntax() {
    let source = std::fs::read_to_string(btree_port_path()).expect("btree port should be readable");
    syn::parse_file(&source).expect("btree port should parse as ordinary Rust syntax");
}

#[test]
fn btree_rs_runtime_std_subset_executes() {
    btree_port::test_btree_map_runtime_std_behavior();
    btree_port::test_btree_set_runtime_std_behavior();
}

#[test]
fn btree_rs_runtime_wrong_std_witnesses_panic() {
    assert_panics(
        btree_port::test_btree_map_runtime_wrong_removed_key_counterexample,
        "wrong BTreeMap removed-key witness",
    );
    assert_panics(
        btree_port::test_btree_set_runtime_wrong_duplicate_insert_counterexample,
        "wrong BTreeSet duplicate-insert witness",
    );
}

#[test]
fn btree_rs_pinned_upstream_case_shapes_are_present() {
    let path = pinned_upstream_btree_path();
    if !path.exists() {
        eprintln!(
            "skipping pinned upstream btree.rs shape check; missing {}",
            path.display()
        );
        return;
    }

    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", path.display()));
    for expected in [
        "test_btree_map",
        "test_btree_set",
        "test_btree_map_struct",
        "test_btree_set_struct",
        "test_btree_map_deep_view",
        "test_btree_map_keys",
        "test_btree_map_values",
        "test_btree_map_decreases",
    ] {
        assert!(
            source.contains(expected),
            "pinned upstream btree.rs should still contain {expected}"
        );
    }
}

#[test]
fn btree_rs_expected_case_metadata_is_exact() {
    let source = std::fs::read_to_string(btree_port_path()).expect("btree port should be readable");
    let file = syn::parse_file(&source).expect("btree port should parse as ordinary Rust syntax");
    assert_eq!(metadata_entries(&file), expected_metadata());
    assert_eq!(btree_port::btree_rs_expected_cases(), EXPECTED_CASES);
}

#[test]
fn btree_rs_expected_case_metadata_matches_manifest() {
    let source = std::fs::read_to_string(btree_port_path()).expect("btree port should be readable");
    let file = syn::parse_file(&source).expect("btree port should parse as ordinary Rust syntax");
    assert_eq!(metadata_entries(&file), manifest_expected_metadata());
}

#[test]
fn btree_rs_verified_subset_verifies_from_file() {
    let path = btree_port_path();
    let path = path.to_str().expect("btree port path should be UTF-8");

    for (case, upstream_case) in VERIFIED_CASES {
        let result = verify_case(path, case, upstream_case);
        assert!(
            matches!(result, VerifyResult::Verified),
            "{case} ({upstream_case}) should verify, got: {result:?}"
        );
    }
}

#[test]
fn btree_rs_counterexample_subset_is_rejected_from_file() {
    let path = btree_port_path();
    let path = path.to_str().expect("btree port path should be UTF-8");

    for (case, upstream_case) in COUNTEREXAMPLE_CASES {
        let result = verify_case(path, case, upstream_case);
        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "{case} ({upstream_case}) should be rejected, got: {result:?}"
        );
    }
}
