// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Executable guards for the upstream-derived `sets.rs` TrustVc port.

use std::{
    collections::{BTreeMap, BTreeSet},
    path::PathBuf,
};
use trust_vc_core::{verify_function_from_file, VerifyResult};

fn sets_port_path() -> PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/ported/sets.rs")
}

fn verus_manifest_path() -> PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/verus-tests.json")
}

fn verify_case(path: &str, case: &str) -> VerifyResult {
    verify_function_from_file(path, case)
        .unwrap_or_else(|err| panic!("{case} should extract from sets.rs: {err}"))
}

const EXPECTED_CASES: &[(&str, &str, &str, usize)] = &[
    ("test_len", "test_len", "verified", 1),
    ("test_len_fails", "test_len_fails", "counterexample", 1),
    ("test_set_fold_singleton", "test_set_fold", "verified", 1),
    ("test_set_fold_empty", "test_set_fold", "verified", 1),
    (
        "test_set_fold_two_insert_sum",
        "test_set_fold",
        "verified",
        1,
    ),
    (
        "test_set_fold_collection_accumulator_fail_closed",
        "test_set_fold",
        "error",
        0,
    ),
    (
        "test1_filter_preserves_positive_member",
        "test1",
        "verified",
        1,
    ),
    ("test1_set_new_empty_alias_boundary", "test1", "verified", 1),
    (
        "test1_filter_excludes_nonpositive_member",
        "test1",
        "verified",
        1,
    ),
    (
        "test1_map_forward_image_contains_successor",
        "test1",
        "verified",
        1,
    ),
    (
        "test1_finite_insert_order_extensionality",
        "test1",
        "verified",
        1,
    ),
    (
        "test_choose_assert_witness",
        "test_choose_assert_witness",
        "verified",
        1,
    ),
    (
        "test_choose_fails_witness",
        "test_choose_fails_witness",
        "counterexample",
        1,
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
        .unwrap_or_else(|| panic!("sets port should define {const_name}"));

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

fn pattern_entries(file: &syn::File) -> BTreeMap<String, Vec<String>> {
    let array = referenced_array_const(file, "SETS_RS_FAIL_CLOSED_ERROR_PATTERNS");
    let mut entries = BTreeMap::new();

    for entry in &array.elems {
        let syn::Expr::Tuple(tuple) = entry else {
            panic!("expected tuple fail-closed pattern metadata entry");
        };
        assert_eq!(
            tuple.elems.len(),
            2,
            "fail-closed pattern entries should have case and fragments"
        );
        let case_id = literal_string(&tuple.elems[0]);
        let syn::Expr::Reference(patterns_reference) = &tuple.elems[1] else {
            panic!("fail-closed patterns should be a referenced array");
        };
        let syn::Expr::Array(patterns_array) = patterns_reference.expr.as_ref() else {
            panic!("fail-closed patterns should reference an array");
        };
        let previous = entries.insert(
            case_id.clone(),
            patterns_array.elems.iter().map(literal_string).collect(),
        );
        assert!(previous.is_none(), "duplicate sets patterns for {case_id}");
    }

    entries
}

fn metadata_entries(file: &syn::File) -> Vec<CaseMetadata> {
    let array = referenced_array_const(file, "SETS_RS_EXPECTED_CASES");
    let patterns = pattern_entries(file);
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
            "duplicate sets metadata for {case_id}"
        );
        let expected_error_patterns = patterns.get(&case_id).cloned().unwrap_or_default();
        entries.push(CaseMetadata {
            case_id,
            upstream_case_id: literal_string(&tuple.elems[1]),
            expected_verdict: literal_string(&tuple.elems[2]),
            min_obligations: literal_usize(&tuple.elems[3]),
            expected_error_patterns,
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
                expected_error_patterns: if *case_id
                    == "test_set_fold_collection_accumulator_fail_closed"
                {
                    vec![
                        "Set::fold currently supports non-collection accumulator/result types only"
                            .to_string(),
                    ]
                } else {
                    Vec::new()
                },
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
            entry["upstream_path"].as_str() == Some("source/rust_verify_test/tests/sets.rs")
        })
        .expect("Verus manifest should contain sets.rs row");

    row["expected_cases"]
        .as_array()
        .expect("sets.rs row should contain expected_cases")
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
fn sets_rs_expected_case_metadata_is_exact() {
    let source = std::fs::read_to_string(sets_port_path()).expect("sets port should be readable");
    let file = syn::parse_file(&source).expect("sets port should parse as ordinary Rust syntax");
    assert_eq!(metadata_entries(&file), expected_metadata());
}

#[test]
fn sets_rs_expected_case_metadata_matches_manifest() {
    let source = std::fs::read_to_string(sets_port_path()).expect("sets port should be readable");
    let file = syn::parse_file(&source).expect("sets port should parse as ordinary Rust syntax");
    assert_eq!(metadata_entries(&file), manifest_expected_metadata());
}

#[test]
fn sets_rs_verified_subset_verifies_from_file() {
    let path = sets_port_path();
    let path = path.to_str().expect("sets port path should be UTF-8");

    for (case, _, _, _) in EXPECTED_CASES
        .iter()
        .filter(|(_, _, verdict, _)| *verdict == "verified")
    {
        let result = verify_case(path, case);
        assert!(
            matches!(result, VerifyResult::Verified),
            "{case} should verify, got {result:?}"
        );
    }
}

#[test]
fn sets_rs_negative_subset_is_rejected_from_file() {
    let path = sets_port_path();
    let path = path.to_str().expect("sets port path should be UTF-8");

    for (case, _, _, _) in EXPECTED_CASES
        .iter()
        .filter(|(_, _, verdict, _)| *verdict == "counterexample")
    {
        let result = verify_case(path, case);
        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "{case} should be rejected, got {result:?}"
        );
    }
}

#[test]
fn sets_rs_fail_closed_guards_are_rejected_from_file() {
    let path = sets_port_path();
    let path = path.to_str().expect("sets port path should be UTF-8");

    for (case, _, _, _) in EXPECTED_CASES
        .iter()
        .filter(|(_, _, verdict, _)| *verdict == "error")
    {
        let result = verify_case(path, case);
        match result {
            VerifyResult::Error { message } => {
                let source = std::fs::read_to_string(sets_port_path())
                    .expect("sets port should be readable");
                let file = syn::parse_file(&source)
                    .expect("sets port should parse as ordinary Rust syntax");
                let patterns = pattern_entries(&file);
                let expected_patterns = patterns
                    .get(*case)
                    .unwrap_or_else(|| panic!("{case} should have fail-closed pattern metadata"));
                assert!(
                    expected_patterns
                        .iter()
                        .any(|expected_pattern| message.contains(expected_pattern)),
                    "{case} should explain the Set::fold collection accumulator guard, got {message:?}"
                );
            }
            other => panic!("{case} should fail closed with Error, got {other:?}"),
        }
    }
}
