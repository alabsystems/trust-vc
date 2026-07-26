// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Executable guards for the upstream hash.rs TrustVc scout slice.
//!
//! These tests intentionally do not claim full Verus hash.rs parity. They pin
//! exact std runtime behavior for HashMap/HashSet/DefaultHasher slices including
//! boxed, custom, string, and iterator variants; verify stable TrustVc Map/Set
//! view-model obligations; reject stable boolean witnesses for negative
//! collection facts; check direct std HashMap/HashSet view observations; pin the
//! upstream harness inventory; and keep std hash mutation/iterator/hasher
//! verifier surfaces fail-closed while the manifest remains
//! `unsupported-gap`.

#![allow(clippy::redundant_closure)]

mod common;

use std::{
    collections::BTreeMap,
    path::{Path, PathBuf},
};
use trust_vc_core::{verify_function_from_file, VerifyResult};

#[path = "../../../evals/verus/ported/hash.rs"]
mod hash_port;

fn hash_port_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/ported/hash.rs")
}

fn pinned_upstream_hash_path() -> PathBuf {
    common::pinned_verus_test_path("hash.rs")
}

fn verus_manifest_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/verus-tests.json")
}

fn active_upstream_cases(source: &str) -> Vec<String> {
    source
        .lines()
        .filter_map(|line| {
            let trimmed = line.trim();
            let rest = trimmed.strip_prefix("#[test] ")?;
            rest.split_whitespace().next().map(str::to_string)
        })
        .collect()
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

fn fail_closed_message(path: &str, case: &str, upstream_case: &str) -> String {
    match verify_function_from_file(path, case) {
        Err(err) => err.to_string(),
        Ok(VerifyResult::Error { message }) => message,
        Ok(other) => {
            panic!("{case} ({upstream_case}) should fail closed with Error, got: {other:?}")
        }
    }
}

fn assert_fail_closed(path: &str, case: &str, upstream_case: &str, expected_terms: &[&str]) {
    let message = fail_closed_message(path, case, upstream_case);
    assert!(
        expected_terms.iter().any(|term| message.contains(term)),
        "{case} ({upstream_case}) fail-closed error should identify one of {expected_terms:?}, got: {message}"
    );
}

const VERIFIED_CASES: &[(&str, &str)] = &[
    (
        "hash_map_view_model_insert_lookup_verified",
        "test_hash_map",
    ),
    (
        "hash_set_view_model_insert_membership_verified",
        "test_hash_set",
    ),
    ("hash_map_view_model_remove_verified", "test_hash_map"),
    (
        "hash_map_view_model_domain_values_verified",
        "test_hash_map_keys_values",
    ),
    ("hash_map_view_model_overwrite_verified", "test_hash_map"),
    (
        "hash_set_view_model_duplicate_insert_verified",
        "test_hash_set",
    ),
    ("std_hash_map_direct_view_verified", "test_hash_map"),
    ("std_hash_set_direct_view_verified", "test_hash_set"),
    (
        "std_hash_map_direct_view_key_guard_verified",
        "test_hash_map",
    ),
    (
        "std_hash_set_direct_view_member_guard_verified",
        "test_hash_set",
    ),
];

const COUNTEREXAMPLE_CASES: &[(&str, &str)] = &[
    (
        "hash_map_removed_key_boolean_witness_counterexample",
        "test_hash_map",
    ),
    (
        "hash_set_duplicate_insert_boolean_witness_counterexample",
        "test_hash_set",
    ),
];

const FAIL_CLOSED_CASES: &[(&str, &str, &[&str])] = &[
    (
        "std_hash_map_mutation_surface_fail_closed_error",
        "test_hash_map",
        &["unsupported method", "HashMap", "insert"],
    ),
    (
        "std_hash_set_mutation_surface_fail_closed_error",
        "test_hash_set",
        &[
            "unsupported method",
            "HashSet",
            "insert",
            "unresolved variable",
        ],
    ),
    (
        "hash_map_keys_iterator_surface_fail_closed_error",
        "test_hash_map_keys",
        &["unsupported", "for", "keys", "unresolved variable"],
    ),
    (
        "default_hasher_verifier_surface_fail_closed_error",
        "test_default_hasher",
        &[
            "unsupported",
            "DefaultHasher",
            "write",
            "finish",
            "unresolved variable",
        ],
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

fn port_expected_metadata() -> Vec<CaseMetadata> {
    let mut error_patterns = hash_port::hash_rs_expected_error_patterns()
        .iter()
        .map(|(case_id, patterns)| {
            (
                *case_id,
                patterns
                    .iter()
                    .map(|pattern| (*pattern).to_string())
                    .collect::<Vec<_>>(),
            )
        })
        .collect::<BTreeMap<_, _>>();

    let entries = hash_port::hash_rs_expected_cases()
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
        .collect::<Vec<_>>();

    assert!(
        error_patterns.is_empty(),
        "error-pattern metadata should not contain orphan cases: {error_patterns:?}"
    );
    entries
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
            entry["upstream_path"].as_str() == Some("source/rust_verify_test/tests/hash.rs")
        })
        .expect("Verus manifest should contain hash.rs row");

    row["expected_cases"]
        .as_array()
        .expect("hash.rs row should contain expected_cases")
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
            expected_error_patterns: case["expected_error_patterns"]
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
fn hash_rs_port_file_is_rust_syntax() {
    let source = std::fs::read_to_string(hash_port_path()).expect("hash port should be readable");
    syn::parse_file(&source).expect("hash port should parse as ordinary Rust syntax");
}

#[test]
fn hash_rs_runtime_std_subset_executes() {
    hash_port::test_default_hasher_runtime_equal_write_sequence();
    hash_port::test_hash_map_runtime_std_behavior();
    hash_port::test_hash_map_runtime_box_key_behavior();
    hash_port::test_hash_map_runtime_struct_key_behavior();
    hash_port::test_string_hash_map_runtime_std_behavior();
    hash_port::test_hash_map_runtime_keys_values_iter_behavior();
    hash_port::test_hash_set_runtime_std_behavior();
    hash_port::test_hash_set_runtime_box_key_behavior();
    hash_port::test_hash_set_runtime_struct_key_behavior();
    hash_port::test_string_hash_set_runtime_std_behavior();
    hash_port::test_hash_set_runtime_iter_behavior();
}

#[test]
fn hash_rs_runtime_wrong_std_witnesses_panic() {
    assert_panics(
        || hash_port::test_default_hasher_runtime_wrong_write_sequence_counterexample(),
        "wrong DefaultHasher write-order witness",
    );
    assert_panics(
        || hash_port::test_hash_map_runtime_wrong_removed_key_counterexample(),
        "wrong HashMap removed-key witness",
    );
    assert_panics(
        || hash_port::test_hash_map_runtime_wrong_box_removed_key_counterexample(),
        "wrong boxed-key HashMap removed-key witness",
    );
    assert_panics(
        || hash_port::test_hash_map_runtime_wrong_struct_lookup_counterexample(),
        "wrong custom-key HashMap lookup witness",
    );
    assert_panics(
        || hash_port::test_string_hash_map_runtime_wrong_removed_key_counterexample(),
        "wrong String-key HashMap removed-key witness",
    );
    assert_panics(
        || hash_port::test_hash_set_runtime_wrong_duplicate_insert_counterexample(),
        "wrong HashSet duplicate-insert witness",
    );
    assert_panics(
        || hash_port::test_hash_set_runtime_wrong_box_duplicate_insert_counterexample(),
        "wrong boxed-key HashSet duplicate-insert witness",
    );
    assert_panics(
        || hash_port::test_hash_set_runtime_wrong_struct_membership_counterexample(),
        "wrong custom-key HashSet membership witness",
    );
    assert_panics(
        || hash_port::test_string_hash_set_runtime_wrong_duplicate_insert_counterexample(),
        "wrong String-key HashSet duplicate-insert witness",
    );
}

#[test]
fn hash_rs_pinned_upstream_active_case_inventory_matches_port() {
    let path = pinned_upstream_hash_path();
    if !path.exists() {
        eprintln!(
            "skipping pinned upstream hash.rs inventory check; missing {}",
            path.display()
        );
        return;
    }

    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", path.display()));
    for expected_shape in [
        "assert(h1@ == Seq::<Seq<u8>>::empty())",
        "HashMap::<Box<u32>, i8>::new()",
        "HashSet::<Box<u32>>::new()",
        "assume(vstd::std_specs::hash::obeys_key_model::<MyStruct>())",
        "HashMapWithView::<MyStruct, u32>::new()",
        "StringHashMap::<i8>::new()",
        "StringHashSet::new()",
        "m.deep_view()[k]",
        "let m_keys = m.keys()",
        "let m_values = m.values()",
        "let m_iter = m.iter()",
        "pub enum Foo",
    ] {
        assert!(
            source.contains(expected_shape),
            "pinned upstream hash.rs should still contain {expected_shape}"
        );
    }

    let cases = active_upstream_cases(&source);
    let expected_cases = hash_port::upstream_hash_rs_active_cases()
        .iter()
        .map(|case| case.to_string())
        .collect::<Vec<_>>();
    assert_eq!(
        cases, expected_cases,
        "ported hash.rs case inventory must match active upstream harness cases"
    );
}

#[test]
fn hash_rs_expected_case_metadata_is_exact() {
    assert_eq!(
        hash_port::hash_rs_expected_cases(),
        &[
            (
                "hash_map_view_model_insert_lookup_verified",
                "test_hash_map",
                "verified",
                4,
            ),
            (
                "hash_set_view_model_insert_membership_verified",
                "test_hash_set",
                "verified",
                4,
            ),
            (
                "hash_map_view_model_remove_verified",
                "test_hash_map",
                "verified",
                2,
            ),
            (
                "hash_map_view_model_domain_values_verified",
                "test_hash_map_keys_values",
                "verified",
                4,
            ),
            (
                "hash_map_view_model_overwrite_verified",
                "test_hash_map",
                "verified",
                2,
            ),
            (
                "hash_set_view_model_duplicate_insert_verified",
                "test_hash_set",
                "verified",
                2,
            ),
            (
                "std_hash_map_direct_view_verified",
                "test_hash_map",
                "verified",
                1,
            ),
            (
                "std_hash_set_direct_view_verified",
                "test_hash_set",
                "verified",
                1,
            ),
            (
                "std_hash_map_direct_view_key_guard_verified",
                "test_hash_map",
                "verified",
                1,
            ),
            (
                "std_hash_set_direct_view_member_guard_verified",
                "test_hash_set",
                "verified",
                1,
            ),
            (
                "hash_map_removed_key_boolean_witness_counterexample",
                "test_hash_map",
                "counterexample",
                1,
            ),
            (
                "hash_set_duplicate_insert_boolean_witness_counterexample",
                "test_hash_set",
                "counterexample",
                1,
            ),
            (
                "std_hash_map_mutation_surface_fail_closed_error",
                "test_hash_map",
                "error",
                0,
            ),
            (
                "std_hash_set_mutation_surface_fail_closed_error",
                "test_hash_set",
                "error",
                0,
            ),
            (
                "hash_map_keys_iterator_surface_fail_closed_error",
                "test_hash_map_keys",
                "error",
                0,
            ),
            (
                "default_hasher_verifier_surface_fail_closed_error",
                "test_default_hasher",
                "error",
                0,
            ),
        ]
    );
    assert_eq!(
        hash_port::hash_rs_expected_error_patterns(),
        &[
            (
                "std_hash_map_mutation_surface_fail_closed_error",
                &["unsupported method", "HashMap", "insert"][..],
            ),
            (
                "std_hash_set_mutation_surface_fail_closed_error",
                &[
                    "unsupported method",
                    "HashSet",
                    "insert",
                    "unresolved variable",
                ][..],
            ),
            (
                "hash_map_keys_iterator_surface_fail_closed_error",
                &["unsupported", "for", "keys", "unresolved variable"][..],
            ),
            (
                "default_hasher_verifier_surface_fail_closed_error",
                &[
                    "unsupported",
                    "DefaultHasher",
                    "write",
                    "finish",
                    "unresolved variable",
                ][..],
            ),
        ]
    );
}

#[test]
fn hash_rs_expected_case_metadata_matches_manifest() {
    assert_eq!(
        port_expected_metadata(),
        manifest_expected_metadata(),
        "hash.rs manifest expected_cases should match port metadata and fail-closed patterns exactly"
    );
}

#[test]
fn hash_rs_verified_subset_verifies_from_file() {
    let path = hash_port_path();
    let path = path.to_str().expect("hash port path should be UTF-8");

    for (case, upstream_case) in VERIFIED_CASES {
        let result = verify_case(path, case, upstream_case);
        assert!(
            matches!(result, VerifyResult::Verified),
            "{case} ({upstream_case}) should verify, got: {result:?}"
        );
    }
}

#[test]
fn hash_rs_counterexample_subset_is_rejected_from_file() {
    let path = hash_port_path();
    let path = path.to_str().expect("hash port path should be UTF-8");

    for (case, upstream_case) in COUNTEREXAMPLE_CASES {
        let result = verify_case(path, case, upstream_case);
        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "{case} ({upstream_case}) should be rejected, got: {result:?}"
        );
    }
}

#[test]
fn hash_rs_unsupported_std_hash_boundaries_fail_closed_from_file() {
    let path = hash_port_path();
    let path = path.to_str().expect("hash port path should be UTF-8");

    for (case, upstream_case, expected_terms) in FAIL_CLOSED_CASES {
        assert_fail_closed(path, case, upstream_case, expected_terms);
    }
}
