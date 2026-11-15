// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Executable guards for the first upstream eq_cmp.rs TrustVc scout slice.
//!
//! These tests intentionally keep `source/rust_verify_test/tests/eq_cmp.rs`
//! fail-closed in the manifest. They prove only the Rust-valid subset TrustVc can
//! express today: operator-backed primitive comparisons, derived structural
//! equality, primitive PartialOrd::{lt, gt} method calls, a concrete
//! order-to-equality helper, primitive branch witnesses, concrete Option
//! equality and finite-integer PartialOrd witnesses, false
//! primitive/helper/structural/order probes from the upstream law-oriented
//! test, concrete custom-PartialEq operator coverage, and stable
//! expected_error_patterns for the remaining generic/direct-PartialEq
//! fail-closed boundaries.

mod common;

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use trust_vc_core::{verify_function_from_file, VerifyResult};

#[path = "../../../evals/verus/ported/eq_cmp.rs"]
mod eq_cmp_port;

type ExpectedErrorPatterns = (&'static str, &'static [&'static str]);

fn eq_cmp_port_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/ported/eq_cmp.rs")
}

fn verus_manifest_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/verus-tests.json")
}

fn pinned_upstream_eq_cmp_path() -> PathBuf {
    common::pinned_verus_test_path("eq_cmp.rs")
}

fn verify_case(path: &str, case: &str, upstream_case: &str) -> VerifyResult {
    verify_function_from_file(path, case)
        .unwrap_or_else(|err| panic!("{case} ({upstream_case}) should extract: {err}"))
}

const VERIFIED_CASES: &[(&str, &str)] = &[
    (
        "eq_cmp_structural_equality_and_primitive_order_verified",
        "eq_cmp1",
    ),
    ("eq_cmp_partial_ord_lt_method_verified", "eq_cmp1"),
    ("eq_cmp_partial_ord_gt_method_verified", "eq_cmp1"),
    ("eq_cmp_u8_order_to_eq_helper_verified", "eq_cmp1::test_eq"),
    (
        "eq_cmp_u8_order_to_eq_helper_call_verified",
        "eq_cmp1::test",
    ),
    ("eq_cmp_primitive_order_branch_equality_verified", "eq_cmp1"),
    ("eq_cmp_option_equality_witnesses_verified", "eq_cmp1"),
    (
        "eq_cmp_option_partial_ord_method_verified",
        "eq_cmp1::test_eq<Option<u8>>",
    ),
    ("eq_cmp_option_order_to_eq_helper_verified", "eq_cmp1::test"),
    ("eq_cmp_structural_tuple_operator_verified", "eq_cmp1"),
    // 2026-09-11: `.eq()` method calls — derived (check_eq) and hand-written (test_p_eq) PartialEq — verify.
    (
        "eq_cmp_structural_tuple_eq_method_verified",
        "eq_cmp1::check_eq",
    ),
    (
        "eq_cmp_custom_partial_eq_method_verified",
        "eq_cmp1::test_p_eq",
    ),
    // 2026-09-11: the `!=` OPERATOR on a hand-written PartialEq lowers to the impl's eq (upstream test_p_ee).
    (
        "eq_cmp_custom_partial_eq_operator_verified",
        "eq_cmp1::test_p_ee",
    ),
];

const COUNTEREXAMPLE_CASES: &[(&str, &str)] = &[
    ("eq_cmp_literal_order_counterexample", "eq_cmp1"),
    ("eq_cmp_partial_ord_gt_method_counterexample", "eq_cmp1"),
    (
        "eq_cmp_primitive_order_wrong_branch_counterexample",
        "eq_cmp1::test_eq_wrong",
    ),
    (
        "eq_cmp_structural_tuple_eq_method_liar_counterexample",
        "eq_cmp1::check_eq",
    ),
    (
        "eq_cmp_custom_partial_eq_method_liar_counterexample",
        "eq_cmp1::test_p_eq",
    ),
    (
        "eq_cmp_custom_partial_eq_operator_liar_counterexample",
        "eq_cmp1::test_p_ee",
    ),
];

const FAIL_CLOSED_CASES: &[(&str, &str, &[&str])] = &[];

fn expected_error_patterns_from_fail_closed_cases() -> Vec<ExpectedErrorPatterns> {
    FAIL_CLOSED_CASES
        .iter()
        .map(|&(case, _, patterns)| (case, patterns))
        .collect()
}

#[derive(Debug, Eq, PartialEq)]
struct CaseMetadata {
    case_id: String,
    upstream_case_id: String,
    expected_verdict: String,
    min_obligations: usize,
    expected_error_patterns: Vec<String>,
}

fn port_expected_metadata() -> Vec<CaseMetadata> {
    let patterns_by_case: BTreeMap<&str, &[&str]> =
        eq_cmp_port::eq_cmp_rs_expected_error_patterns()
            .iter()
            .copied()
            .collect();

    eq_cmp_port::eq_cmp_rs_expected_cases()
        .iter()
        .map(
            |(case_id, upstream_case_id, expected_verdict, min_obligations)| CaseMetadata {
                case_id: (*case_id).to_string(),
                upstream_case_id: (*upstream_case_id).to_string(),
                expected_verdict: (*expected_verdict).to_string(),
                min_obligations: *min_obligations,
                expected_error_patterns: patterns_by_case
                    .get(case_id)
                    .map(|patterns| {
                        patterns
                            .iter()
                            .map(|pattern| (*pattern).to_string())
                            .collect()
                    })
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
            entry["upstream_path"].as_str() == Some("source/rust_verify_test/tests/eq_cmp.rs")
        })
        .expect("Verus manifest should contain eq_cmp.rs row");

    row["expected_cases"]
        .as_array()
        .expect("eq_cmp.rs row should contain expected_cases")
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

fn expect_error_contains_all(
    path: &str,
    case: &str,
    upstream_case: &str,
    expected_fragments: &[&str],
) {
    let message = match verify_function_from_file(path, case) {
        Err(err) => err.to_string(),
        Ok(VerifyResult::Error { message }) => message,
        Ok(VerifyResult::Unknown { reason, .. }) => {
            panic!("{case} ({upstream_case}) returned solver Unknown, which is not stable evidence: {reason}")
        }
        Ok(other) => {
            panic!("{case} ({upstream_case}) should fail closed with Error, got: {other:?}")
        }
    };

    for expected_fragment in expected_fragments {
        assert!(
            message.contains(expected_fragment),
            "{case} ({upstream_case}) error should contain {expected_fragment:?}, got: {message}"
        );
    }
}

#[test]
fn eq_cmp_rs_port_file_is_rust_syntax() {
    let source =
        std::fs::read_to_string(eq_cmp_port_path()).expect("eq_cmp port should be readable");
    syn::parse_file(&source).expect("eq_cmp port should parse as ordinary Rust syntax");
}

#[test]
fn eq_cmp_rs_pinned_upstream_case_shape_is_present() {
    let path = pinned_upstream_eq_cmp_path();
    if !path.exists() {
        eprintln!(
            "skipping pinned upstream eq_cmp.rs shape check; missing {}",
            path.display()
        );
        return;
    }

    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", path.display()));
    for expected in [
        "#[test] eq_cmp1",
        "fn test_eq<T: Ord>",
        "fn test_eq_wrong<T: Ord>",
        "struct P(u8, bool)",
        "struct S(u8, bool)",
    ] {
        assert!(
            source.contains(expected),
            "pinned upstream eq_cmp.rs should still contain {expected}"
        );
    }
}

#[test]
fn eq_cmp_rs_expected_case_metadata_is_exact() {
    assert_eq!(
        eq_cmp_port::eq_cmp_rs_expected_cases(),
        &[
            (
                "eq_cmp_structural_equality_and_primitive_order_verified",
                "eq_cmp1",
                "verified",
                6,
            ),
            (
                "eq_cmp_literal_order_counterexample",
                "eq_cmp1",
                "counterexample",
                1,
            ),
            (
                "eq_cmp_partial_ord_lt_method_verified",
                "eq_cmp1",
                "verified",
                1,
            ),
            (
                "eq_cmp_partial_ord_gt_method_verified",
                "eq_cmp1",
                "verified",
                1,
            ),
            (
                "eq_cmp_partial_ord_gt_method_counterexample",
                "eq_cmp1",
                "counterexample",
                1,
            ),
            (
                "eq_cmp_u8_order_to_eq_helper_verified",
                "eq_cmp1::test_eq",
                "verified",
                1,
            ),
            (
                "eq_cmp_u8_order_to_eq_helper_call_verified",
                "eq_cmp1::test",
                "verified",
                1,
            ),
            (
                "eq_cmp_primitive_order_branch_equality_verified",
                "eq_cmp1",
                "verified",
                1,
            ),
            (
                "eq_cmp_primitive_order_wrong_branch_counterexample",
                "eq_cmp1::test_eq_wrong",
                "counterexample",
                1,
            ),
            (
                "eq_cmp_option_equality_witnesses_verified",
                "eq_cmp1",
                "verified",
                2,
            ),
            (
                "eq_cmp_structural_tuple_operator_verified",
                "eq_cmp1",
                "verified",
                2,
            ),
            (
                "eq_cmp_structural_tuple_eq_method_verified",
                "eq_cmp1::check_eq",
                "verified",
                3,
            ),
            (
                "eq_cmp_structural_tuple_eq_method_liar_counterexample",
                "eq_cmp1::check_eq",
                "counterexample",
                2,
            ),
            (
                "eq_cmp_option_partial_ord_method_verified",
                "eq_cmp1::test_eq<Option<u8>>",
                "verified",
                1,
            ),
            (
                "eq_cmp_option_order_to_eq_helper_verified",
                "eq_cmp1::test",
                "verified",
                1,
            ),
            (
                "eq_cmp_custom_partial_eq_method_verified",
                "eq_cmp1::test_p_eq",
                "verified",
                2,
            ),
            (
                "eq_cmp_custom_partial_eq_method_liar_counterexample",
                "eq_cmp1::test_p_eq",
                "counterexample",
                2,
            ),
            (
                "eq_cmp_custom_partial_eq_operator_verified",
                "eq_cmp1::test_p_ee",
                "verified",
                1,
            ),
            (
                "eq_cmp_custom_partial_eq_operator_liar_counterexample",
                "eq_cmp1::test_p_ee",
                "counterexample",
                1,
            ),
        ]
    );
}

#[test]
fn eq_cmp_rs_expected_error_pattern_metadata_is_exact() {
    let expected = expected_error_patterns_from_fail_closed_cases();
    assert_eq!(eq_cmp_port::eq_cmp_rs_expected_error_patterns(), expected);
}

#[test]
fn eq_cmp_rs_expected_case_metadata_matches_manifest() {
    assert_eq!(port_expected_metadata(), manifest_expected_metadata());
}

#[test]
fn eq_cmp_rs_error_cases_have_expected_error_patterns() {
    let mut patterns_by_case: BTreeMap<&str, &[&str]> =
        eq_cmp_port::eq_cmp_rs_expected_error_patterns()
            .iter()
            .copied()
            .collect();

    for expected_case in eq_cmp_port::eq_cmp_rs_expected_cases() {
        let (case, upstream_case, verdict, min_obligations) = *expected_case;
        if verdict == "error" {
            assert_eq!(
                min_obligations, 0,
                "{case} ({upstream_case}) error evidence should not declare obligations"
            );
            let expected_patterns = patterns_by_case.remove(case).unwrap_or_else(|| {
                panic!("{case} ({upstream_case}) should declare expected_error_patterns")
            });
            assert!(
                !expected_patterns.is_empty(),
                "{case} ({upstream_case}) should declare at least one expected_error_patterns value"
            );
            for expected_pattern in expected_patterns {
                assert!(
                    !expected_pattern.trim().is_empty(),
                    "{case} ({upstream_case}) declares an empty expected_error_patterns value"
                );
            }
        } else {
            assert!(
                !patterns_by_case.contains_key(case),
                "{case} ({upstream_case}) should not declare expected_error_patterns for {verdict} evidence"
            );
        }
    }

    assert!(
        patterns_by_case.is_empty(),
        "expected_error_patterns metadata should not contain orphan cases: {patterns_by_case:?}"
    );
}

#[test]
fn eq_cmp_rs_verified_subset_verifies_from_file() {
    let path = eq_cmp_port_path();
    let path = path.to_str().expect("eq_cmp port path should be UTF-8");

    for (case, upstream_case) in VERIFIED_CASES {
        let result = verify_case(path, case, upstream_case);
        assert!(
            matches!(result, VerifyResult::Verified),
            "{case} ({upstream_case}) should verify, got: {result:?}"
        );
    }
}

#[test]
fn eq_cmp_rs_custom_partial_eq_boundary_fails_closed_from_file() {
    let path = eq_cmp_port_path();
    let path = path.to_str().expect("eq_cmp port path should be UTF-8");

    for (case, upstream_case, expected_fragments) in FAIL_CLOSED_CASES {
        expect_error_contains_all(path, case, upstream_case, expected_fragments);
    }
}

#[test]
fn eq_cmp_rs_counterexample_subset_is_rejected_from_file() {
    let path = eq_cmp_port_path();
    let path = path.to_str().expect("eq_cmp port path should be UTF-8");

    for (case, upstream_case) in COUNTEREXAMPLE_CASES {
        let result = verify_case(path, case, upstream_case);
        eprintln!("{case} ({upstream_case}) => {result:?}");
        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "{case} ({upstream_case}) should produce a counterexample, got: {result:?}"
        );
    }
}
