// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Executable guards for the faithful upstream-derived `multiset.rs` TrustVc port.
//!
//! The port reproduces all five upstream `test_verify_one_file!` cases verbatim
//! through the Multiset surface:
//!   * `multiset_basics` => Ok(()) — eight proof fns, all verify.
//!   * `multiset_fail` / `multiset_fail2` / `multiset_fail3` / `multiset_fail4`
//!     => `assert_one_fails` — genuine counterexamples (no surrogate verdicts).
//!
//! These guards (a) verify every annotated function from the port file with the
//! upstream-expected verdict, and (b) hold the port and the Verus manifest row in
//! lockstep so the accepted corpus evidence cannot silently drift.

use std::{collections::BTreeSet, path::PathBuf};
use trust_vc_core::{verify_function_from_file, VerifyResult};

fn port_path() -> PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/ported/multiset.rs")
}

fn verus_manifest_path() -> PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/verus-tests.json")
}

/// The eight upstream `multiset_basics` proof fns (case_id -> upstream_case_id).
/// All carry `upstream_case_id = multiset_basics` and verify.
const VERIFIED_CASES: &[&str] = &[
    "commutative",
    "associative",
    "insert2",
    "insert2_count",
    "add_sub_cancel",
    "sub_add_cancel",
    "choose_count",
    "len_is_zero_if_count_for_each_value_is_zero",
];

/// The four upstream `*_fail` proof fns, each a genuine counterexample.
/// (case_id == upstream_case_id for these.)
const COUNTEREXAMPLE_CASES: &[&str] = &[
    "multiset_fail",
    "multiset_fail2",
    "multiset_fail3",
    "multiset_fail4",
];

fn verify_case(path: &str, case: &str) -> VerifyResult {
    verify_function_from_file(path, case)
        .unwrap_or_else(|err| panic!("{case} should extract from multiset.rs: {err}"))
}

fn assert_verified(path: &str, case: &str) {
    let result = verify_case(path, case);
    assert!(
        matches!(result, VerifyResult::Verified),
        "{case} should verify, got {result:?}"
    );
}

fn assert_counterexample(path: &str, case: &str) {
    let result = verify_case(path, case);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "{case} should be a genuine counterexample, got {result:?}"
    );
}

#[derive(Debug, Eq, PartialEq, Ord, PartialOrd)]
struct CaseMetadata {
    case_id: String,
    upstream_case_id: String,
    expected_verdict: String,
}

fn manifest_expected_case_metadata() -> Vec<CaseMetadata> {
    let source =
        std::fs::read_to_string(verus_manifest_path()).expect("Verus manifest should be readable");
    let manifest: serde_json::Value =
        serde_json::from_str(&source).expect("Verus manifest should parse as JSON");
    let row = manifest["entries"]
        .as_array()
        .expect("Verus manifest should contain entries")
        .iter()
        .find(|entry| {
            entry["upstream_path"].as_str() == Some("source/rust_verify_test/tests/multiset.rs")
        })
        .expect("Verus manifest should contain multiset.rs row");

    assert_eq!(
        row["classification"].as_str(),
        Some("ported"),
        "multiset.rs row should be a ported entry"
    );

    let mut cases: Vec<CaseMetadata> = row["expected_cases"]
        .as_array()
        .expect("multiset.rs row should contain expected_cases")
        .iter()
        .map(|entry| {
            // Pinned proof entries must carry obligation_fingerprints consistent
            // with min_obligations (the corpus run re-checks them against a real
            // verifier run; here we only assert the shape stays honest).
            let min_obl = entry["min_obligations"].as_u64().unwrap_or(0) as usize;
            let fps = entry["obligation_fingerprints"]
                .as_array()
                .map(|a| a.len())
                .unwrap_or(0);
            let case_id = entry["case_id"].as_str().expect("case_id").to_string();
            assert_eq!(
                min_obl, fps,
                "{case_id}: min_obligations must equal pinned obligation_fingerprints count"
            );
            assert!(
                min_obl >= 1,
                "{case_id}: every faithful multiset case must pin at least one obligation"
            );
            assert!(
                entry["expected_error_patterns"].as_array().is_none(),
                "{case_id}: faithful multiset port must not use error/surrogate patterns"
            );
            CaseMetadata {
                case_id,
                upstream_case_id: entry["upstream_case_id"]
                    .as_str()
                    .expect("upstream_case_id")
                    .to_string(),
                expected_verdict: entry["expected_verdict"]
                    .as_str()
                    .expect("expected_verdict")
                    .to_string(),
            }
        })
        .collect();
    cases.sort();
    cases
}

#[test]
fn multiset_rs_upstream_basics_cases_verify_from_file() {
    let path = port_path();
    let path = path.to_str().expect("multiset port path should be UTF-8");
    for case in VERIFIED_CASES {
        assert_verified(path, case);
    }
}

#[test]
fn multiset_rs_upstream_fail_cases_are_genuine_counterexamples_from_file() {
    let path = port_path();
    let path = path.to_str().expect("multiset port path should be UTF-8");
    for case in COUNTEREXAMPLE_CASES {
        assert_counterexample(path, case);
    }
}

#[test]
fn multiset_rs_manifest_row_matches_faithful_upstream_coverage() {
    let mut expected: Vec<CaseMetadata> = Vec::new();
    for case in VERIFIED_CASES {
        expected.push(CaseMetadata {
            case_id: (*case).to_string(),
            upstream_case_id: "multiset_basics".to_string(),
            expected_verdict: "verified".to_string(),
        });
    }
    for case in COUNTEREXAMPLE_CASES {
        expected.push(CaseMetadata {
            case_id: (*case).to_string(),
            // For the *_fail cases the port function is named for its upstream test.
            upstream_case_id: (*case).to_string(),
            expected_verdict: "counterexample".to_string(),
        });
    }
    expected.sort();

    assert_eq!(
        manifest_expected_case_metadata(),
        expected,
        "multiset.rs port functions and Verus manifest row must stay in lockstep"
    );

    // The five upstream test_verify_one_file cases must all be covered exactly once
    // in the upstream_case_id mapping.
    let upstream_ids: BTreeSet<&str> = [
        "multiset_basics",
        "multiset_fail",
        "multiset_fail2",
        "multiset_fail3",
        "multiset_fail4",
    ]
    .into_iter()
    .collect();
    let mapped: BTreeSet<String> = manifest_expected_case_metadata()
        .into_iter()
        .map(|c| c.upstream_case_id)
        .collect();
    assert_eq!(
        mapped,
        upstream_ids.iter().map(|s| (*s).to_string()).collect(),
        "all five upstream multiset cases must be covered"
    );
}
