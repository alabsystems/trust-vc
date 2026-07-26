// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Executable guards for the faithful 1:1 upstream nonlinear.rs TrustVc port.
//!
//! The port reproduces every non-ignored upstream `nonlinear.rs` case (one
//! TrustVc fn per upstream case; the two-fn upstream `test_new_vars` case maps
//! to `test_new_vars` + `test_new_vars_loop`) with the matching verifier
//! verdict. These tests pin the 1:1 structure, the per-case verdicts, the two
//! Verus VIR diagnostics, and exact agreement with the accepted-corpus
//! manifest row.

mod common;

use std::{
    collections::{BTreeMap, BTreeSet},
    path::PathBuf,
};
use trust_vc_core::{verify_function_from_file, VerifyResult};

fn nonlinear_port_path() -> PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/ported/nonlinear.rs")
}

fn verus_manifest_path() -> PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/verus-tests.json")
}

fn pinned_upstream_nonlinear_path() -> PathBuf {
    common::pinned_verus_test_path("nonlinear.rs")
}

/// Every upstream `test_verify_one_file!` case id in pinned order.
/// `nlarith1` is `#[ignore]`d upstream (Z3 too slow) and is the only case the
/// port does not map.
const UPSTREAM_CASES: &[&str] = &[
    "test1",
    "test2",
    "test3",
    "test4",
    "test1_fails",
    "test2_fails",
    "test5",
    "test6",
    "test_requires",
    "test7",
    "test3_fails",
    "test4_fails",
    "test_assert_nonlinear_by_in_nonlinear",
    "test_negative",
    "test_unexpected_vars",
    "test_complex_vars",
    "test_requires_no_block",
    "test_new_vars",
    "nlarith1",
];

const EXPECTED_CASES: &[(&str, &str, &str, usize)] = &[
    ("test1", "test1", "verified", 1),
    ("test2", "test2", "verified", 1),
    ("test3", "test3", "verified", 1),
    ("test4", "test4", "verified", 1),
    ("test1_fails", "test1_fails", "counterexample", 1),
    ("test2_fails", "test2_fails", "counterexample", 1),
    ("test5", "test5", "verified", 1),
    ("test6", "test6", "verified", 1),
    ("test_requires", "test_requires", "counterexample", 1),
    ("test7", "test7", "verified", 1),
    ("test3_fails", "test3_fails", "counterexample", 1),
    ("test4_fails", "test4_fails", "counterexample", 1),
    (
        "test_assert_nonlinear_by_in_nonlinear",
        "test_assert_nonlinear_by_in_nonlinear",
        "error",
        0,
    ),
    ("test_negative", "test_negative", "counterexample", 1),
    ("test_unexpected_vars", "test_unexpected_vars", "error", 0),
    ("test_complex_vars", "test_complex_vars", "verified", 1),
    (
        "test_requires_no_block",
        "test_requires_no_block",
        "verified",
        1,
    ),
    ("test_new_vars", "test_new_vars", "verified", 1),
    ("test_new_vars_loop", "test_new_vars", "verified", 1),
];

const ERROR_PATTERN_CASES: &[(&str, &str, &[&str])] = &[
    (
        "test_assert_nonlinear_by_in_nonlinear",
        "test_assert_nonlinear_by_in_nonlinear",
        &["assert_by_query not allowed in #[verifier::nonlinear] functions"],
    ),
    (
        "test_unexpected_vars",
        "test_unexpected_vars",
        &["not mentioned in requires/ensures"],
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
        .unwrap_or_else(|| panic!("nonlinear port should define {const_name}"));

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
    let array = referenced_array_const(file, "NONLINEAR_RS_ERROR_PATTERNS");
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
    let array = referenced_array_const(file, "NONLINEAR_RS_EXPECTED_CASES");
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
            "duplicate nonlinear metadata for {case_id}"
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
    let error_patterns: BTreeMap<&str, Vec<String>> = ERROR_PATTERN_CASES
        .iter()
        .map(|(case_id, _, fragments)| {
            (
                *case_id,
                fragments
                    .iter()
                    .map(|fragment| (*fragment).to_string())
                    .collect(),
            )
        })
        .collect();

    EXPECTED_CASES
        .iter()
        .map(
            |(case_id, upstream_case_id, expected_verdict, min_obligations)| CaseMetadata {
                case_id: (*case_id).to_string(),
                upstream_case_id: (*upstream_case_id).to_string(),
                expected_verdict: (*expected_verdict).to_string(),
                min_obligations: *min_obligations,
                expected_error_patterns: error_patterns.get(case_id).cloned().unwrap_or_default(),
            },
        )
        .collect()
}

/// The accepted-corpus manifest pins `min_obligations` to the exact observed
/// obligation count, which is >= the lower bound declared in the port's own
/// metadata table. Compare every field except `min_obligations` exactly, and
/// require the manifest count to be at least the port's declared lower bound.
fn assert_matches_manifest(port: &[CaseMetadata], manifest: &[CaseMetadata]) {
    assert_eq!(
        port.len(),
        manifest.len(),
        "port and manifest should agree on the case count"
    );
    for (port_case, manifest_case) in port.iter().zip(manifest.iter()) {
        assert_eq!(port_case.case_id, manifest_case.case_id);
        assert_eq!(port_case.upstream_case_id, manifest_case.upstream_case_id);
        assert_eq!(port_case.expected_verdict, manifest_case.expected_verdict);
        assert_eq!(
            port_case.expected_error_patterns,
            manifest_case.expected_error_patterns
        );
        assert!(
            manifest_case.min_obligations >= port_case.min_obligations,
            "manifest min_obligations for {} ({}) should be at least the port lower bound {}",
            manifest_case.case_id,
            manifest_case.min_obligations,
            port_case.min_obligations
        );
    }
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
            entry["upstream_path"].as_str() == Some("source/rust_verify_test/tests/nonlinear.rs")
        })
        .expect("Verus manifest should contain nonlinear.rs row");

    // RECORDED: every case below verifies 1:1 with its upstream verdict (the
    // from-file tests in this harness are the executable witness), and the row
    // is classified `ported` with trust_vc_source_hashes + obligation
    // fingerprints auto-pinned by the passing all-or-nothing
    // --refresh-trust-vc-corpus-evidence run (never hand-edited).
    assert_eq!(
        row["classification"].as_str(),
        Some("ported"),
        "nonlinear.rs manifest row classification drifted from the recorded ported state"
    );

    row["expected_cases"]
        .as_array()
        .expect("nonlinear.rs row should contain expected_cases")
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
fn nonlinear_rs_port_file_is_rust_syntax() {
    let source =
        std::fs::read_to_string(nonlinear_port_path()).expect("nonlinear port should read");
    syn::parse_file(&source).expect("nonlinear port should parse as ordinary Rust syntax");
}

#[test]
fn nonlinear_rs_expected_case_metadata_is_exact() {
    let source =
        std::fs::read_to_string(nonlinear_port_path()).expect("nonlinear port should read");
    let file = syn::parse_file(&source).expect("nonlinear port should parse");
    assert_eq!(metadata_entries(&file), expected_metadata());
    assert!(
        source.contains("nonlinear_rs_expected_cases"),
        "nonlinear port should export expected-case metadata"
    );
    assert!(
        source.contains("nonlinear_rs_error_patterns"),
        "nonlinear port should export error-pattern metadata"
    );
}

#[test]
fn nonlinear_rs_expected_case_metadata_matches_manifest() {
    let source =
        std::fs::read_to_string(nonlinear_port_path()).expect("nonlinear port should read");
    let file = syn::parse_file(&source).expect("nonlinear port should parse");
    assert_matches_manifest(&metadata_entries(&file), &manifest_expected_metadata());
}

/// Every non-ignored upstream case id is mapped by at least one expected case
/// (via `upstream_case_id`); the only unmapped upstream case is the
/// `#[ignore]`d `nlarith1`; and every port fn named by a `case_id` exists.
#[test]
fn nonlinear_rs_expected_cases_cover_upstream_one_to_one() {
    let mapped: BTreeSet<&str> = EXPECTED_CASES
        .iter()
        .map(|(_, upstream_case_id, _, _)| *upstream_case_id)
        .collect();
    for upstream_case in UPSTREAM_CASES {
        if *upstream_case == "nlarith1" {
            assert!(
                !mapped.contains(upstream_case),
                "nlarith1 is #[ignore]d upstream and must not be claimed by the port"
            );
            continue;
        }
        assert!(
            mapped.contains(upstream_case),
            "upstream case {upstream_case} should be mapped by the port"
        );
    }

    let source =
        std::fs::read_to_string(nonlinear_port_path()).expect("nonlinear port should read");
    let parsed = syn::parse_file(&source).expect("nonlinear port should parse");
    for (case_id, _, _, _) in EXPECTED_CASES {
        let found = parsed.items.iter().any(|item| match item {
            syn::Item::Fn(function) => function.sig.ident == case_id,
            _ => false,
        });
        assert!(found, "{case_id} should be a top-level port fn");
    }
}

#[test]
fn nonlinear_rs_verified_subset_verifies_from_file() {
    let path = nonlinear_port_path();
    let path = path.to_str().expect("nonlinear port path should be UTF-8");

    for (case, upstream_case, _, _) in EXPECTED_CASES
        .iter()
        .filter(|(_, _, verdict, _)| *verdict == "verified")
    {
        let result = verify_function_from_file(path, case)
            .unwrap_or_else(|err| panic!("{case} ({upstream_case}) should extract: {err}"));
        assert!(
            matches!(result, VerifyResult::Verified),
            "{case} ({upstream_case}) should verify, got: {result:?}"
        );
    }
}

#[test]
fn nonlinear_rs_counterexample_subset_is_rejected_from_file() {
    let path = nonlinear_port_path();
    let path = path.to_str().expect("nonlinear port path should be UTF-8");

    for (case, upstream_case, _, _) in EXPECTED_CASES
        .iter()
        .filter(|(_, _, verdict, _)| *verdict == "counterexample")
    {
        let result = verify_function_from_file(path, case)
            .unwrap_or_else(|err| panic!("{case} ({upstream_case}) should extract: {err}"));
        // The corpus `counterexample` expectation means "assert_fails": either
        // a genuine model-bearing counterexample OR a model-less
        // incompleteness non-proof, which maps to the gate's `counterexample`
        // label per design-unknown-as-failure.md; never a fabricated
        // model.
        let rejected = match &result {
            VerifyResult::Counterexample { .. } => true,
            VerifyResult::Unknown { category, .. } => category.is_incompleteness(),
            _ => false,
        };
        assert!(
            rejected,
            "{case} ({upstream_case}) should be rejected (counterexample or incompleteness non-proof), got: {result:?}"
        );
    }
}

/// The two upstream VIR diagnostics: nested assert-by query inside a
/// `#[verifier(nonlinear)]` fn, and a proof-block variable outside the scoped
/// query interface. Each must fail closed with the upstream message.
#[test]
fn nonlinear_rs_vir_diagnostics_fail_closed_from_file() {
    let path = nonlinear_port_path();
    let path = path.to_str().expect("nonlinear port path should be UTF-8");

    for (case, upstream_case, expected_fragments) in ERROR_PATTERN_CASES {
        let message = match verify_function_from_file(path, case) {
            Ok(VerifyResult::Error { message }) => message,
            Ok(other) => panic!("{case} ({upstream_case}) should fail closed, got: {other:?}"),
            Err(err) => err.to_string(),
        };
        assert!(
            expected_fragments
                .iter()
                .all(|fragment| message.contains(fragment)),
            "{case} ({upstream_case}) error should mention all of {expected_fragments:?}, got: {message}"
        );
    }
}

/// The pinned upstream file's shape must not drift: case order, verdict
/// counts, the `#[ignore]` count, and the two VIR diagnostics.
#[test]
fn nonlinear_rs_pinned_upstream_shape_stays_expected() {
    let path = pinned_upstream_nonlinear_path();
    if !path.exists() {
        eprintln!(
            "skipping pinned upstream nonlinear.rs shape check; missing {}",
            path.display()
        );
        return;
    }

    let source = std::fs::read_to_string(&path).expect("pinned upstream nonlinear.rs should read");

    let mut previous = 0;
    for case in UPSTREAM_CASES {
        let marker = format!("\n    #[test] {case}");
        let current = source
            .find(&marker)
            .unwrap_or_else(|| panic!("upstream nonlinear.rs should contain case {case}"));
        assert!(
            current >= previous,
            "upstream nonlinear.rs case {case} should stay in pinned order"
        );
        previous = current;
    }

    assert_eq!(
        source.matches("=> Ok(())").count(),
        11,
        "upstream nonlinear.rs verified-case count should stay pinned"
    );
    assert_eq!(
        source.matches("=> Err(e) => assert_one_fails(e)").count(),
        6,
        "upstream nonlinear.rs one-failure count should stay pinned"
    );
    assert_eq!(
        source
            .matches("=> Err(err) => assert_vir_error_msg")
            .count(),
        2,
        "upstream nonlinear.rs Vir diagnostic count should stay pinned"
    );
    assert_eq!(
        source.matches("#[ignore]").count(),
        1,
        "upstream nonlinear.rs ignored slow-case count should stay pinned"
    );
    assert!(
        source.contains("assert_by_query not allowed in #[verifier::nonlinear] functions"),
        "upstream nested assert-by diagnostic should stay pinned"
    );
    assert!(
        source.contains("not mentioned in requires/ensures"),
        "upstream unexpected-variable diagnostic should stay pinned"
    );
}
