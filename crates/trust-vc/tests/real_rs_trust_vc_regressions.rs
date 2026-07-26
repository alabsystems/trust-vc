// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Executable guards for the faithful 1:1 upstream real.rs TrustVc port.
//!
//! The port reproduces every non-ignored upstream `real.rs` case (one TrustVc
//! proof fn per upstream proof fn) with the matching verifier verdict. These
//! tests pin that 1:1 structure, the per-case verdicts, and the mixed-chain
//! fail-closed diagnostic, and assert exact agreement with the accepted-corpus
//! manifest row.

mod common;

use std::{
    collections::{BTreeMap, BTreeSet},
    path::PathBuf,
};
use trust_vc_core::{verify_function_from_file, VerifyResult};
use trust_vc_types::nat;

fn real_port_path() -> PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/ported/real.rs")
}

fn verus_manifest_path() -> PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/verus-tests.json")
}

fn metadata_prelude(source: &str) -> &str {
    source
        .split_once("#[trust_vc::ensures(true)]\nfn real_basics")
        .map(|(prefix, _)| prefix)
        .expect("real port should keep metadata before the first proof case")
}

const EXPECTED_CASES: &[(&str, &str, &str, usize)] = &[
    ("real_basics", "real_basics", "counterexample", 1),
    ("real_nonlinear1", "real_nonlinear1", "verified", 1),
    ("real_nonlinear2", "real_nonlinear2", "counterexample", 1),
    ("archimedean_nat", "archimedean_nat", "verified", 1),
    ("test_chained", "test_chained", "verified", 1),
    ("test_reject_mixed", "test_reject_mixed", "error", 0),
];

const FAIL_CLOSED_CASES: &[(&str, &str, &[&str])] = &[(
    "test_reject_mixed",
    "test_reject_mixed",
    &["chained inequalities require all elements to have the same type"],
)];

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
        .unwrap_or_else(|| panic!("real port should define {const_name}"));

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
    let array = referenced_array_const(file, "REAL_RS_FAIL_CLOSED_ERROR_PATTERNS");
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
    let array = referenced_array_const(file, "REAL_RS_EXPECTED_CASES");
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
            "duplicate real metadata for {case_id}"
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
    let error_patterns: BTreeMap<&str, Vec<String>> = FAIL_CLOSED_CASES
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
            entry["upstream_path"].as_str() == Some("source/rust_verify_test/tests/real.rs")
        })
        .expect("Verus manifest should contain real.rs row");

    row["expected_cases"]
        .as_array()
        .expect("real.rs row should contain expected_cases")
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
fn real_rs_expected_case_metadata_is_exact() {
    let source = std::fs::read_to_string(real_port_path()).expect("real port should be readable");
    let file = syn::parse_file(metadata_prelude(&source))
        .expect("real port metadata prelude should parse as ordinary Rust syntax");
    assert_eq!(metadata_entries(&file), expected_metadata());
    assert!(
        source.contains("real_rs_expected_cases"),
        "real port should export expected-case metadata"
    );
    assert!(
        source.contains("real_rs_fail_closed_error_patterns"),
        "real port should export fail-closed error-pattern metadata"
    );
}

#[test]
fn real_rs_expected_case_metadata_matches_manifest() {
    let source = std::fs::read_to_string(real_port_path()).expect("real port should be readable");
    let file = syn::parse_file(metadata_prelude(&source))
        .expect("real port metadata prelude should parse as ordinary Rust syntax");
    assert_matches_manifest(&metadata_entries(&file), &manifest_expected_metadata());
}

#[test]
fn real_rs_verified_subset_verifies_from_file() {
    let path = real_port_path();
    let path = path.to_str().expect("real port path should be UTF-8");

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
fn real_rs_counterexample_subset_is_rejected_from_file() {
    let path = real_port_path();
    let path = path.to_str().expect("real port path should be UTF-8");

    for (case, upstream_case, _, _) in EXPECTED_CASES
        .iter()
        .filter(|(_, _, verdict, _)| *verdict == "counterexample")
    {
        let result = verify_function_from_file(path, case)
            .unwrap_or_else(|err| panic!("{case} ({upstream_case}) should extract: {err}"));
        // The corpus `counterexample` expectation means "assert_fails": either a
        // genuine model-bearing counterexample (real_basics) OR a model-less
        // incompleteness non-proof (real_nonlinear2, the hint-free nonlinear-real
        // goal). The latter maps to the gate's `counterexample` label per
        // design-unknown-as-failure.md; never a fabricated model.
        let rejected = match &result {
            VerifyResult::Counterexample { .. } => true,
            VerifyResult::Unknown { category, .. } => category.is_incompleteness(),
            // A model-less incompleteness non-proof is the SAME fail-closed
            // rejection whether the engine wraps it as `Unknown` or `NotProved`
            // (design-unknown-as-failure.md); the nonlinear-real profile guard
            // (`smt.arith.nl=false` analog) emits the latter for `real_nonlinear2`.
            VerifyResult::NotProved { category, .. } => category.is_incompleteness(),
            _ => false,
        };
        assert!(
            rejected,
            "{case} ({upstream_case}) should be rejected (counterexample or incompleteness non-proof), got: {result:?}"
        );
    }
}

#[test]
fn real_rs_mixed_chain_fails_closed_from_file() {
    let path = real_port_path();
    let path = path.to_str().expect("real port path should be UTF-8");

    for (case, upstream_case, expected_fragments) in FAIL_CLOSED_CASES {
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

#[test]
fn real_rs_decimal_literal_exactness_verifies() {
    let _ = common::verify_should_pass(|| {
        trust_vc::assert!(1.5 == 3.0 / 2.0);
    });
}

#[test]
fn real_rs_chained_nat_to_real_verifies() {
    let _ = common::verify_should_pass(|| {
        #[trust_vc::proof]
        fn proof_chained_nat_to_real(n: nat) {
            trust_vc::assert!(0 <= 0 < (n as real) + 1 < (n as real) + 2);
        }

        proof_chained_nat_to_real(0);
    });
}
