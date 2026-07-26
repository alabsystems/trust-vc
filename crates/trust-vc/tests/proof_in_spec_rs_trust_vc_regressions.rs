// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Executable guards for the expanded upstream proof_in_spec.rs scout slice.
//!
//! These tests intentionally keep the upstream file as an unsupported gap. They
//! prove only Rust-valid recursive/spec/proof helper subsets, reject stable
//! counterexamples, and pin proof code inside spec/pure code as fail-closed
//! extraction errors rather than accepted Verus-compatible behavior. Solver
//! `Unknown` is rejected as replacement evidence.

mod common;

use std::{
    collections::BTreeMap,
    path::{Path, PathBuf},
};
use trust_vc_core::{
    extract_verification_conditions_with_file_context, verify_function_from_file, VerifyResult,
};

#[derive(Debug, PartialEq, Eq)]
struct CaseMetadata {
    case_id: String,
    upstream_case_id: String,
    expected_verdict: String,
    min_obligations: usize,
    expected_error_patterns: Vec<String>,
}

fn proof_in_spec_port_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/ported/proof_in_spec.rs")
}

fn pinned_upstream_proof_in_spec_path() -> PathBuf {
    common::pinned_verus_test_path("proof_in_spec.rs")
}

fn verus_manifest_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/verus-tests.json")
}

fn proof_in_spec_port_file() -> syn::File {
    let path = proof_in_spec_port_path();
    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|err| panic!("proof_in_spec port should read from {:?}: {err}", path));
    syn::parse_file(&source).expect("proof_in_spec port should parse as ordinary Rust syntax")
}

fn verify_port_case(case: &str, upstream_case: &str) -> (VerifyResult, usize) {
    let path = proof_in_spec_port_path();
    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|err| panic!("{} should read: {err}", path.display()));
    let file = syn::parse_file(&source)
        .unwrap_or_else(|err| panic!("{} should parse as Rust syntax: {err}", path.display()));
    let func = file
        .items
        .iter()
        .find_map(|item| match item {
            syn::Item::Fn(func) if func.sig.ident == case => Some(func),
            _ => None,
        })
        .unwrap_or_else(|| {
            panic!(
                "{case} ({upstream_case}) should exist in {}",
                path.display()
            )
        });

    let vc = extract_verification_conditions_with_file_context(&file, func)
        .unwrap_or_else(|err| panic!("{case} ({upstream_case}) should extract VCs: {err}"));
    let obligations = vc.obligations().len();
    (vc.verify(), obligations)
}

fn fail_closed_message(case: &str, upstream_case: &str) -> String {
    let path = proof_in_spec_port_path();
    let path = path
        .to_str()
        .expect("proof_in_spec port path should be UTF-8");

    match verify_function_from_file(path, case) {
        Err(err) => err.to_string(),
        Ok(VerifyResult::Error { message }) => message,
        Ok(VerifyResult::Unknown { reason, .. }) => {
            panic!(
                "{case} ({upstream_case}) returned solver Unknown, which is not stable evidence: {reason}"
            )
        }
        Ok(other) => {
            panic!("{case} ({upstream_case}) should fail closed with Error, got: {other:?}")
        }
    }
}

fn literal_string(expr: &syn::Expr) -> String {
    match expr {
        syn::Expr::Lit(syn::ExprLit {
            lit: syn::Lit::Str(lit),
            ..
        }) => lit.value(),
        _ => panic!("expected string literal in proof_in_spec metadata"),
    }
}

fn literal_usize(expr: &syn::Expr) -> usize {
    match expr {
        syn::Expr::Lit(syn::ExprLit {
            lit: syn::Lit::Int(lit),
            ..
        }) => lit
            .base10_parse::<usize>()
            .unwrap_or_else(|err| panic!("expected usize literal in metadata: {err}")),
        _ => panic!("expected usize literal in proof_in_spec metadata"),
    }
}

fn referenced_array_const(file: &syn::File, const_name: &str) -> syn::ExprArray {
    let const_item = file
        .items
        .iter()
        .find_map(|item| match item {
            syn::Item::Const(item) if item.ident == const_name => Some(item),
            _ => None,
        })
        .unwrap_or_else(|| panic!("proof_in_spec port should define {const_name}"));

    let syn::Expr::Reference(reference) = const_item.expr.as_ref() else {
        panic!("{const_name} should be a referenced array");
    };
    let syn::Expr::Array(array) = reference.expr.as_ref() else {
        panic!("{const_name} should reference an array");
    };
    array.clone()
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
    let array = referenced_array_const(file, "PROOF_IN_SPEC_RS_EXPECTED_ERROR_PATTERNS");
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
    let array = referenced_array_const(file, "PROOF_IN_SPEC_RS_EXPECTED_CASES");
    let mut error_patterns = error_pattern_entries(file);
    let mut entries = Vec::new();

    for entry in &array.elems {
        let syn::Expr::Tuple(tuple) = entry else {
            panic!("expected tuple metadata entry");
        };
        assert_eq!(
            tuple.elems.len(),
            4,
            "metadata entries should have case, upstream case, verdict, and min obligations"
        );
        let case_id = literal_string(&tuple.elems[0]);
        entries.push(CaseMetadata {
            expected_error_patterns: error_patterns.remove(&case_id).unwrap_or_default(),
            case_id,
            upstream_case_id: literal_string(&tuple.elems[1]),
            expected_verdict: literal_string(&tuple.elems[2]),
            min_obligations: literal_usize(&tuple.elems[3]),
        });
    }

    assert!(
        error_patterns.is_empty(),
        "error-pattern metadata should not contain orphan cases: {error_patterns:?}"
    );
    entries
}

fn expected_case(case: &str) -> (&'static str, &'static str, usize) {
    EXPECTED_CASE_METADATA
        .iter()
        .find_map(|(candidate, upstream_case, status, min_obligations)| {
            (*candidate == case).then_some((*upstream_case, *status, *min_obligations))
        })
        .unwrap_or_else(|| panic!("{case} should be present in expected metadata"))
}

fn reject_unknown(result: &VerifyResult, case: &str, upstream_case: &str) {
    if let VerifyResult::Unknown { reason, .. } = result {
        panic!("{case} ({upstream_case}) returned solver Unknown, which is not stable evidence: {reason}");
    }
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
                expected_error_patterns: patterns_by_case.remove(*case_id).unwrap_or_default(),
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
                == Some("source/rust_verify_test/tests/proof_in_spec.rs")
        })
        .expect("Verus manifest should contain proof_in_spec.rs row");

    row["expected_cases"]
        .as_array()
        .expect("proof_in_spec.rs row should contain expected_cases")
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
                                .expect("expected_error_patterns entries should be strings")
                                .to_string()
                        })
                        .collect()
                })
                .unwrap_or_default(),
        })
        .collect()
}

const EXPECTED_CASE_METADATA: &[(&str, &str, &str, usize)] = &[
    (
        "rec_assert_result_small_compute_verified",
        "rec_assert_result",
        "verified",
        1,
    ),
    (
        "rec_spec_calling_spec_helper_compute_verified",
        "",
        "verified",
        1,
    ),
    ("proof_calling_spec_helper_verified", "", "verified", 1),
    ("proof_calling_proof_helper_verified", "", "verified", 1),
    ("proof_by_compute_spec_helper_verified", "", "verified", 1),
    ("rec_assert_bitvector_requires_verified", "", "verified", 1),
    ("rec_spinoff_prover_compute_verified", "", "verified", 1),
    (
        "rec_assert_result_wrong_value_counterexample",
        "rec_assert_result",
        "counterexample",
        1,
    ),
    (
        "rec_spec_calling_spec_helper_wrong_value_counterexample",
        "",
        "counterexample",
        1,
    ),
    (
        "proof_calling_spec_helper_wrong_result_counterexample",
        "",
        "counterexample",
        1,
    ),
    (
        "proof_calling_proof_helper_bad_requires_counterexample",
        "",
        "counterexample",
        1,
    ),
    (
        "proof_by_compute_spec_helper_wrong_value_counterexample",
        "",
        "counterexample",
        1,
    ),
    (
        "rec_assert_bitvector_missing_requires_counterexample",
        "",
        "counterexample",
        1,
    ),
    (
        "nonrecursive_spec_proof_block_fails_closed",
        "nonrecursive_not_yet_supported1",
        "error",
        0,
    ),
    (
        "recursive_spec_proof_block_fails_closed",
        "nonrecursive_not_yet_supported2",
        "error",
        0,
    ),
    (
        "proof_fn_local_proof_block_expression_fails_closed",
        "non_spec_fn_not_yet_supported",
        "error",
        0,
    ),
    (
        "spec_proof_block_return_fails_closed",
        "return_not_allowed",
        "error",
        0,
    ),
    (
        "proof_block_assignment_fails_closed",
        "assign_not_allowed",
        "error",
        0,
    ),
    (
        "spec_calling_proof_helper_compute_fails_closed",
        "",
        "error",
        0,
    ),
    ("spec_tracked_get_boundary_fails_closed", "", "error", 0),
    (
        "choose_body_proof_block_currently_verifies_blocker",
        "",
        "verified-blocker",
        0,
    ),
];

const FAIL_CLOSED_CASES: &[(&str, &str, &[&str])] = &[
    (
        "nonrecursive_spec_proof_block_fails_closed",
        "nonrecursive_not_yet_supported1",
        &["Unsupported proof_block!()"],
    ),
    (
        "recursive_spec_proof_block_fails_closed",
        "nonrecursive_not_yet_supported2",
        &["Unsupported proof_block!()"],
    ),
    (
        "proof_fn_local_proof_block_expression_fails_closed",
        "non_spec_fn_not_yet_supported",
        &["Unsupported proof_block!()"],
    ),
    (
        "spec_proof_block_return_fails_closed",
        "return_not_allowed",
        &["Unsupported proof_block!()"],
    ),
    (
        "proof_block_assignment_fails_closed",
        "assign_not_allowed",
        &["Unsupported proof_block!()"],
    ),
    (
        "spec_calling_proof_helper_compute_fails_closed",
        "",
        &["proof_in_spec_ghost_helper"],
    ),
    (
        "spec_tracked_get_boundary_fails_closed",
        "",
        &["Tracked::get", "unsupported", "method", "get"],
    ),
];

#[test]
fn proof_in_spec_rs_port_file_is_rust_syntax() {
    let source = std::fs::read_to_string(proof_in_spec_port_path())
        .expect("proof_in_spec port should be readable");
    syn::parse_file(&source).expect("proof_in_spec port should parse as ordinary Rust syntax");
    assert!(
        source.contains("proof_in_spec_rs_expected_cases")
            && source.contains("proof_in_spec_rs_expected_error_patterns"),
        "proof_in_spec scout should expose its expected-case and error-pattern helpers"
    );
}

#[test]
fn proof_in_spec_rs_pinned_upstream_case_shapes_are_present() {
    let path = pinned_upstream_proof_in_spec_path();
    if !path.exists() {
        eprintln!(
            "skipping pinned upstream proof_in_spec.rs shape check; missing {}",
            path.display()
        );
        return;
    }

    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", path.display()));
    for expected in [
        "#[test] rec_assume",
        "#[test] rec_assert_false",
        "#[test] rec_assert_assume",
        "#[test] rec_assert_bitvector1",
        "#[test] rec_assert_bitvector2",
        "#[test] rec_assert_bitvector3",
        "#[test] rec_assert_result",
        "#[test] rec_proof_ok",
        "#[test] rec_proof_fails_requires",
        "#[test] rec_proof_ineffective",
        "#[test] rec_proof_ok_by",
        "#[test] rec_proof_fails_requires_by",
        "#[test] rec_proof_ineffective_by",
        "#[test] rec_proof_by_fails",
        "#[test] nonrecursive_not_yet_supported1",
        "#[test] nonrecursive_not_yet_supported2",
        "#[test] non_spec_fn_not_yet_supported",
        "#[test] return_not_allowed",
        "#[test] assign_not_allowed",
        "#[test] tracked_not_allowed1",
        "#[test] tracked_not_allowed2",
        "#[test] rec_cycle1",
        "#[test] rec_cycle2",
        "#[test] rec_cycle3",
        "#[test] rec_cycle4",
        "#[test] rec_cycle5",
        "#[test] proof_inside_pure1",
        "#[test] proof_inside_pure2",
        "#[test] proof_inside_pure3",
        "#[test] rec_spinoff_prover",
        "assert(i >> 1 < i) by(bit_vector)",
        "assert(one() == 1) by {",
        "proof block must have type",
        "return 3;",
        "b = true;",
        "let tracked x = g();",
        "choose|i: int|",
        "#[verifier::spinoff_prover]",
    ] {
        assert!(
            source.contains(expected),
            "pinned upstream proof_in_spec.rs should still contain {expected}"
        );
    }
}

#[test]
fn proof_in_spec_rs_expected_case_metadata_is_exact() {
    let file = proof_in_spec_port_file();
    let actual = metadata_entries(&file);
    assert_eq!(
        actual,
        expected_metadata_from_tests(),
        "proof_in_spec port metadata should exactly match the regression inventory"
    );
    assert_eq!(
        error_pattern_entries(&file),
        expected_error_pattern_entries(),
        "proof_in_spec port error-pattern metadata should match fail-closed cases"
    );

    for required_status in ["verified", "counterexample", "error", "verified-blocker"] {
        assert!(
            actual
                .iter()
                .any(|case| case.expected_verdict == required_status),
            "metadata should include at least one {required_status} case"
        );
    }
    assert!(
        !actual.iter().any(|case| case.expected_verdict == "unknown"),
        "Unknown outcomes must not be inventoried as replacement evidence"
    );
}

#[test]
fn proof_in_spec_rs_expected_case_metadata_matches_manifest() {
    let file = proof_in_spec_port_file();

    assert_eq!(
        metadata_entries(&file),
        manifest_expected_metadata(),
        "proof_in_spec manifest expected_cases should match port metadata exactly"
    );
}

#[test]
fn proof_in_spec_rs_error_cases_have_expected_error_patterns() {
    let file = proof_in_spec_port_file();
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
fn proof_in_spec_rs_expected_case_metadata_names_exist_in_port() {
    let file = proof_in_spec_port_file();
    let function_names = file
        .items
        .iter()
        .filter_map(|item| match item {
            syn::Item::Fn(func) => Some(func.sig.ident.to_string()),
            _ => None,
        })
        .collect::<std::collections::BTreeSet<_>>();

    for case in metadata_entries(&file) {
        assert!(
            function_names.contains(&case.case_id),
            "metadata case {} should name a function in proof_in_spec port",
            case.case_id
        );
    }
}

#[test]
fn proof_in_spec_rs_verified_subset_verifies_from_file() {
    for (case, upstream_case, status, min_obligations) in EXPECTED_CASE_METADATA
        .iter()
        .filter(|(_, _, status, _)| *status == "verified")
    {
        let (result, obligations) = verify_port_case(case, upstream_case);
        reject_unknown(&result, case, upstream_case);
        assert!(
            obligations >= *min_obligations,
            "{case} ({upstream_case}) should collect at least {min_obligations} obligation(s), got {obligations}"
        );
        assert!(
            matches!(result, VerifyResult::Verified),
            "{case} ({upstream_case}) should verify, got: {result:?}"
        );
        assert_eq!(*status, "verified");
    }
}

#[test]
fn proof_in_spec_rs_counterexample_subset_is_rejected_from_file() {
    for (case, upstream_case, status, min_obligations) in EXPECTED_CASE_METADATA
        .iter()
        .filter(|(_, _, status, _)| *status == "counterexample")
    {
        let (result, obligations) = verify_port_case(case, upstream_case);
        reject_unknown(&result, case, upstream_case);
        assert!(
            obligations >= *min_obligations,
            "{case} ({upstream_case}) should collect at least {min_obligations} obligation(s), got {obligations}"
        );
        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "{case} ({upstream_case}) should be rejected, got: {result:?}"
        );
        assert_eq!(*status, "counterexample");
    }
}

#[test]
fn proof_in_spec_rs_verified_blockers_are_rejected_as_replacement_evidence() {
    for (case, upstream_case, status, _) in EXPECTED_CASE_METADATA
        .iter()
        .filter(|(_, _, status, _)| *status == "verified-blocker")
    {
        let (result, _) = verify_port_case(case, upstream_case);
        reject_unknown(&result, case, upstream_case);
        assert!(
            matches!(result, VerifyResult::Verified),
            "{case} ({upstream_case}) currently verifies and must remain a blocker until TrustVc rejects or models the upstream semantic shape, got: {result:?}"
        );
        assert_eq!(*status, "verified-blocker");
    }
}

#[test]
fn proof_in_spec_rs_inline_proof_block_in_spec_fails_closed_from_file() {
    let metadata_error_cases = EXPECTED_CASE_METADATA
        .iter()
        .filter_map(|(case, _, status, _)| (*status == "error").then_some(*case))
        .collect::<Vec<_>>();
    let fragment_error_cases = FAIL_CLOSED_CASES
        .iter()
        .map(|(case, _, _)| *case)
        .collect::<Vec<_>>();
    assert_eq!(
        fragment_error_cases, metadata_error_cases,
        "every metadata error case should have exact fail-closed fragments"
    );

    for (case, upstream_case, expected_fragments) in FAIL_CLOSED_CASES {
        let (_, status, _) = expected_case(case);
        assert_eq!(status, "error");
        let message = fail_closed_message(case, upstream_case);

        assert!(
            expected_fragments
                .iter()
                .any(|expected_fragment| message.contains(expected_fragment)),
            "{case} ({upstream_case}) error should contain one of {expected_fragments:?}, got: {message}"
        );
    }
}
