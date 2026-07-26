// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Executable guards for the first upstream triggers.rs TrustVc scout slice.
//!
//! These tests intentionally keep upstream triggers.rs as an unsupported gap.
//! They prove only a narrow arithmetic-trigger quantifier witness, reject an
//! adjacent false quantifier claim, pin the current explicit-trigger false
//! universal solver-Unknown boundary, prove an assert-forall Verus-style inner
//! trigger-group witness, and pin explicit-trigger diagnostic boundaries as
//! fail-closed.

use std::{
    collections::{BTreeMap, BTreeSet},
    path::PathBuf,
};
use trust_vc_core::{
    extract_verification_conditions_with_file_context, verify_function_from_file, VerifyResult,
};

fn triggers_port_path() -> PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/ported/triggers.rs")
}

fn verus_manifest_path() -> PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/verus-tests.json")
}

fn verify_case(path: &str, case: &str, upstream_case: &str) -> VerifyResult {
    verify_function_from_file(path, case)
        .unwrap_or_else(|err| panic!("{case} ({upstream_case}) should extract: {err}"))
}

fn expect_fail_closed(path: &str, case: &str, upstream_case: &str, expected_fragments: &[&str]) {
    let message = match verify_function_from_file(path, case) {
        Ok(VerifyResult::Error { message }) => message,
        Ok(result) => {
            panic!("{case} ({upstream_case}) should fail closed with Error, got: {result:?}")
        }
        Err(err) => err.to_string(),
    };

    for expected_fragment in expected_fragments {
        assert!(
            message.contains(expected_fragment),
            "{case} ({upstream_case}) error should contain {expected_fragment:?}, got: {message}"
        );
    }
}

const VERIFIED_CASES: &[(&str, &str)] = &[
    (
        "arithmetic_trigger_quantifier_verified",
        "test_ok_arith_trigger",
    ),
    (
        "verus_style_multi_trigger_groups_verified",
        "test_multiple_triggers",
    ),
];

const COUNTEREXAMPLE_CASES: &[(&str, &str)] = &[(
    "trigger_adjacent_quantifier_counterexample",
    "test_arith_function_trigger_fail",
)];

const UNKNOWN_CASES: &[(&str, &str)] = &[(
    "explicit_trigger_false_universal_currently_unknown",
    "test_arith_function_trigger_fail explicit-trigger false universal scout",
)];

const FAIL_CLOSED_CASES: &[(&str, &str, &[&str])] = &[
    (
        "trigger_without_bound_var_fails_closed",
        "test_fails_single_trigger",
        &["does not reference any bound variable"],
    ),
    (
        "quantifier_level_trigger_syntax_fails_closed",
        "test_multiple_triggers",
        &["Failed to parse assert_forall_by!() expression"],
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
        .unwrap_or_else(|| panic!("triggers port should define {const_name}"));

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
    let array = referenced_array_const(file, "TRIGGERS_RS_EXPECTED_ERROR_PATTERNS");
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
    let array = referenced_array_const(file, "TRIGGERS_RS_EXPECTED_CASES");
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
            "duplicate triggers metadata for {case_id}"
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
    let verified = VERIFIED_CASES
        .iter()
        .map(|(case_id, upstream_case_id)| CaseMetadata {
            case_id: (*case_id).to_string(),
            upstream_case_id: (*upstream_case_id).to_string(),
            expected_verdict: "verified".to_string(),
            min_obligations: 1,
            expected_error_patterns: Vec::new(),
        });
    let counterexamples = COUNTEREXAMPLE_CASES
        .iter()
        .map(|(case_id, upstream_case_id)| CaseMetadata {
            case_id: (*case_id).to_string(),
            upstream_case_id: (*upstream_case_id).to_string(),
            expected_verdict: "counterexample".to_string(),
            min_obligations: 1,
            expected_error_patterns: Vec::new(),
        });
    let errors =
        FAIL_CLOSED_CASES
            .iter()
            .map(
                |(case_id, upstream_case_id, expected_error_patterns)| CaseMetadata {
                    case_id: (*case_id).to_string(),
                    upstream_case_id: (*upstream_case_id).to_string(),
                    expected_verdict: "error".to_string(),
                    min_obligations: 0,
                    expected_error_patterns: expected_error_patterns
                        .iter()
                        .map(|pattern| (*pattern).to_string())
                        .collect(),
                },
            );

    verified.chain(counterexamples).chain(errors).collect()
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
            entry["upstream_path"].as_str() == Some("source/rust_verify_test/tests/triggers.rs")
        })
        .expect("Verus manifest should contain triggers.rs row");

    row["expected_cases"]
        .as_array()
        .expect("triggers.rs row should contain expected_cases")
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
fn triggers_rs_expected_case_metadata_is_exact() {
    let source =
        std::fs::read_to_string(triggers_port_path()).expect("triggers port should be readable");
    let file =
        syn::parse_file(&source).expect("triggers port should parse as ordinary Rust syntax");
    assert_eq!(metadata_entries(&file), expected_metadata());
}

#[test]
fn triggers_rs_expected_case_metadata_matches_manifest() {
    let source =
        std::fs::read_to_string(triggers_port_path()).expect("triggers port should be readable");
    let file =
        syn::parse_file(&source).expect("triggers port should parse as ordinary Rust syntax");
    assert_eq!(metadata_entries(&file), manifest_expected_metadata());
}

#[test]
fn triggers_rs_arithmetic_trigger_subset_verifies_from_file() {
    let path = triggers_port_path();
    let path = path.to_str().expect("triggers port path should be UTF-8");

    for (case, upstream_case) in VERIFIED_CASES {
        let result = verify_case(path, case, upstream_case);
        assert!(
            matches!(result, VerifyResult::Verified),
            "{case} ({upstream_case}) should verify, got: {result:?}"
        );
    }
}

#[test]
fn triggers_rs_arithmetic_trigger_counterexample_from_file() {
    let path = triggers_port_path();
    let path = path.to_str().expect("triggers port path should be UTF-8");

    for (case, upstream_case) in COUNTEREXAMPLE_CASES {
        let result = verify_case(path, case, upstream_case);
        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "{case} ({upstream_case}) should be rejected, got: {result:?}"
        );
    }
}

#[test]
fn triggers_rs_explicit_trigger_false_universal_stays_fail_closed_from_file() {
    let path = triggers_port_path();
    let path = path.to_str().expect("triggers port path should be UTF-8");

    for (case, upstream_case) in UNKNOWN_CASES {
        let result = verify_case(path, case, upstream_case);
        assert!(
            matches!(result, VerifyResult::Unknown { .. }),
            "{case} ({upstream_case}) should stay fail-closed as solver Unknown, got: {result:?}"
        );
    }
}

#[test]
fn triggers_rs_explicit_trigger_boundary_fails_closed_from_file() {
    let path = triggers_port_path();
    let path = path.to_str().expect("triggers port path should be UTF-8");

    for (case, upstream_case, expected_messages) in FAIL_CLOSED_CASES {
        expect_fail_closed(path, case, upstream_case, expected_messages);
    }
}

#[test]
fn triggers_rs_manual_trigger_surface_is_preserved_from_file() {
    let path = triggers_port_path();
    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|err| panic!("triggers.rs should read from {:?}: {err}", path));
    let parsed =
        syn::parse_file(&source).unwrap_or_else(|err| panic!("triggers.rs should parse: {err}"));
    let func = parsed
        .items
        .iter()
        .find_map(|item| match item {
            syn::Item::Fn(func) if func.sig.ident == "arithmetic_trigger_quantifier_verified" => {
                Some(func)
            }
            _ => None,
        })
        .expect("arithmetic_trigger_quantifier_verified should exist in triggers.rs");

    let vc = extract_verification_conditions_with_file_context(&parsed, func)
        .unwrap_or_else(|err| panic!("trigger scout should extract: {err}"));
    let assertion = vc
        .obligations()
        .iter()
        .find(|obligation| obligation.name().starts_with("assertion"))
        .expect("trigger scout should emit an assertion");

    assert!(
        assertion.condition().contains("# [trigger]"),
        "manual trigger attribute should survive source extraction, got: {}",
        assertion.condition()
    );
    assert!(
        assertion.condition().contains("forall"),
        "manual trigger case should remain a quantified assertion, got: {}",
        assertion.condition()
    );

    let wanted = "verus_style_multi_trigger_groups_verified";
    let func = parsed
        .items
        .iter()
        .find_map(|item| match item {
            syn::Item::Fn(func) if func.sig.ident == wanted => Some(func),
            _ => None,
        })
        .expect("verus_style_multi_trigger_groups_verified should exist in triggers.rs");

    let vc = extract_verification_conditions_with_file_context(&parsed, func)
        .unwrap_or_else(|err| panic!("Verus-style inner trigger scout should extract: {err}"));
    let assertion = vc
        .obligations()
        .iter()
        .find(|obligation| obligation.name().starts_with("assert_forall_by"))
        .expect("Verus-style inner trigger scout should emit an assert_forall_by obligation");
    let patterns = assertion
        .trigger_patterns()
        .expect("Verus-style inner trigger groups should be preserved");
    assert_eq!(
        patterns.len(),
        2,
        "expected two inner trigger groups, got: {patterns:?}"
    );
    assert_eq!(
        patterns[0].len(),
        1,
        "first trigger group should have one pattern, got: {patterns:?}"
    );
    assert_eq!(
        patterns[1].len(),
        2,
        "second trigger group should preserve the two-pattern trigger group, got: {patterns:?}"
    );
    assert!(
        patterns
            .iter()
            .flatten()
            .any(|pattern| pattern.contains("i")),
        "inner trigger patterns should mention bound variable i, got: {patterns:?}"
    );
    assert!(
        patterns
            .iter()
            .flatten()
            .any(|pattern| pattern.contains("j")),
        "inner trigger patterns should mention bound variable j, got: {patterns:?}"
    );
    assert!(
        !assertion.condition().contains("#![trigger") && !assertion.condition().contains("# !"),
        "inner trigger attributes must not leak into condition, got: {}",
        assertion.condition()
    );
}
