// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Executable guards for the upstream quantifiers.rs TrustVc scout.
//!
//! These tests intentionally keep upstream quantifiers.rs classified as an
//! unsupported gap. They pin only stable verified quantified subsets, stable
//! counterexamples, and fail-closed parser/encoder boundaries. Solver
//! `Unknown` is rejected as replacement evidence.

mod common;

use std::{
    collections::{BTreeMap, BTreeSet},
    path::{Path, PathBuf},
};
use trust_vc_core::{
    extract_verification_conditions_with_file_context, parse_file_allow_tracked,
    verify_function_from_file, VerifyResult,
};

#[derive(Debug, PartialEq, Eq)]
struct CaseMetadata {
    case_id: String,
    upstream_case_id: String,
    expected_verdict: String,
    min_obligations: usize,
    expected_error_patterns: Vec<String>,
}

struct CaseExpectation {
    case_id: &'static str,
    upstream_case_id: &'static str,
    min_obligations: usize,
}

fn quantifiers_port_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/ported/quantifiers.rs")
}

fn pinned_upstream_quantifiers_path() -> PathBuf {
    common::pinned_verus_test_path("quantifiers.rs")
}

fn verus_manifest_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/verus-tests.json")
}

fn quantifiers_port_file() -> syn::File {
    let path = quantifiers_port_path();
    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|err| panic!("quantifiers port should read from {:?}: {err}", path));
    parse_file_allow_tracked(&source).expect("quantifiers port should parse as source Rust")
}

fn extract_port_case(case: &CaseExpectation) -> (trust_vc_core::vc::VerificationContext, usize) {
    let file = quantifiers_port_file();
    let func = file
        .items
        .iter()
        .find_map(|item| match item {
            syn::Item::Fn(func) if func.sig.ident == case.case_id => Some(func),
            _ => None,
        })
        .unwrap_or_else(|| panic!("{} should exist in quantifiers port", case.case_id));
    let vc = extract_verification_conditions_with_file_context(&file, func).unwrap_or_else(|err| {
        panic!(
            "{} ({}) should extract: {err}",
            case.case_id, case.upstream_case_id
        )
    });
    let obligation_count = vc.obligations().len();
    (vc, obligation_count)
}

fn expect_verified(case: &CaseExpectation) {
    let (vc, obligations) = extract_port_case(case);
    assert!(
        obligations >= case.min_obligations,
        "{} ({}) should collect at least {} obligation(s), got {obligations}",
        case.case_id,
        case.upstream_case_id,
        case.min_obligations
    );

    match vc.verify() {
        VerifyResult::Verified => {}
        VerifyResult::Unknown { reason, .. } => panic!(
            "{} ({}) returned solver Unknown, which is not replacement evidence: {reason}",
            case.case_id, case.upstream_case_id
        ),
        other => panic!(
            "{} ({}) should verify, got: {other:?}",
            case.case_id, case.upstream_case_id
        ),
    }
}

fn expect_counterexample(case: &CaseExpectation) {
    let (vc, obligations) = extract_port_case(case);
    assert!(
        obligations >= case.min_obligations,
        "{} ({}) should collect at least {} obligation(s), got {obligations}",
        case.case_id,
        case.upstream_case_id,
        case.min_obligations
    );

    match vc.verify() {
        VerifyResult::Counterexample { .. } => {}
        VerifyResult::Unknown { reason, .. } => panic!(
            "{} ({}) returned solver Unknown, which is not replacement evidence: {reason}",
            case.case_id, case.upstream_case_id
        ),
        other => panic!(
            "{} ({}) should be rejected with a counterexample, got: {other:?}",
            case.case_id, case.upstream_case_id
        ),
    }
}

fn expect_error_contains_any(case: &str, upstream_case: &str, expected_fragments: &[&str]) {
    let path = quantifiers_port_path();
    let path = path
        .to_str()
        .expect("quantifiers port path should be UTF-8");
    let message = match verify_function_from_file(path, case) {
        Err(err) => err.to_string(),
        Ok(VerifyResult::Error { message }) => message,
        Ok(VerifyResult::Unknown { reason, .. }) => {
            panic!("{case} ({upstream_case}) returned solver Unknown, which is not replacement evidence: {reason}")
        }
        Ok(other) => {
            panic!("{case} ({upstream_case}) should fail closed with Error, got: {other:?}")
        }
    };

    assert!(
        expected_fragments
            .iter()
            .any(|expected_fragment| message.contains(expected_fragment)),
        "{case} ({upstream_case}) error should contain one of {expected_fragments:?}, got: {message}"
    );
}

fn lit_str(expr: &syn::Expr) -> String {
    match expr {
        syn::Expr::Lit(syn::ExprLit {
            lit: syn::Lit::Str(lit),
            ..
        }) => lit.value(),
        _ => panic!("expected string literal in metadata tuple"),
    }
}

fn lit_usize(expr: &syn::Expr) -> usize {
    match expr {
        syn::Expr::Lit(syn::ExprLit {
            lit: syn::Lit::Int(lit),
            ..
        }) => lit.base10_parse().expect("metadata count should be usize"),
        _ => panic!("expected integer literal in metadata tuple"),
    }
}

fn string_slice(expr: &syn::Expr) -> Vec<String> {
    match expr {
        syn::Expr::Reference(reference) => match reference.expr.as_ref() {
            syn::Expr::Array(array) => array.elems.iter().map(lit_str).collect(),
            _ => panic!("expected referenced string-slice array metadata"),
        },
        _ => panic!("expected referenced string-slice metadata"),
    }
}

fn referenced_array_const(file: &syn::File, const_name: &str) -> syn::ExprArray {
    let item_const = file
        .items
        .iter()
        .find_map(|item| match item {
            syn::Item::Const(item_const) if item_const.ident == const_name => Some(item_const),
            _ => None,
        })
        .unwrap_or_else(|| panic!("quantifiers port should expose {const_name}"));

    match item_const.expr.as_ref() {
        syn::Expr::Reference(reference) => match reference.expr.as_ref() {
            syn::Expr::Array(array) => array.clone(),
            _ => panic!("{const_name} should reference an array"),
        },
        _ => panic!("{const_name} should reference an array"),
    }
}

fn error_pattern_entries(file: &syn::File) -> BTreeMap<String, Vec<String>> {
    let array = referenced_array_const(file, "QUANTIFIERS_RS_EXPECTED_ERROR_PATTERNS");
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

        let case_id = lit_str(&tuple.elems[0]);
        let patterns = string_slice(&tuple.elems[1]);
        assert!(
            entries.insert(case_id.clone(), patterns).is_none(),
            "duplicate error-pattern metadata for {case_id}"
        );
    }

    entries
}

fn metadata_entries(file: &syn::File) -> Vec<CaseMetadata> {
    let array = referenced_array_const(file, "QUANTIFIERS_RS_EXPECTED_CASES");
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

        let case_id = lit_str(&tuple.elems[0]);
        assert!(
            seen.insert(case_id.clone()),
            "duplicate quantifiers metadata for {case_id}"
        );
        let expected_error_patterns = error_patterns.remove(&case_id).unwrap_or_default();
        entries.push(CaseMetadata {
            case_id,
            upstream_case_id: lit_str(&tuple.elems[1]),
            expected_verdict: lit_str(&tuple.elems[2]),
            min_obligations: lit_usize(&tuple.elems[3]),
            expected_error_patterns,
        });
    }

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
            entry["upstream_path"].as_str() == Some("source/rust_verify_test/tests/quantifiers.rs")
        })
        .expect("Verus manifest should contain quantifiers.rs row");

    row["expected_cases"]
        .as_array()
        .expect("quantifiers.rs row should contain expected_cases")
        .iter()
        .map(|entry| CaseMetadata {
            case_id: entry["case_id"]
                .as_str()
                .expect("case_id should be a string")
                .to_string(),
            upstream_case_id: entry
                .get("upstream_case_id")
                .and_then(serde_json::Value::as_str)
                .unwrap_or("")
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

const VERIFIED_CASES: &[CaseExpectation] = &[
    CaseExpectation {
        case_id: "test1",
        upstream_case_id: "",
        min_obligations: 2,
    },
    CaseExpectation {
        case_id: "simple_exists_witness",
        upstream_case_id: "",
        min_obligations: 1,
    },
    CaseExpectation {
        case_id: "simple_forall_reflexive",
        upstream_case_id: "",
        min_obligations: 1,
    },
    CaseExpectation {
        case_id: "inline_exists_nat_witness",
        upstream_case_id: "test1",
        min_obligations: 1,
    },
    CaseExpectation {
        case_id: "opaque_predicate_ground_exists_verified",
        upstream_case_id: "",
        min_obligations: 2,
    },
    CaseExpectation {
        case_id: "manual_trigger_expression_parity",
        upstream_case_id: "",
        min_obligations: 1,
    },
];

const COUNTEREXAMPLE_CASES: &[CaseExpectation] = &[
    CaseExpectation {
        case_id: "opaque_predicate_dual_forall_counterexample",
        upstream_case_id: "",
        min_obligations: 2,
    },
    CaseExpectation {
        case_id: "test1_fails",
        upstream_case_id: "",
        min_obligations: 1,
    },
    CaseExpectation {
        case_id: "simple_forall_fails",
        upstream_case_id: "",
        min_obligations: 1,
    },
];

const FAIL_CLOSED_CASES: &[(&str, &str, &[&str])] = &[
    (
        "invalid_trigger_without_bound_var_fails_closed",
        "",
        &["does not reference any bound variable"],
    ),
    (
        "forall_untyped_binder_fails_closed",
        "",
        &["requires an explicit type annotation", "'i'"],
    ),
    (
        "exists_empty_binder_fails_closed",
        "",
        &["at least one bound variable"],
    ),
    (
        "forall_unsupported_bound_type_fails_closed",
        "",
        &["Unsupported type", "Rc<i32>"],
    ),
    (
        "assert_forall_invalid_inner_trigger_attr_fails_closed",
        "assert_forall_invalid_attr",
        &["expected trigger attribute in assert forall"],
    ),
];

#[test]
fn quantifiers_rs_port_file_is_source_rust_syntax() {
    quantifiers_port_file();
}

#[test]
fn quantifiers_rs_pinned_upstream_case_shapes_are_present() {
    let path = pinned_upstream_quantifiers_path();
    if !path.exists() {
        eprintln!(
            "skipping pinned upstream quantifiers.rs shape check; missing {}",
            path.display()
        );
        return;
    }

    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", path.display()));
    for expected in [
        "#[test] test1",
        "#[test] test1_fails",
        "#[test] test2",
        "#[test] test3",
        "#[test] test1g",
        "#[test] test1g_fails",
        "#[test] test2g",
        "#[test] test3g",
        "#[test] test4",
        "#[test] test4_fails",
        "#[test] test_nested_assert_forall_by_regression_155",
        "#[test] manual_trigger",
        "#[test] assert_forall_triggers_regression_335",
        "#[test] assert_forall_triggers_regression_470",
        "#[test] assert_forall_invalid_attr",
        "#[test] forall_auto_parens_regression_378",
        "#[test] test_inner_triggers_broadcast_forall",
        "#[test] test_trigger_with_expression_should_be_disallowed_regression_1456",
        "assert(exists|i: nat| i >= 0 && tr(i as int));",
        "assert(exists|i| 0 <= i && tr(i));",
        "#[trigger] tr2(i as int)",
        "#![trigger s[i], s[j]]",
        "#![trigger f(k, z)]",
        "#![auto]",
        "#![autos]",
        "forall (|i: int, j: int| #![auto]",
        "#[trigger a(x)] c(x)",
    ] {
        assert!(
            source.contains(expected),
            "pinned upstream quantifiers.rs should still contain {expected}"
        );
    }
}

#[test]
fn quantifiers_rs_expected_case_metadata_is_exact_and_rejects_unknown() {
    let file = quantifiers_port_file();
    let source = std::fs::read_to_string(quantifiers_port_path())
        .expect("quantifiers port should be readable");
    assert!(
        source.contains("pub fn quantifiers_rs_expected_cases")
            && source.contains("pub fn quantifiers_rs_expected_error_patterns"),
        "quantifiers port should expose expected-case and expected-error-pattern metadata accessors"
    );

    let actual = metadata_entries(&file);
    let expected = vec![
        CaseMetadata {
            case_id: "test1".to_string(),
            upstream_case_id: "".to_string(),
            expected_verdict: "verified".to_string(),
            min_obligations: 2,
            expected_error_patterns: Vec::new(),
        },
        CaseMetadata {
            case_id: "simple_exists_witness".to_string(),
            upstream_case_id: "".to_string(),
            expected_verdict: "verified".to_string(),
            min_obligations: 1,
            expected_error_patterns: Vec::new(),
        },
        CaseMetadata {
            case_id: "simple_forall_reflexive".to_string(),
            upstream_case_id: "".to_string(),
            expected_verdict: "verified".to_string(),
            min_obligations: 1,
            expected_error_patterns: Vec::new(),
        },
        CaseMetadata {
            case_id: "inline_exists_nat_witness".to_string(),
            upstream_case_id: "test1".to_string(),
            expected_verdict: "verified".to_string(),
            min_obligations: 1,
            expected_error_patterns: Vec::new(),
        },
        CaseMetadata {
            case_id: "opaque_predicate_ground_exists_verified".to_string(),
            upstream_case_id: "".to_string(),
            expected_verdict: "verified".to_string(),
            min_obligations: 2,
            expected_error_patterns: Vec::new(),
        },
        CaseMetadata {
            case_id: "opaque_predicate_dual_forall_counterexample".to_string(),
            upstream_case_id: "".to_string(),
            expected_verdict: "counterexample".to_string(),
            min_obligations: 2,
            expected_error_patterns: Vec::new(),
        },
        CaseMetadata {
            case_id: "test1_fails".to_string(),
            upstream_case_id: "".to_string(),
            expected_verdict: "counterexample".to_string(),
            min_obligations: 1,
            expected_error_patterns: Vec::new(),
        },
        CaseMetadata {
            case_id: "simple_forall_fails".to_string(),
            upstream_case_id: "".to_string(),
            expected_verdict: "counterexample".to_string(),
            min_obligations: 1,
            expected_error_patterns: Vec::new(),
        },
        CaseMetadata {
            case_id: "manual_trigger_expression_parity".to_string(),
            upstream_case_id: "".to_string(),
            expected_verdict: "verified".to_string(),
            min_obligations: 1,
            expected_error_patterns: Vec::new(),
        },
        CaseMetadata {
            case_id: "invalid_trigger_without_bound_var_fails_closed".to_string(),
            upstream_case_id: "".to_string(),
            expected_verdict: "error".to_string(),
            min_obligations: 0,
            expected_error_patterns: vec!["does not reference any bound variable".to_string()],
        },
        CaseMetadata {
            case_id: "forall_untyped_binder_fails_closed".to_string(),
            upstream_case_id: "".to_string(),
            expected_verdict: "error".to_string(),
            min_obligations: 0,
            expected_error_patterns: vec![
                "requires an explicit type annotation".to_string(),
                "'i'".to_string(),
            ],
        },
        CaseMetadata {
            case_id: "exists_empty_binder_fails_closed".to_string(),
            upstream_case_id: "".to_string(),
            expected_verdict: "error".to_string(),
            min_obligations: 0,
            expected_error_patterns: vec!["at least one bound variable".to_string()],
        },
        CaseMetadata {
            case_id: "forall_unsupported_bound_type_fails_closed".to_string(),
            upstream_case_id: "".to_string(),
            expected_verdict: "error".to_string(),
            min_obligations: 0,
            expected_error_patterns: vec!["Unsupported type".to_string(), "Rc<i32>".to_string()],
        },
        CaseMetadata {
            case_id: "assert_forall_invalid_inner_trigger_attr_fails_closed".to_string(),
            upstream_case_id: "assert_forall_invalid_attr".to_string(),
            expected_verdict: "error".to_string(),
            min_obligations: 0,
            expected_error_patterns: vec!["expected trigger attribute in assert forall".to_string()],
        },
    ];

    assert_eq!(actual, expected);
    assert!(
        !metadata_entries(&file)
            .iter()
            .any(|case| case.expected_verdict == "unknown"),
        "Unknown outcomes must not be inventoried as replacement evidence"
    );
}

#[test]
fn quantifiers_rs_expected_case_metadata_matches_manifest() {
    let file = quantifiers_port_file();
    assert_eq!(metadata_entries(&file), manifest_expected_metadata());
}

#[test]
fn quantifiers_rs_expected_case_metadata_names_exist_in_port() {
    let file = quantifiers_port_file();
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
            "metadata case {} should name a function in quantifiers port",
            case.case_id
        );
    }
}

#[test]
fn quantifiers_rs_verified_subset_verifies_from_file() {
    for case in VERIFIED_CASES {
        expect_verified(case);
    }
}

#[test]
fn quantifiers_rs_counterexample_subset_is_rejected_from_file() {
    for case in COUNTEREXAMPLE_CASES {
        expect_counterexample(case);
    }
}

#[test]
fn quantifiers_rs_unsupported_boundaries_fail_closed_from_file() {
    for (case, upstream_case, expected_fragments) in FAIL_CLOSED_CASES {
        expect_error_contains_any(case, upstream_case, expected_fragments);
    }
}

#[test]
fn quantifiers_rs_manual_trigger_surface_is_preserved_from_file() {
    let case = CaseExpectation {
        case_id: "manual_trigger_expression_parity",
        upstream_case_id: "",
        min_obligations: 1,
    };
    let (vc, _) = extract_port_case(&case);
    let assertion = vc
        .obligations()
        .iter()
        .find(|obligation| obligation.name().starts_with("assertion"))
        .expect("manual trigger parity case should emit an assertion");

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
}
