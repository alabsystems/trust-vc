// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Executable guards for the first upstream mut_refs_closures.rs TrustVc scout.
//!
//! These tests intentionally keep the upstream file as an unsupported gap. They
//! pin only the Rust-valid mutable-reference subset that TrustVc can express
//! today, reject stale-value and explicit-false assertions, and keep direct
//! closure, reflection, resolvedness, and old/final surfaces fail-closed.

mod common;

use std::{
    collections::{BTreeMap, BTreeSet},
    path::{Path, PathBuf},
};
use trust_vc_core::{
    extract_verification_conditions_with_file_context, verify_function_from_file, VerifyResult,
};

fn mut_refs_closures_port_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/ported/mut_refs_closures.rs")
}

fn mut_refs_closures_upstream_path() -> PathBuf {
    common::pinned_verus_test_path("mut_refs_closures.rs")
}

fn verus_manifest_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/verus-tests.json")
}

#[derive(Debug, Eq, PartialEq)]
struct CaseMetadata {
    case_id: String,
    upstream_case_id: String,
    expected_verdict: String,
    min_obligations: usize,
    expected_error_patterns: Vec<String>,
}

fn verify_port_case_with_obligations(case: &str, upstream_case: &str) -> (VerifyResult, usize) {
    let path = mut_refs_closures_port_path();
    let path_str = path
        .to_str()
        .expect("mut_refs_closures port path should be UTF-8");
    let result = verify_function_from_file(path_str, case)
        .unwrap_or_else(|err| panic!("{case} ({upstream_case}) should extract: {err}"));

    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|err| panic!("{} should be readable: {err}", path.display()));
    let file = syn::parse_file(&source)
        .unwrap_or_else(|err| panic!("{} should parse as Rust syntax: {err}", path.display()));
    let function = file
        .items
        .iter()
        .find_map(|item| match item {
            syn::Item::Fn(function) if function.sig.ident == case => Some(function),
            _ => None,
        })
        .unwrap_or_else(|| {
            panic!(
                "{case} ({upstream_case}) should exist in {}",
                path.display()
            )
        });
    let vc = extract_verification_conditions_with_file_context(&file, function)
        .unwrap_or_else(|err| panic!("{case} ({upstream_case}) should extract: {err}"));
    let obligations = vc.obligations().len();

    (result, obligations)
}

fn fail_closed_message(case: &str, upstream_case: &str) -> String {
    let path = mut_refs_closures_port_path();
    let path = path
        .to_str()
        .expect("mut_refs_closures port path should be UTF-8");

    match verify_function_from_file(path, case) {
        Err(err) => err.to_string(),
        Ok(VerifyResult::Error { message }) => message,
        Ok(VerifyResult::Unknown { reason, .. }) => {
            panic!("{case} ({upstream_case}) returned solver Unknown, which is not stable evidence: {reason}")
        }
        Ok(other) => {
            panic!("{case} ({upstream_case}) should fail closed with Error, got: {other:?}")
        }
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
        .unwrap_or_else(|| panic!("mut_refs_closures port should define {const_name}"));

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
    let array = referenced_array_const(file, "MUT_REFS_CLOSURES_RS_EXPECTED_ERROR_PATTERNS");
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
            "duplicate mut_refs_closures error-pattern metadata for {case_id}"
        );
    }

    entries
}

fn metadata_entries(file: &syn::File) -> Vec<CaseMetadata> {
    let array = referenced_array_const(file, "MUT_REFS_CLOSURES_RS_EXPECTED_CASES");
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
            "duplicate mut_refs_closures metadata for {case_id}"
        );
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
                == Some("source/rust_verify_test/tests/mut_refs_closures.rs")
        })
        .expect("Verus manifest should contain mut_refs_closures.rs row");

    row["expected_cases"]
        .as_array()
        .expect("mut_refs_closures.rs row should contain expected_cases")
        .iter()
        .map(|case| CaseMetadata {
            case_id: case["case_id"]
                .as_str()
                .expect("manifest case should contain case_id")
                .to_string(),
            upstream_case_id: case
                .get("upstream_case_id")
                .and_then(serde_json::Value::as_str)
                .unwrap_or("")
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
            expected_error_patterns: case
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
        "mut_refs_closure_arg_direct_update_verified",
        "closure_with_mut_ref_arg_basic",
        "verified",
        1,
    ),
    (
        "mut_refs_closure_arg_two_direct_updates_verified",
        "closure_with_mut_ref_arg_basic",
        "verified",
        2,
    ),
    (
        "mut_refs_closure_arg_param_increment_verified",
        "",
        "verified",
        2,
    ),
    (
        "mut_refs_in_closure_rebind_body_verified",
        "mut_refs_in_closure",
        "verified",
        2,
    ),
    (
        "mut_refs_closure_returning_first_local_borrow_verified",
        "",
        "verified",
        2,
    ),
    (
        "mut_refs_closure_arg_wrong_old_value_counterexample",
        "closure_with_mut_ref_arg_basic",
        "counterexample",
        1,
    ),
    (
        "mut_refs_closure_arg_param_increment_wrong_value_counterexample",
        "",
        "counterexample",
        1,
    ),
    (
        "mut_refs_closure_arg_direct_update_false_tail_counterexample",
        "",
        "counterexample",
        1,
    ),
    (
        "mut_refs_in_closure_rebind_body_false_counterexample",
        "",
        "counterexample",
        1,
    ),
    (
        "mut_refs_closure_returning_first_local_false_tail_counterexample",
        "",
        "counterexample",
        1,
    ),
    (
        "mut_refs_closure_returning_tuple_field_borrow_currently_errors",
        "",
        "error",
        0,
    ),
    (
        "mut_refs_closure_direct_mut_ref_arg_application_currently_errors",
        "closure_with_mut_ref_arg_basic",
        "error",
        0,
    ),
    (
        "mut_refs_closure_returning_mut_ref_arg_currently_errors",
        "closure_returning_mut_ref_arg_basic",
        "error",
        0,
    ),
    (
        "mut_refs_closure_call_requires_currently_errors",
        "",
        "error",
        0,
    ),
    (
        "mut_refs_closure_call_ensures_currently_errors",
        "",
        "error",
        0,
    ),
    (
        "mut_refs_closure_old_final_post_state_currently_errors",
        "",
        "error",
        0,
    ),
    (
        "mut_refs_closure_has_resolved_capture_currently_errors",
        "",
        "error",
        0,
    ),
    (
        "mut_refs_closure_mut_ref_current_capture_currently_errors",
        "spec_capture_of_mut_ref",
        "error",
        0,
    ),
];

const VERIFIED_CASES: &[(&str, &str, usize)] = &[
    (
        "mut_refs_closure_arg_direct_update_verified",
        "closure_with_mut_ref_arg_basic",
        1,
    ),
    (
        "mut_refs_closure_arg_two_direct_updates_verified",
        "closure_with_mut_ref_arg_basic",
        2,
    ),
    ("mut_refs_closure_arg_param_increment_verified", "", 2),
    (
        "mut_refs_in_closure_rebind_body_verified",
        "mut_refs_in_closure",
        2,
    ),
    (
        "mut_refs_closure_returning_first_local_borrow_verified",
        "",
        2,
    ),
];

const COUNTEREXAMPLE_CASES: &[(&str, &str, usize)] = &[
    (
        "mut_refs_closure_arg_wrong_old_value_counterexample",
        "closure_with_mut_ref_arg_basic",
        1,
    ),
    (
        "mut_refs_closure_arg_param_increment_wrong_value_counterexample",
        "",
        1,
    ),
    (
        "mut_refs_closure_arg_direct_update_false_tail_counterexample",
        "",
        1,
    ),
    (
        "mut_refs_in_closure_rebind_body_false_counterexample",
        "",
        1,
    ),
    (
        "mut_refs_closure_returning_first_local_false_tail_counterexample",
        "",
        1,
    ),
];

const FAIL_CLOSED_CASES: &[(&str, &str, &[&str])] = &[
    (
        "mut_refs_closure_returning_tuple_field_borrow_currently_errors",
        "",
        &[
            "assignment through a dereferenced reference is unsupported",
            "dereferenced reference",
            "tuple/index/nested projections",
        ],
    ),
    (
        "mut_refs_closure_direct_mut_ref_arg_application_currently_errors",
        "closure_with_mut_ref_arg_basic",
        &["assignment through a dereferenced reference is unsupported"],
    ),
    (
        "mut_refs_closure_returning_mut_ref_arg_currently_errors",
        "closure_returning_mut_ref_arg_basic",
        &["assignment through a dereferenced reference is unsupported"],
    ),
    (
        "mut_refs_closure_call_requires_currently_errors",
        "",
        &[
            "call_requires",
            "unknown return type for function",
            "standalone closure",
            "assignment through a dereferenced reference is unsupported",
        ],
    ),
    (
        "mut_refs_closure_call_ensures_currently_errors",
        "",
        &[
            "call_ensures",
            "unknown return type for function",
            "standalone closure",
            "assignment through a dereferenced reference is unsupported",
        ],
    ),
    (
        "mut_refs_closure_old_final_post_state_currently_errors",
        "",
        &[
            "Unsupported old-state expression `old(...)`",
            "Failed to parse assert!() expression",
            "final",
            "old",
        ],
    ),
    (
        "mut_refs_closure_has_resolved_capture_currently_errors",
        "",
        &[
            "has_resolved",
            "unknown return type for function",
            "standalone closure",
        ],
    ),
    (
        // Deref-assignment `*x = 5` is now supported; this surface fails-closed
        // later on the `mut_ref_current(P)` prophecy-intrinsic call form. Accept
        // either sound fail-closed message.
        "mut_refs_closure_mut_ref_current_capture_currently_errors",
        "spec_capture_of_mut_ref",
        &[
            "assignment through a dereferenced reference is unsupported",
            "unknown return type for function",
        ],
    ),
];

#[test]
fn mut_refs_closures_rs_port_file_is_rust_syntax() {
    let source = std::fs::read_to_string(mut_refs_closures_port_path())
        .expect("mut_refs_closures port should be readable");
    syn::parse_file(&source).expect("mut_refs_closures port should parse as ordinary Rust syntax");
}

#[test]
fn mut_refs_closures_rs_upstream_fixture_is_present() {
    let path = mut_refs_closures_upstream_path();
    if !path.exists() {
        eprintln!(
            "skipping pinned upstream mut_refs_closures.rs shape check; missing {}",
            path.display()
        );
        return;
    }

    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", path.display()));

    for expected in [
        "#[test] closure_with_mut_ref_arg_basic",
        "#[test] closure_returning_mut_ref_arg_basic",
        "#[test] closure_with_mut_ref_arg_pass_as_arg",
        "#[test] closure_returning_mut_ref_arg_pass_as_arg",
        "#[test] closure_resolve_basic_move",
        "#[test] closure_resolve_basic_move2",
        "#[test] closure_resolve_basic_move_of_closure_param",
        "#[test] proof_closure_resolve_basic_move",
        "#[test] closure_resolve_nested_move",
        "#[test] closure_resolve_field_move",
        "#[test] closure_resolve_overlapping_moves",
        "#[test] closure_resolve_params",
        "#[test] mut_refs_in_closure",
        "#[test] spec_capture_of_mut_ref",
        "ensures *final(a) == *old(a) + 1",
        "*final(pair) == (*final(fst), old(pair).1)",
        "call_requires",
        "call_ensures",
        "has_resolved",
        "proof_fn[Once]",
        "mut_ref_current",
    ] {
        assert!(
            source.contains(expected),
            "pinned upstream mut_refs_closures.rs should still contain {expected}"
        );
    }
}

#[test]
fn mut_refs_closures_rs_expected_case_metadata_is_exact() {
    let source = std::fs::read_to_string(mut_refs_closures_port_path())
        .expect("mut_refs_closures port should be readable");
    let file = syn::parse_file(&source)
        .expect("mut_refs_closures port should parse as ordinary Rust syntax");
    for expected in [
        "MUT_REFS_CLOSURES_RS_EXPECTED_CASES",
        "mut_refs_closures_rs_expected_cases",
        "MUT_REFS_CLOSURES_RS_EXPECTED_ERROR_PATTERNS",
        "mut_refs_closures_rs_expected_error_patterns",
    ] {
        assert!(
            source.contains(expected),
            "mut_refs_closures port metadata should contain {expected}"
        );
    }

    assert_eq!(
        metadata_entries(&file),
        manifest_expected_metadata(),
        "mut_refs_closures.rs manifest expected_cases should match port metadata and error patterns exactly"
    );

    let mut expected_case_names = EXPECTED_CASE_METADATA
        .iter()
        .map(|(case, _, _, _)| *case)
        .collect::<Vec<_>>();
    expected_case_names.sort_unstable();

    let mut categorized_case_names = VERIFIED_CASES
        .iter()
        .map(|(case, _, _)| *case)
        .chain(COUNTEREXAMPLE_CASES.iter().map(|(case, _, _)| *case))
        .chain(FAIL_CLOSED_CASES.iter().map(|(case, _, _)| *case))
        .collect::<Vec<_>>();
    categorized_case_names.sort_unstable();

    assert_eq!(
        expected_case_names, categorized_case_names,
        "every metadata case should have exactly one regression expectation"
    );
}

#[test]
fn mut_refs_closures_rs_verified_subset_verifies_from_file() {
    for (case, upstream_case, min_obligations) in VERIFIED_CASES {
        let (result, obligations) = verify_port_case_with_obligations(case, upstream_case);
        assert!(
            obligations >= *min_obligations,
            "{case} ({upstream_case}) should collect at least {min_obligations} obligation(s), got {obligations}"
        );
        assert!(
            matches!(result, VerifyResult::Verified),
            "{case} ({upstream_case}) should verify, got: {result:?}"
        );
    }
}

#[test]
fn mut_refs_closures_rs_stale_value_assertion_is_rejected_from_file() {
    for (case, upstream_case, min_obligations) in COUNTEREXAMPLE_CASES {
        let (result, obligations) = verify_port_case_with_obligations(case, upstream_case);
        assert!(
            obligations >= *min_obligations,
            "{case} ({upstream_case}) should collect at least {min_obligations} obligation(s), got {obligations}"
        );
        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "{case} ({upstream_case}) should be rejected, got: {result:?}"
        );
    }
}

#[test]
fn mut_refs_closures_rs_direct_closure_surfaces_fail_closed_from_file() {
    for (case, upstream_case, expected_fragments) in FAIL_CLOSED_CASES {
        let message = fail_closed_message(case, upstream_case);
        assert!(
            expected_fragments
                .iter()
                .any(|expected_fragment| message.contains(expected_fragment)),
            "{case} ({upstream_case}) error should contain one of {expected_fragments:?}, got: {message}"
        );
    }
}
