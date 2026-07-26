// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Executable guards for the upstream modes.rs TrustVc scout slice.
//!
//! These tests intentionally keep upstream modes.rs as an unsupported gap. They
//! pin only Rust-valid executable TrustVc mode behavior, stable counterexamples,
//! upstream source-shape anchors, and fail-closed unsupported Verus mode
//! boundaries.

mod common;

use std::path::{Path, PathBuf};
use trust_vc_core::{
    extract_verification_conditions_with_file_context, verify_function_from_file, VerifyResult,
};

fn modes_port_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/ported/modes.rs")
}

fn pinned_upstream_modes_path() -> PathBuf {
    common::pinned_verus_test_path("modes.rs")
}

fn verus_manifest_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/verus-tests.json")
}

#[derive(Debug, PartialEq, Eq)]
struct CaseMetadata {
    case_id: String,
    upstream_case_id: String,
    expected_verdict: String,
    min_obligations: usize,
    expected_error_patterns: Vec<String>,
}

fn verify_port_case(case: &str, upstream_case: &str) -> (VerifyResult, usize) {
    let path = modes_port_path();
    let path_str = path.to_str().expect("modes port path should be UTF-8");

    let result = verify_function_from_file(path_str, case)
        .unwrap_or_else(|err| panic!("{case} ({upstream_case}) should extract: {err}"));

    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|err| panic!("{} should be readable: {err}", path.display()));
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

    (result, vc.obligations().len())
}

fn fail_closed_message(case: &str, upstream_case: &str) -> String {
    let path = modes_port_path();
    let path = path.to_str().expect("modes port path should be UTF-8");

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

fn literal_string(expr: &syn::Expr) -> String {
    match expr {
        syn::Expr::Lit(syn::ExprLit {
            lit: syn::Lit::Str(lit),
            ..
        }) => lit.value(),
        _ => panic!("expected string literal in modes metadata"),
    }
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

fn const_array<'a>(
    file: &'a syn::File,
    name: &str,
) -> &'a syn::punctuated::Punctuated<syn::Expr, syn::Token![,]> {
    let item = file
        .items
        .iter()
        .find_map(|item| match item {
            syn::Item::Const(item) if item.ident == name => Some(item),
            _ => None,
        })
        .unwrap_or_else(|| panic!("modes port should define {name}"));

    let syn::Expr::Reference(reference) = item.expr.as_ref() else {
        panic!("{name} should be a borrowed array");
    };
    let syn::Expr::Array(array) = reference.expr.as_ref() else {
        panic!("{name} should borrow an array literal");
    };

    &array.elems
}

fn port_expected_case_metadata() -> Vec<(String, String, String, usize)> {
    let source = std::fs::read_to_string(modes_port_path()).expect("modes port should be readable");
    let file = syn::parse_file(&source).expect("modes port should parse as ordinary Rust syntax");

    const_array(&file, "MODES_RS_EXPECTED_CASES")
        .iter()
        .map(|entry| {
            let syn::Expr::Tuple(tuple) = entry else {
                panic!("expected-case metadata entries should be tuples");
            };
            assert_eq!(
                tuple.elems.len(),
                4,
                "expected-case metadata entries should be (case, upstream_case, verdict, min_obligations)"
            );

            let min_obligations = match &tuple.elems[3] {
                syn::Expr::Lit(syn::ExprLit {
                    lit: syn::Lit::Int(lit),
                    ..
                }) => lit.base10_parse::<usize>().expect("min_obligations should be usize"),
                _ => panic!("expected integer literal for min_obligations"),
            };

            (
                literal_string(&tuple.elems[0]),
                literal_string(&tuple.elems[1]),
                literal_string(&tuple.elems[2]),
                min_obligations,
            )
        })
        .collect()
}

fn port_fail_closed_error_pattern_metadata() -> Vec<(String, Vec<String>)> {
    let source = std::fs::read_to_string(modes_port_path()).expect("modes port should be readable");
    let file = syn::parse_file(&source).expect("modes port should parse as ordinary Rust syntax");

    const_array(&file, "MODES_RS_EXPECTED_ERROR_PATTERNS")
        .iter()
        .map(|entry| {
            let syn::Expr::Tuple(tuple) = entry else {
                panic!("error-pattern metadata entries should be tuples");
            };
            assert_eq!(
                tuple.elems.len(),
                2,
                "error-pattern metadata entries should be (case, patterns)"
            );

            (
                literal_string(&tuple.elems[0]),
                string_slice(&tuple.elems[1]),
            )
        })
        .collect()
}

fn expected_fail_closed_error_pattern_metadata_from_tests() -> Vec<(String, Vec<String>)> {
    FAIL_CLOSED_CASES
        .iter()
        .map(|(case, _, patterns)| {
            (
                (*case).to_string(),
                patterns
                    .iter()
                    .map(|pattern| (*pattern).to_string())
                    .collect(),
            )
        })
        .collect()
}

fn expected_case_metadata_from_tests() -> Vec<CaseMetadata> {
    let error_patterns = expected_fail_closed_error_pattern_metadata_from_tests();

    VERIFIED_CASES
        .iter()
        .map(|(case, upstream_case, min_obligations)| CaseMetadata {
            case_id: (*case).to_string(),
            upstream_case_id: (*upstream_case).to_string(),
            expected_verdict: "verified".to_string(),
            min_obligations: *min_obligations,
            expected_error_patterns: Vec::new(),
        })
        .chain(
            COUNTEREXAMPLE_CASES
                .iter()
                .map(|(case, upstream_case, min_obligations)| CaseMetadata {
                    case_id: (*case).to_string(),
                    upstream_case_id: (*upstream_case).to_string(),
                    expected_verdict: "counterexample".to_string(),
                    min_obligations: *min_obligations,
                    expected_error_patterns: Vec::new(),
                }),
        )
        .chain(FAIL_CLOSED_CASES.iter().map(|(case, upstream_case, _)| {
            CaseMetadata {
                case_id: (*case).to_string(),
                upstream_case_id: (*upstream_case).to_string(),
                expected_verdict: "error".to_string(),
                min_obligations: 0,
                expected_error_patterns: error_patterns
                    .iter()
                    .find_map(|(pattern_case, patterns)| {
                        (pattern_case == case).then(|| patterns.clone())
                    })
                    .unwrap_or_default(),
            }
        }))
        .collect()
}

fn port_case_metadata() -> Vec<CaseMetadata> {
    let error_patterns = port_fail_closed_error_pattern_metadata();

    port_expected_case_metadata()
        .into_iter()
        .map(
            |(case_id, upstream_case_id, expected_verdict, min_obligations)| CaseMetadata {
                expected_error_patterns: error_patterns
                    .iter()
                    .find_map(|(pattern_case, patterns)| {
                        (*pattern_case == case_id).then(|| patterns.clone())
                    })
                    .unwrap_or_default(),
                case_id,
                upstream_case_id,
                expected_verdict,
                min_obligations,
            },
        )
        .collect()
}

fn manifest_row() -> serde_json::Value {
    let source =
        std::fs::read_to_string(verus_manifest_path()).expect("Verus manifest should be readable");
    let manifest: serde_json::Value =
        serde_json::from_str(&source).expect("Verus manifest should parse as JSON");
    manifest["entries"]
        .as_array()
        .expect("Verus manifest should contain entries")
        .iter()
        .find(|entry| {
            entry["upstream_path"].as_str() == Some("source/rust_verify_test/tests/modes.rs")
        })
        .expect("Verus manifest should contain modes.rs row")
        .clone()
}

fn manifest_case_metadata() -> Vec<CaseMetadata> {
    manifest_row()["expected_cases"]
        .as_array()
        .expect("modes manifest row should contain expected_cases")
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

const VERIFIED_CASES: &[(&str, &str, usize)] = &[
    ("mode_exec_struct_field_projection_verified", "", 2),
    ("mode_exec_tuple_projection_verified", "", 2),
    ("mode_exec_if_expression_verified", "", 2),
    ("mode_exec_return_value_verified", "", 1),
    ("mode_spec_if_expression_verified", "", 1),
    ("mode_spec_can_call_spec_helper_verified", "", 1),
    ("proof_mode_can_call_spec_helper_verified", "", 1),
    ("proof_mode_can_call_proof_helper_verified", "", 1),
    ("ghost_param_view_reflexive", "fn_param_wrappers", 1),
    ("ghost_param_copyable_verified", "", 1),
    (
        "tracked_param_wrapper_is_accepted",
        "tracked_tracked_get",
        1,
    ),
    ("tracked_copy_wrapper_reuse_verified", "", 1),
    ("empty_tuple_wrappers_verified", "", 1),
    ("mode_ghost_tuple_projection_verified", "", 2),
];

const COUNTEREXAMPLE_CASES: &[(&str, &str, usize)] = &[
    (
        "mode_exec_tuple_projection_wrong_value_counterexample",
        "",
        1,
    ),
    (
        "ghost_param_view_wrong_value_counterexample",
        "fn_param_wrappers",
        1,
    ),
    ("ghost_param_copy_wrong_value_counterexample", "", 1),
    ("tracked_wrapper_false_assert_counterexample", "", 1),
];

const FAIL_CLOSED_CASES: &[(&str, &str, &[&str])] = &[
    (
        "spec_mode_proof_call_compute_fails_closed",
        "",
        &["mode_separation_proof_helper"],
    ),
    (
        "mode_old_in_exec_currently_blocked",
        "",
        &["Unsupported old-state expression `old(...)`", "old"],
    ),
    (
        "mode_ghost_constructor_in_exec_currently_blocked",
        "",
        &["Ghost::new"],
    ),
    ("mode_tracked_get_currently_blocked", "", &["get"]),
    ("mode_tracked_borrow_currently_blocked", "", &["borrow"]),
    (
        "fn_param_wrapper_pattern_currently_blocked",
        "fn_param_wrappers",
        &["Unsupported parameter pattern"],
    ),
];

#[test]
fn modes_rs_port_file_is_rust_syntax() {
    let source = std::fs::read_to_string(modes_port_path()).expect("modes port should be readable");
    syn::parse_file(&source).expect("modes port should parse as ordinary Rust syntax");
}

#[test]
fn modes_rs_pinned_upstream_case_shapes_are_present() {
    let path = pinned_upstream_modes_path();
    if !path.exists() {
        eprintln!(
            "skipping pinned upstream modes.rs shape check; missing {}",
            path.display()
        );
        return;
    }

    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", path.display()));
    for expected in [
        "#[test] struct1",
        "#[test] verus_struct1",
        "#[test] struct_fails1",
        "#[test] tuple1",
        "#[test] tuple_fails1",
        "#[test] eq_mode",
        "#[test] if_spec_cond",
        "#[test] if_spec_cond_proof",
        "#[test] regression_int_if",
        "#[test] ret_mode",
        "#[test] ret_mode_fail2",
        "#[test] assign_from_proof",
        "#[test] ghost_wrapper_assign_fail1",
        "#[test] ghost_wrapper_call_fail1",
        "#[test] tracked_ghost_typ_params_make",
        "#[test] tracked_tracked_typ_params_misc",
        "#[test] test_struct_pattern_fields_out_of_order_success_issue_348",
        "#[test] initialize_proof_var_in_exec",
        "#[test] assign_proof_var_in_exec",
        "#[test] ghost_decl_enters_ghost_code",
        "#[test] fn_param_wrappers",
        "fn test1(Ghost(g): Ghost<int>, Tracked(t): Tracked<S>)",
        "#[test] fn_param_wrappers_mut",
        "#[test] ghost_tracked_new1",
        "#[test] ghost_tracked_new_fail1",
        "#[test] destructure_tracked_shorthand",
        "#[test] ghost_wrapper_is_copyable",
        "#[test] old_in_exec_mode_issue922",
        "#[test] empty_tuple_ghost",
        "#[test] tracked_tracked_get",
        "#[test] ghost_tracked_borrow",
        "#[test] match_in_pure_expr",
    ] {
        assert!(
            source.contains(expected),
            "pinned upstream modes.rs should still contain {expected}"
        );
    }
}

#[test]
fn modes_rs_expected_case_metadata_is_exact() {
    let source = std::fs::read_to_string(modes_port_path()).expect("modes port should be readable");
    assert!(
        source.contains("MODES_RS_EXPECTED_CASES")
            && source.contains("modes_rs_expected_cases")
            && source.contains("MODES_RS_EXPECTED_ERROR_PATTERNS")
            && source.contains("modes_rs_expected_error_patterns"),
        "modes port should expose expected-case and expected-error-pattern metadata helpers"
    );
    assert_eq!(
        port_case_metadata(),
        expected_case_metadata_from_tests(),
        "modes port expected-case metadata should match the regression inventory"
    );
}

#[test]
fn modes_rs_fail_closed_error_pattern_metadata_is_exact() {
    let source = std::fs::read_to_string(modes_port_path()).expect("modes port should be readable");
    assert!(
        source.contains("MODES_RS_FAIL_CLOSED_ERROR_PATTERNS")
            && source.contains("modes_rs_fail_closed_error_patterns"),
        "modes port should expose fail-closed error-pattern metadata helpers"
    );

    let actual = port_fail_closed_error_pattern_metadata();
    assert_eq!(
        actual,
        expected_fail_closed_error_pattern_metadata_from_tests(),
        "modes fail-closed error-pattern metadata should match the regression inventory exactly"
    );
    for (case, patterns) in actual {
        assert!(
            !patterns.is_empty(),
            "{case} should declare at least one stable expected_error_patterns fragment"
        );
    }
}

#[test]
fn modes_rs_expected_case_metadata_matches_manifest() {
    assert_eq!(
        port_case_metadata(),
        manifest_case_metadata(),
        "modes manifest expected_cases should match port metadata, including expected_error_patterns, exactly"
    );
}

#[test]
fn modes_rs_error_cases_have_expected_error_patterns() {
    let mut patterns_by_case = port_fail_closed_error_pattern_metadata();

    for expected_case in port_case_metadata() {
        if expected_case.expected_verdict == "error" {
            assert_eq!(
                expected_case.min_obligations, 0,
                "{} ({}) error evidence should not declare obligations",
                expected_case.case_id, expected_case.upstream_case_id
            );
            let patterns = patterns_by_case
                .iter()
                .position(|(case, _)| case == &expected_case.case_id)
                .map(|index| patterns_by_case.remove(index).1)
                .unwrap_or_else(|| {
                    panic!(
                        "{} ({}) should have expected_error_patterns metadata",
                        expected_case.case_id, expected_case.upstream_case_id
                    )
                });
            assert!(
                !patterns.is_empty(),
                "{} ({}) expected_error_patterns should not be empty",
                expected_case.case_id,
                expected_case.upstream_case_id
            );
        } else {
            assert!(
                !patterns_by_case
                    .iter()
                    .any(|(case, _)| case == &expected_case.case_id),
                "{} ({}) should not declare expected_error_patterns for {} evidence",
                expected_case.case_id,
                expected_case.upstream_case_id,
                expected_case.expected_verdict
            );
        }
    }

    assert!(
        patterns_by_case.is_empty(),
        "expected_error_patterns should not contain orphan cases: {patterns_by_case:?}"
    );
}

#[test]
fn modes_rs_verified_subset_verifies_from_file() {
    for (case, upstream_case, min_obligations) in VERIFIED_CASES {
        let (result, obligations) = verify_port_case(case, upstream_case);
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
fn modes_rs_counterexample_subset_is_rejected_from_file() {
    for (case, upstream_case, min_obligations) in COUNTEREXAMPLE_CASES {
        let (result, obligations) = verify_port_case(case, upstream_case);
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
fn modes_rs_unsupported_boundaries_fail_closed_from_file() {
    for (case, upstream_case, expected_fragments) in FAIL_CLOSED_CASES {
        let message = fail_closed_message(case, upstream_case);
        for expected_fragment in *expected_fragments {
            assert!(
                message.contains(expected_fragment),
                "{case} ({upstream_case}) error should contain {expected_fragment:?}, got: {message}"
            );
        }
    }
}
