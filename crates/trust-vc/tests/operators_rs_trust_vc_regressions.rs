// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Executable guards for the first upstream operators.rs TrustVc scout slice.
//!
//! These tests intentionally do not claim full Verus operators.rs parity. They
//! pin the currently executable signed arithmetic and concrete comparison/
//! logical evidence, shift-width and derived structural-equality witnesses, and
//! the primitive integer Add::add witness plus fail-closed custom trait-method
//! gap while operator
//! overloading, external trait specs, vstd operator specs, and diagnostic parity
//! remain unsupported.

mod common;

use std::path::{Path, PathBuf};
use trust_vc_core::{verify_function_from_file, VerifyResult};

fn operators_port_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/ported/operators.rs")
}

fn verus_manifest_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/verus-tests.json")
}

fn pinned_upstream_operators_path() -> PathBuf {
    common::pinned_verus_test_path("operators.rs")
}

fn verify_case(path: &str, case: &str, upstream_case: &str) -> VerifyResult {
    verify_function_from_file(path, case)
        .unwrap_or_else(|err| panic!("{case} ({upstream_case}) should extract: {err}"))
}

const VERIFIED_CASES: &[(&str, &str, usize)] = &[
    (
        "signed_division_rounds_toward_zero_verified",
        "test_arith/test_signed_div",
        4,
    ),
    (
        "signed_remainder_keeps_dividend_sign_verified",
        "test_arith/test_signed_mod",
        4,
    ),
    (
        "comparison_and_logical_operators_verified",
        "test_arith/test_eq_ineq",
        8,
    ),
    ("shift_left_in_range_u16_verified", "test_arith/test_shl", 1),
    (
        "shift_right_in_range_i16_verified",
        "test_arith/test_shr",
        1,
    ),
    (
        "derived_structural_equality_verified",
        "test_structural_eq",
        3,
    ),
    (
        "primitive_integer_add_method_verified",
        "test_integer_using_trait_add",
        2,
    ),
    // 2026-09-11: a hand-written `PartialEq::eq` METHOD call means its body (upstream test_eq_overload).
    ("custom_partial_eq_method_verified", "test_eq_overload", 3),
];

const COUNTEREXAMPLE_CASES: &[(&str, &str, usize)] = &[
    (
        "boolean_logical_operator_wrong_counterexample",
        "test_arith/test_eq_ineq",
        1,
    ),
    (
        "custom_partial_eq_method_negated_counterexample",
        "test_eq_overload",
        3,
    ),
    (
        "custom_partial_eq_method_structural_liar_counterexample",
        "test_eq_overload",
        3,
    ),
];

const FAIL_CLOSED_CASES: &[(&str, &str, &[&str])] = &[];

fn expect_error_contains_any(
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

    assert!(
        expected_fragments
            .iter()
            .any(|expected_fragment| message.contains(expected_fragment)),
        "{case} ({upstream_case}) error should contain one of {expected_fragments:?}, got: {message}"
    );
}

fn expected_case_inventory() -> Vec<(&'static str, &'static str, &'static str, usize)> {
    vec![
        (
            "signed_division_rounds_toward_zero_verified",
            "test_arith/test_signed_div",
            "verified",
            4,
        ),
        (
            "signed_remainder_keeps_dividend_sign_verified",
            "test_arith/test_signed_mod",
            "verified",
            4,
        ),
        (
            "comparison_and_logical_operators_verified",
            "test_arith/test_eq_ineq",
            "verified",
            8,
        ),
        (
            "shift_left_in_range_u16_verified",
            "test_arith/test_shl",
            "verified",
            1,
        ),
        (
            "shift_right_in_range_i16_verified",
            "test_arith/test_shr",
            "verified",
            1,
        ),
        (
            "derived_structural_equality_verified",
            "test_structural_eq",
            "verified",
            3,
        ),
        (
            "boolean_logical_operator_wrong_counterexample",
            "test_arith/test_eq_ineq",
            "counterexample",
            1,
        ),
        (
            "primitive_integer_add_method_verified",
            "test_integer_using_trait_add",
            "verified",
            2,
        ),
        (
            "custom_partial_eq_method_verified",
            "test_eq_overload",
            "verified",
            3,
        ),
        (
            "custom_partial_eq_method_negated_counterexample",
            "test_eq_overload",
            "counterexample",
            3,
        ),
        (
            "custom_partial_eq_method_structural_liar_counterexample",
            "test_eq_overload",
            "counterexample",
            3,
        ),
    ]
}

#[derive(Debug, Eq, PartialEq)]
struct CaseMetadata {
    case_id: String,
    upstream_case_id: String,
    expected_verdict: String,
    min_obligations: usize,
}

fn case_metadata_as_owned(
    cases: &[(&'static str, &'static str, &'static str, usize)],
) -> Vec<CaseMetadata> {
    cases
        .iter()
        .map(
            |(case_id, upstream_case_id, expected_verdict, min_obligations)| CaseMetadata {
                case_id: (*case_id).to_string(),
                upstream_case_id: (*upstream_case_id).to_string(),
                expected_verdict: (*expected_verdict).to_string(),
                min_obligations: *min_obligations,
            },
        )
        .collect()
}

fn error_patterns_as_owned(patterns: &[(&str, &str, &[&str])]) -> Vec<(String, Vec<String>)> {
    patterns
        .iter()
        .map(|(case_id, _, patterns)| {
            (
                (*case_id).to_string(),
                patterns
                    .iter()
                    .map(|pattern| (*pattern).to_string())
                    .collect(),
            )
        })
        .collect()
}

fn operators_port_file() -> syn::File {
    let source =
        std::fs::read_to_string(operators_port_path()).expect("operators port should be readable");
    syn::parse_file(&source).expect("operators port should parse as ordinary Rust syntax")
}

fn referenced_array_const(file: &syn::File, const_name: &str) -> syn::ExprArray {
    let const_item = file
        .items
        .iter()
        .find_map(|item| match item {
            syn::Item::Const(item) if item.ident == const_name => Some(item),
            _ => None,
        })
        .unwrap_or_else(|| panic!("operators port should define {const_name}"));
    let syn::Expr::Reference(reference) = const_item.expr.as_ref() else {
        panic!("{const_name} should be a referenced array literal");
    };
    let syn::Expr::Array(array) = reference.expr.as_ref() else {
        panic!("{const_name} should be a referenced array literal");
    };

    array.clone()
}

fn literal_string(expr: &syn::Expr) -> String {
    let syn::Expr::Lit(syn::ExprLit {
        lit: syn::Lit::Str(lit),
        ..
    }) = expr
    else {
        panic!("expected string literal");
    };

    lit.value()
}

fn literal_usize(expr: &syn::Expr) -> usize {
    let syn::Expr::Lit(syn::ExprLit {
        lit: syn::Lit::Int(lit),
        ..
    }) = expr
    else {
        panic!("expected integer literal");
    };

    lit.base10_parse()
        .expect("integer literal should fit usize")
}

fn string_slice(expr: &syn::Expr) -> Vec<String> {
    let syn::Expr::Reference(reference) = expr else {
        panic!("expected referenced string-slice literal");
    };
    let syn::Expr::Array(array) = reference.expr.as_ref() else {
        panic!("expected referenced string-slice literal");
    };

    array.elems.iter().map(literal_string).collect()
}

fn port_expected_case_metadata() -> Vec<CaseMetadata> {
    let file = operators_port_file();
    let array = referenced_array_const(&file, "OPERATORS_RS_EXPECTED_CASES");
    array
        .elems
        .iter()
        .map(|entry| {
            let syn::Expr::Tuple(tuple) = entry else {
                panic!("OPERATORS_RS_EXPECTED_CASES entries should be tuples");
            };
            assert_eq!(
                tuple.elems.len(),
                4,
                "operators expected-case tuple arity should stay fixed"
            );
            CaseMetadata {
                case_id: literal_string(&tuple.elems[0]),
                upstream_case_id: literal_string(&tuple.elems[1]),
                expected_verdict: literal_string(&tuple.elems[2]),
                min_obligations: literal_usize(&tuple.elems[3]),
            }
        })
        .collect()
}

fn port_fail_closed_error_pattern_metadata() -> Vec<(String, Vec<String>)> {
    let file = operators_port_file();
    let array = referenced_array_const(&file, "OPERATORS_RS_FAIL_CLOSED_ERROR_PATTERNS");
    array
        .elems
        .iter()
        .map(|entry| {
            let syn::Expr::Tuple(tuple) = entry else {
                panic!("OPERATORS_RS_FAIL_CLOSED_ERROR_PATTERNS entries should be tuples");
            };
            assert_eq!(
                tuple.elems.len(),
                2,
                "operators fail-closed tuple arity should stay fixed"
            );

            (
                literal_string(&tuple.elems[0]),
                string_slice(&tuple.elems[1]),
            )
        })
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
            entry["upstream_path"].as_str() == Some("source/rust_verify_test/tests/operators.rs")
        })
        .expect("Verus manifest should contain operators.rs row")
        .clone()
}

fn manifest_expected_case_metadata() -> Vec<CaseMetadata> {
    manifest_row()["expected_cases"]
        .as_array()
        .expect("operators manifest row should contain expected_cases")
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
        })
        .collect()
}

fn manifest_fail_closed_error_pattern_metadata() -> Vec<(String, Vec<String>)> {
    manifest_row()["expected_cases"]
        .as_array()
        .expect("operators manifest row should contain expected_cases")
        .iter()
        .filter_map(|case| {
            let patterns = case["expected_error_patterns"].as_array()?;
            Some((
                case["case_id"]
                    .as_str()
                    .expect("manifest case should contain case_id")
                    .to_string(),
                patterns
                    .iter()
                    .map(|pattern| {
                        pattern
                            .as_str()
                            .expect("expected_error_patterns entries should be strings")
                            .to_string()
                    })
                    .collect(),
            ))
        })
        .collect()
}

#[test]
fn operators_rs_port_file_is_rust_syntax() {
    let source =
        std::fs::read_to_string(operators_port_path()).expect("operators port should be readable");
    syn::parse_file(&source).expect("operators port should parse as ordinary Rust syntax");
}

#[test]
fn operators_rs_pinned_upstream_case_shapes_are_present() {
    let path = pinned_upstream_operators_path();
    if !path.exists() {
        eprintln!(
            "skipping pinned upstream operators.rs shape check; missing {}",
            path.display()
        );
        return;
    }

    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", path.display()));
    for expected in [
        "#[test] test_integer_using_trait_add",
        "#[test] test_integer_trait_op_call_when_no_vstd",
        "#[test] test_integer_op_different_from_generic_op_when_no_vstd_fails",
        "#[test] test_partial_eq_overload",
        "#[test] test_cmp_usize_diff",
        "#[test] test_trait_add",
        "#[test] test_operator_overload",
        "#[test] test_call_operator_trait_method",
        "#[test] test_operator_not_implemented",
        "#[test] test_eq_overload",
        "#[test] test_structural_eq",
        "#[test] test_arith",
        "fn test_shl(u: u16)",
        "fn test_shr(u: i16)",
        "fn test_signed_div()",
        "fn test_signed_mod()",
    ] {
        assert!(
            source.contains(expected),
            "pinned upstream operators.rs should still contain {expected}"
        );
    }
}

#[test]
fn operators_rs_expected_case_metadata_is_exact() {
    let expected = case_metadata_as_owned(&expected_case_inventory());
    let actual = port_expected_case_metadata();

    assert_eq!(actual, expected, "operators metadata should be exact");
}

#[test]
fn operators_rs_expected_case_metadata_matches_manifest() {
    assert_eq!(
        manifest_expected_case_metadata(),
        port_expected_case_metadata(),
        "operators manifest expected_cases should match port metadata exactly"
    );

    assert_eq!(
        manifest_fail_closed_error_pattern_metadata(),
        port_fail_closed_error_pattern_metadata(),
        "operators manifest expected_error_patterns should match fail-closed metadata exactly"
    );

    assert_eq!(
        port_fail_closed_error_pattern_metadata(),
        error_patterns_as_owned(FAIL_CLOSED_CASES),
        "operators port fail-closed metadata should match runtime error checks exactly"
    );
}

#[test]
fn operators_rs_verified_subset_verifies_from_file() {
    let path = operators_port_path();
    let path = path.to_str().expect("operators port path should be UTF-8");

    for (case, upstream_case, _) in VERIFIED_CASES {
        let result = verify_case(path, case, upstream_case);
        assert!(
            matches!(result, VerifyResult::Verified),
            "{case} ({upstream_case}) should verify, got: {result:?}"
        );
    }
}

#[test]
fn operators_rs_counterexample_subset_is_rejected_from_file() {
    let path = operators_port_path();
    let path = path.to_str().expect("operators port path should be UTF-8");

    for (case, upstream_case, _) in COUNTEREXAMPLE_CASES {
        let result = verify_case(path, case, upstream_case);
        eprintln!("{case} ({upstream_case}) => {result:?}");
        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "{case} ({upstream_case}) should produce a counterexample, got: {result:?}"
        );
    }
}

#[test]
fn operators_rs_trait_method_boundaries_fail_closed_from_file() {
    let path = operators_port_path();
    let path = path.to_str().expect("operators port path should be UTF-8");

    for (case, upstream_case, expected_fragments) in FAIL_CLOSED_CASES {
        expect_error_contains_any(path, case, upstream_case, expected_fragments);
    }
}
