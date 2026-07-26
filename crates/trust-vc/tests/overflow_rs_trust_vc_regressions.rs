// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Executable guards for the first upstream overflow.rs TrustVc scout slice.
//!
//! These tests intentionally keep `source/rust_verify_test/tests/overflow.rs`
//! as an unsupported gap. They pin only stable TrustVc behavior for a small
//! Rust-valid arithmetic/div-rem/const/shift subset, primitive Add::add
//! lowering, fail-closed unsupported boundaries, and avoid Unknown outcomes as
//! evidence.

mod common;

use std::{
    collections::{BTreeMap, BTreeSet},
    path::{Path, PathBuf},
};
use trust_vc_core::{
    extract_verification_conditions_with_file_context, verify_function_from_file, VerifyResult,
};

fn overflow_port_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/ported/overflow.rs")
}

fn verus_manifest_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/verus-tests.json")
}

fn pinned_upstream_overflow_path() -> PathBuf {
    common::pinned_verus_test_path("overflow.rs")
}

fn verify_case(path: &str, case: &str, upstream_case: &str) -> VerifyResult {
    verify_function_from_file(path, case)
        .unwrap_or_else(|err| panic!("{case} ({upstream_case}) should extract: {err}"))
}

type ExpectedCase = (&'static str, &'static str, &'static str, usize);

#[derive(Debug, Eq, PartialEq)]
struct CaseMetadata {
    case_id: String,
    upstream_case_id: String,
    expected_verdict: String,
    min_obligations: usize,
    expected_error_patterns: Vec<String>,
}

const EXPECTED_CASES: &[ExpectedCase] = &[
    (
        "overflow_u64_add_by_two_guard_verified",
        "test_overflow_fails_1",
        "verified",
        2,
    ),
    (
        "overflow_u64_two_adds_guard_verified",
        "test_overflow_spec_fails_2",
        "verified",
        2,
    ),
    (
        "overflow_ensures_pass_usize_guard_verified",
        "test_overflow_ensures_pass",
        "verified",
        2,
    ),
    (
        "divide_by_nonzero_u8_guard_verified",
        "test_divide_by_zero",
        "verified",
        2,
    ),
    (
        "remainder_by_nonzero_u8_guard_verified",
        "test_divide_by_zero",
        "verified",
        1,
    ),
    (
        "const_u8_add_in_range_verified",
        "test_const_ok",
        "verified",
        1,
    ),
    (
        "underflow_u64_sub_guard_verified",
        "underflow",
        "verified",
        2,
    ),
    (
        "bit_shift_in_range_u16_verified",
        "bit_shift_overflow",
        "verified",
        1,
    ),
    (
        "bit_shift_left_in_range_u16_verified",
        "bit_shift_overflow",
        "verified",
        1,
    ),
    (
        "bit_shift_left_usize_bits_minus_one_verified",
        "bit_shift_overflow",
        "verified",
        1,
    ),
    (
        "nonlinear_unsigned_div_rem_guard_verified",
        "nonlinear_ops_dont_overflow_unsigned",
        "verified",
        2,
    ),
    (
        "arith_bounds_add_guard_verified",
        "arith_bounds_asserted_and_assumed",
        "verified",
        2,
    ),
    (
        "overflow_fails_u64_add_by_two_counterexample",
        "test_overflow_fails_1",
        "counterexample",
        1,
    ),
    (
        "overflow_two_u64_adds_second_counterexample",
        "test_overflow_fails_2",
        "counterexample",
        1,
    ),
    (
        "overflow_fails_usize_unbounded_counterexample",
        "test_overflow_fails_usize",
        "counterexample",
        1,
    ),
    (
        "divide_by_zero_guard_missing_counterexample",
        "test_divide_by_zero",
        "counterexample",
        1,
    ),
    (
        "remainder_by_zero_guard_missing_counterexample",
        "test_divide_by_zero",
        "counterexample",
        1,
    ),
    (
        "underflow_u64_sub_counterexample",
        "underflow",
        "counterexample",
        1,
    ),
    (
        "bit_shift_width_boundary_counterexample",
        "bit_shift_overflow",
        "counterexample",
        1,
    ),
    (
        "bit_shift_left_width_boundary_counterexample",
        "bit_shift_overflow",
        "counterexample",
        1,
    ),
    (
        "bit_shift_usize_bits_boundary_counterexample",
        "bit_shift_overflow",
        "counterexample",
        1,
    ),
    (
        "arith_bounds_add_missing_guard_counterexample",
        "arith_bounds_asserted_and_assumed",
        "counterexample",
        1,
    ),
    (
        "primitive_add_trait_method_verified",
        "test_overflow_spec_pass",
        "verified",
        2,
    ),
    (
        "const_item_initializer_overflow_counterexample",
        "test_const_fail",
        "counterexample",
        1,
    ),
    (
        "static_item_initializer_overflow_counterexample",
        "test_static_fail",
        "counterexample",
        1,
    ),
    (
        "bit_shift_width_mismatch_u32_counterexample",
        "bit_shift_width_mismatch",
        "counterexample",
        1,
    ),
    (
        "bit_shift_width_mismatch_signed_counterexample",
        "bit_shift_width_mismatch_signed",
        "counterexample",
        1,
    ),
    (
        "bit_shift_right_nonzero_left_arg_u16_verified",
        "bit_shift_overflow",
        "verified",
        1,
    ),
    (
        "bit_shift_width_above_boundary_counterexample",
        "bit_shift_overflow",
        "counterexample",
        1,
    ),
    (
        "bit_shift_underflow_signed_fail_closed",
        "bit_shift_underflow",
        "error",
        1,
    ),
    (
        "bit_shift_unsigned_lhs_signed_shift_fail_closed",
        "bit_shift_unsigned_shift_signed",
        "error",
        1,
    ),
];

fn expected_metadata() -> Vec<CaseMetadata> {
    let mut error_patterns = fail_closed_error_patterns_owned();
    let metadata = EXPECTED_CASES
        .iter()
        .map(|(case, upstream_case, verdict, min_obligations)| {
            let expected_error_patterns = error_patterns.remove(*case).unwrap_or_default();
            CaseMetadata {
                case_id: (*case).to_owned(),
                upstream_case_id: (*upstream_case).to_owned(),
                expected_verdict: (*verdict).to_owned(),
                min_obligations: *min_obligations,
                expected_error_patterns,
            }
        })
        .collect();
    assert!(
        error_patterns.is_empty(),
        "error-pattern metadata should not contain orphan cases: {error_patterns:?}"
    );
    metadata
}

fn fail_closed_error_patterns_owned() -> BTreeMap<&'static str, Vec<String>> {
    FAIL_CLOSED_CASES
        .iter()
        .map(|(case, _, patterns)| {
            (
                *case,
                patterns
                    .iter()
                    .map(|pattern| (*pattern).to_owned())
                    .collect(),
            )
        })
        .collect()
}

fn referenced_array_const(file: &syn::File, const_name: &str) -> syn::ExprArray {
    let const_item = file
        .items
        .iter()
        .find_map(|item| match item {
            syn::Item::Const(item_const) if item_const.ident == const_name => Some(item_const),
            _ => None,
        })
        .unwrap_or_else(|| panic!("overflow port should define {const_name}"));
    let syn::Expr::Reference(reference) = const_item.expr.as_ref() else {
        panic!("{const_name} should be a referenced array");
    };
    let syn::Expr::Array(array) = reference.expr.as_ref() else {
        panic!("{const_name} should reference an array literal");
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

    array
        .elems
        .iter()
        .map(|expr| string_lit(expr, "error pattern"))
        .collect()
}

fn error_pattern_entries(file: &syn::File) -> BTreeMap<String, Vec<String>> {
    let array = referenced_array_const(file, "OVERFLOW_RS_FAIL_CLOSED_ERROR_PATTERNS");
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

        let case_id = string_lit(&tuple.elems[0], "case id");
        let patterns = string_slice(&tuple.elems[1]);
        assert!(
            entries.insert(case_id.clone(), patterns).is_none(),
            "duplicate overflow error-pattern metadata for {case_id}"
        );
    }

    entries
}

fn overflow_metadata_cases_from_source(file: &syn::File) -> Vec<CaseMetadata> {
    let array = referenced_array_const(file, "OVERFLOW_RS_EXPECTED_CASES");
    let mut error_patterns = error_pattern_entries(file);
    let mut seen = BTreeSet::new();
    let mut entries = Vec::new();

    for expr in &array.elems {
        let syn::Expr::Tuple(tuple) = expr else {
            panic!("OVERFLOW_RS_EXPECTED_CASES entries should be tuples");
        };
        assert_eq!(
            tuple.elems.len(),
            4,
            "overflow metadata entries should have four fields"
        );
        let case_id = string_lit(&tuple.elems[0], "case id");
        assert!(
            seen.insert(case_id.clone()),
            "duplicate overflow metadata for {case_id}"
        );
        let expected_error_patterns = error_patterns.remove(&case_id).unwrap_or_default();
        entries.push(CaseMetadata {
            case_id,
            upstream_case_id: string_lit(&tuple.elems[1], "upstream case id"),
            expected_verdict: string_lit(&tuple.elems[2], "expected verdict"),
            min_obligations: usize_lit(&tuple.elems[3], "min obligations"),
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
            entry["upstream_path"].as_str() == Some("source/rust_verify_test/tests/overflow.rs")
        })
        .expect("Verus manifest should contain overflow.rs row");

    row["expected_cases"]
        .as_array()
        .expect("overflow.rs row should contain expected_cases")
        .iter()
        .map(|case| CaseMetadata {
            case_id: case["case_id"]
                .as_str()
                .expect("case should contain case_id")
                .to_owned(),
            upstream_case_id: case["upstream_case_id"]
                .as_str()
                .expect("case should contain upstream_case_id")
                .to_owned(),
            expected_verdict: case["expected_verdict"]
                .as_str()
                .expect("case should contain expected_verdict")
                .to_owned(),
            min_obligations: case["min_obligations"]
                .as_u64()
                .expect("case should contain min_obligations")
                .try_into()
                .expect("min_obligations should fit usize"),
            expected_error_patterns: case["expected_error_patterns"]
                .as_array()
                .map(|patterns| {
                    patterns
                        .iter()
                        .map(|pattern| {
                            pattern
                                .as_str()
                                .expect("expected_error_patterns values should be strings")
                                .to_owned()
                        })
                        .collect()
                })
                .unwrap_or_default(),
        })
        .collect()
}

fn string_lit(expr: &syn::Expr, label: &str) -> String {
    match expr {
        syn::Expr::Lit(syn::ExprLit {
            lit: syn::Lit::Str(lit),
            ..
        }) => lit.value(),
        _ => panic!("overflow metadata {label} should be a string literal"),
    }
}

fn usize_lit(expr: &syn::Expr, label: &str) -> usize {
    match expr {
        syn::Expr::Lit(syn::ExprLit {
            lit: syn::Lit::Int(lit),
            ..
        }) => lit
            .base10_parse::<usize>()
            .unwrap_or_else(|err| panic!("overflow metadata {label} should parse: {err}")),
        _ => panic!("overflow metadata {label} should be an integer literal"),
    }
}

fn find_port_function<'a>(file: &'a syn::File, case: &str) -> &'a syn::ItemFn {
    file.items
        .iter()
        .find_map(|item| match item {
            syn::Item::Fn(function) if function.sig.ident == case => Some(function),
            _ => None,
        })
        .unwrap_or_else(|| panic!("{case} should exist in overflow port"))
}

fn verify_port_case(case: &str, upstream_case: &str) -> (VerifyResult, usize) {
    let path = overflow_port_path();
    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|err| panic!("overflow port should read: {err}"));
    let file =
        syn::parse_file(&source).unwrap_or_else(|err| panic!("overflow port should parse: {err}"));
    let function = find_port_function(&file, case);

    let vc = extract_verification_conditions_with_file_context(&file, function)
        .unwrap_or_else(|err| panic!("{case} ({upstream_case}) should extract: {err}"));
    let obligation_count = vc.obligations().len();
    (vc.verify(), obligation_count)
}

fn collect_port_function_names(file: &syn::File) -> Vec<String> {
    let mut names = file
        .items
        .iter()
        .filter_map(|item| match item {
            syn::Item::Fn(function) => Some(function.sig.ident.to_string()),
            _ => None,
        })
        .filter(|name| name != "overflow_rs_expected_cases")
        .filter(|name| name != "overflow_rs_fail_closed_error_patterns")
        .collect::<Vec<_>>();
    names.sort();
    names
}

fn expect_fail_closed_error_contains_any(
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

const VERIFIED_CASES: &[(&str, &str, usize)] = &[
    (
        "overflow_u64_add_by_two_guard_verified",
        "test_overflow_fails_1",
        2,
    ),
    (
        "overflow_u64_two_adds_guard_verified",
        "test_overflow_spec_fails_2",
        2,
    ),
    (
        "overflow_ensures_pass_usize_guard_verified",
        "test_overflow_ensures_pass",
        2,
    ),
    (
        "divide_by_nonzero_u8_guard_verified",
        "test_divide_by_zero",
        2,
    ),
    (
        "remainder_by_nonzero_u8_guard_verified",
        "test_divide_by_zero",
        1,
    ),
    ("const_u8_add_in_range_verified", "test_const_ok", 1),
    ("underflow_u64_sub_guard_verified", "underflow", 2),
    ("bit_shift_in_range_u16_verified", "bit_shift_overflow", 1),
    (
        "bit_shift_right_nonzero_left_arg_u16_verified",
        "bit_shift_overflow",
        1,
    ),
    (
        "bit_shift_left_in_range_u16_verified",
        "bit_shift_overflow",
        1,
    ),
    (
        "bit_shift_left_usize_bits_minus_one_verified",
        "bit_shift_overflow",
        1,
    ),
    (
        "nonlinear_unsigned_div_rem_guard_verified",
        "nonlinear_ops_dont_overflow_unsigned",
        2,
    ),
    (
        "arith_bounds_add_guard_verified",
        "arith_bounds_asserted_and_assumed",
        2,
    ),
    (
        "primitive_add_trait_method_verified",
        "test_overflow_spec_pass",
        2,
    ),
];

const COUNTEREXAMPLE_CASES: &[(&str, &str, usize)] = &[
    (
        "overflow_fails_u64_add_by_two_counterexample",
        "test_overflow_fails_1",
        1,
    ),
    (
        "overflow_two_u64_adds_second_counterexample",
        "test_overflow_fails_2",
        1,
    ),
    (
        "overflow_fails_usize_unbounded_counterexample",
        "test_overflow_fails_usize",
        1,
    ),
    (
        "divide_by_zero_guard_missing_counterexample",
        "test_divide_by_zero",
        1,
    ),
    (
        "remainder_by_zero_guard_missing_counterexample",
        "test_divide_by_zero",
        1,
    ),
    ("underflow_u64_sub_counterexample", "underflow", 1),
    (
        "bit_shift_width_boundary_counterexample",
        "bit_shift_overflow",
        1,
    ),
    (
        "bit_shift_width_above_boundary_counterexample",
        "bit_shift_overflow",
        1,
    ),
    (
        "bit_shift_left_width_boundary_counterexample",
        "bit_shift_overflow",
        1,
    ),
    (
        "bit_shift_usize_bits_boundary_counterexample",
        "bit_shift_overflow",
        1,
    ),
    (
        "arith_bounds_add_missing_guard_counterexample",
        "arith_bounds_asserted_and_assumed",
        1,
    ),
    (
        "bit_shift_width_mismatch_u32_counterexample",
        "bit_shift_width_mismatch",
        1,
    ),
    (
        "bit_shift_width_mismatch_signed_counterexample",
        "bit_shift_width_mismatch_signed",
        1,
    ),
    (
        "const_item_initializer_overflow_counterexample",
        "test_const_fail",
        1,
    ),
    (
        "static_item_initializer_overflow_counterexample",
        "test_static_fail",
        1,
    ),
];

const FAIL_CLOSED_CASES: &[(&str, &str, &[&str])] = &[
    (
        "bit_shift_underflow_signed_fail_closed",
        "bit_shift_underflow",
        &["possible bit shift underflow/overflow"],
    ),
    (
        "bit_shift_unsigned_lhs_signed_shift_fail_closed",
        "bit_shift_unsigned_shift_signed",
        &["possible bit shift underflow/overflow"],
    ),
];

#[test]
fn overflow_rs_port_file_is_rust_syntax() {
    let source =
        std::fs::read_to_string(overflow_port_path()).expect("overflow port should be readable");
    syn::parse_file(&source).expect("overflow port should parse as ordinary Rust syntax");
}

#[test]
fn overflow_rs_pinned_upstream_case_shapes_are_present() {
    let path = pinned_upstream_overflow_path();
    if !path.exists() {
        eprintln!(
            "skipping pinned upstream overflow.rs shape check; missing {}",
            path.display()
        );
        return;
    }

    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", path.display()));
    for expected in [
        "#[test] test_overflow_spec_pass",
        "#[test] test_overflow_spec_fails_1",
        "#[test] test_overflow_fails_1",
        "#[test] test_overflow_spec_fails_2",
        "#[test] test_overflow_fails_2",
        "#[test] test_divide_by_zero",
        "#[test] test_const_ok",
        "#[test] test_const_fail",
        "#[test] test_static_fail",
        "#[test] test_literal_out_of_range",
        "#[test] test_overflow_fails_usize",
        "#[test] test_overflow_ensures_pass",
        "#[test] underflow",
        "#[test] bit_shift_overflow",
        "#[test] bit_shift_width_mismatch",
        "#[test] bit_shift_width_mismatch_signed",
        "#[test] bit_shift_unsigned_shift_signed",
        "#[test] bit_shift_underflow",
        "#[test] bit_shift_overflow_arch32",
        "#[test] bit_shift_overflow_arch64",
        "#[test] spec_bitshift_defined_for_larger_ints",
        "#[test] spec_bitshift_negative",
        "#[test] nonlinear_ops_dont_overflow_unsigned",
        "#[test] arith_bounds_asserted_and_assumed",
    ] {
        assert!(
            source.contains(expected),
            "pinned upstream overflow.rs should still contain {expected}"
        );
    }
}

#[test]
fn overflow_rs_expected_case_metadata_is_exact() {
    let source =
        std::fs::read_to_string(overflow_port_path()).expect("overflow port should be readable");
    let file =
        syn::parse_file(&source).expect("overflow port should parse as ordinary Rust syntax");
    assert!(
        source.contains("overflow_rs_expected_cases")
            && source.contains("overflow_rs_fail_closed_error_patterns"),
        "overflow port should export expected-case and fail-closed error-pattern metadata"
    );
    assert_eq!(
        overflow_metadata_cases_from_source(&file),
        expected_metadata()
    );
}

#[test]
fn overflow_rs_expected_case_metadata_matches_manifest() {
    let source =
        std::fs::read_to_string(overflow_port_path()).expect("overflow port should be readable");
    let file =
        syn::parse_file(&source).expect("overflow port should parse as ordinary Rust syntax");
    assert_eq!(
        overflow_metadata_cases_from_source(&file),
        manifest_expected_metadata(),
        "overflow manifest expected_cases should match port metadata exactly"
    );
}

#[test]
fn overflow_rs_expected_case_metadata_names_all_port_functions() {
    let source =
        std::fs::read_to_string(overflow_port_path()).expect("overflow port should be readable");
    let file =
        syn::parse_file(&source).expect("overflow port should parse as ordinary Rust syntax");
    let mut function_names = collect_port_function_names(&file);
    let mut metadata_names = overflow_metadata_cases_from_source(&file)
        .iter()
        .map(|metadata| metadata.case_id.clone())
        .collect::<Vec<_>>();
    metadata_names.sort();

    assert_eq!(
        function_names, metadata_names,
        "overflow port expected-case metadata should cover every scout function"
    );
    function_names.dedup();
    assert_eq!(
        function_names.len(),
        metadata_names.len(),
        "overflow port expected-case metadata should not contain duplicate case IDs"
    );
}

#[test]
fn overflow_rs_verified_subset_verifies_from_file() {
    for (case, upstream_case, min_obligations) in VERIFIED_CASES {
        let (result, obligations) = verify_port_case(case, upstream_case);
        assert!(
            obligations >= *min_obligations,
            "{case} ({upstream_case}) should collect at least {min_obligations} obligation(s), got {obligations}"
        );
        match result {
            VerifyResult::Verified => {}
            VerifyResult::Unknown { reason, .. } => {
                panic!("{case} ({upstream_case}) returned solver Unknown, which is not stable evidence: {reason}")
            }
            other => panic!("{case} ({upstream_case}) should verify, got: {other:?}"),
        }
    }
}

#[test]
fn overflow_rs_counterexample_subset_is_rejected_from_file() {
    for (case, upstream_case, min_obligations) in COUNTEREXAMPLE_CASES {
        let (result, obligations) = verify_port_case(case, upstream_case);
        assert!(
            obligations >= *min_obligations,
            "{case} ({upstream_case}) should collect at least {min_obligations} obligation(s), got {obligations}"
        );
        match result {
            VerifyResult::Counterexample { .. } => {}
            VerifyResult::Unknown { reason, .. } => {
                panic!("{case} ({upstream_case}) returned solver Unknown, which is not stable evidence: {reason}")
            }
            other => panic!("{case} ({upstream_case}) should be rejected, got: {other:?}"),
        }
    }
}

#[test]
fn overflow_rs_verify_function_from_file_entrypoint_still_covers_representative_cases() {
    let path = overflow_port_path();
    let path = path.to_str().expect("overflow port path should be UTF-8");

    for (case, upstream_case, expected_verified) in [
        (
            "overflow_ensures_pass_usize_guard_verified",
            "test_overflow_ensures_pass",
            true,
        ),
        (
            "underflow_u64_sub_guard_verified",
            "underflow bounded subtraction surrogate",
            true,
        ),
        (
            "overflow_fails_usize_unbounded_counterexample",
            "test_overflow_fails_usize",
            false,
        ),
        (
            "bit_shift_width_boundary_counterexample",
            "bit_shift_overflow right shift overflow",
            false,
        ),
    ] {
        let result = verify_case(path, case, upstream_case);
        match (expected_verified, result) {
            (true, VerifyResult::Verified) | (false, VerifyResult::Counterexample { .. }) => {}
            (_, VerifyResult::Unknown { reason, .. }) => {
                panic!("{case} ({upstream_case}) returned solver Unknown, which is not stable evidence: {reason}")
            }
            (true, other) => panic!("{case} ({upstream_case}) should verify, got: {other:?}"),
            (false, other) => {
                panic!("{case} ({upstream_case}) should be rejected, got: {other:?}")
            }
        }
    }
}

#[test]
fn overflow_rs_unsupported_boundaries_fail_closed_from_file() {
    let path = overflow_port_path();
    let path = path.to_str().expect("overflow port path should be UTF-8");

    for (case, upstream_case, expected_fragments) in FAIL_CLOSED_CASES {
        expect_fail_closed_error_contains_any(path, case, upstream_case, expected_fragments);
    }
}
