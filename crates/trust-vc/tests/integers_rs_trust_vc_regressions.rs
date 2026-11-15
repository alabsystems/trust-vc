// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Executable guards for the currently ported upstream integers.rs subset.
//!
//! The manifest keeps `source/rust_verify_test/tests/integers.rs` classified as
//! an unsupported gap. These tests pin the Rust-valid TrustVc slices that now
//! execute through the verifier and keep still-unsupported semantics fail-closed.

mod common;

use std::{
    collections::BTreeSet,
    path::{Path, PathBuf},
};
use trust_vc_core::{
    extract_verification_conditions_with_file_context, verify_function_from_file, VerifyResult,
};

fn integers_port_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/ported/integers.rs")
}

fn verus_manifest_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/verus-tests.json")
}

fn pinned_upstream_integers_path() -> PathBuf {
    common::pinned_verus_test_path("integers.rs")
}

/// `test_enum_to_int_overflow_wrap` is not here: it states the tautology
/// `result == v as u8` about `v as u8`, upstream verifies it, and
/// `verified_liar_twins.rs` pins its `Verified` answer with refuted twins.
const FAIL_CLOSED_CASES: &[(&str, &str)] = &[(
    "test_finite_signed_to_nat_cast_fails_without_nonnegative",
    "finite_signed_to_nat_requires_nonnegative",
)];

const EXPECTED_CASES: &[(&str, &str, &str, usize)] = &[
    ("test1_int_nat_arithmetic", "test1", "verified", 17),
    (
        "test1_fails_wrapping_add_counterexample",
        "test1_fails",
        "counterexample",
        2,
    ),
    (
        "test1_symbolic_division_remainder_verified",
        "test1",
        "verified",
        4,
    ),
    (
        "test2_fails_u8_wrapped_256_counterexample",
        "test2_fails",
        "counterexample",
        2,
    ),
    (
        "test3_fails_signed_division_counterexample",
        "test3_fails",
        "counterexample",
        2,
    ),
    (
        "test_chained_nat_bounds_verified",
        "test_chained",
        "verified",
        4,
    ),
    (
        "test_chained_nat_bounds_counterexample",
        "test_chained",
        "counterexample",
        2,
    ),
    (
        "test_chained_equalities_verified",
        "test_chained1",
        "verified",
        7,
    ),
    (
        "test_chained_equalities_counterexample",
        "test_chained1",
        "counterexample",
        2,
    ),
    ("test4_explicit_cast_typing_surface", "test4", "verified", 8),
    ("test_literals_boundaries", "test_literals", "verified", 7),
    (
        "test_literals_fails_wrong_zero_boundary_counterexample",
        "test_literals_fails1",
        "counterexample",
        2,
    ),
    (
        "test_literals_fails_wrong_u8_boundary_counterexample",
        "test_literals_fails2",
        "counterexample",
        2,
    ),
    (
        "test_literals_fails_wrong_i8_low_boundary_counterexample",
        "test_literals_fails3",
        "counterexample",
        2,
    ),
    (
        "test_literals_fails_wrong_i8_high_boundary_counterexample",
        "test_literals_fails4",
        "counterexample",
        2,
    ),
    (
        "test_spec_const_like_large_arithmetic",
        "test_spec_const",
        "verified",
        4,
    ),
    ("test_bool_to_int", "test_bool_to_int", "verified", 5),
    (
        "test_enum_to_int_discriminant_constants",
        "test_enum_to_int",
        "verified",
        4,
    ),
    (
        "test_enum_to_int_discriminant_liar_counterexample",
        "test_enum_to_int",
        "counterexample",
        2,
    ),
    (
        "test_enum_to_int_symbolic_return",
        "test_enum_to_int",
        "verified",
        3,
    ),
    (
        "test_enum_to_int_symbolic_return_liar_counterexample",
        "test_enum_to_int",
        "counterexample",
        2,
    ),
    ("test_finite_unsigned_to_nat_casts", "test1", "verified", 6),
    (
        "test_nat_to_finite_cast_wrap_constant",
        "test4",
        "verified",
        3,
    ),
    (
        "test_finite_signed_to_nat_cast_nonnegative",
        "finite_signed_to_nat_nonnegative",
        "verified",
        3,
    ),
];

#[derive(Debug, Eq, PartialEq)]
struct CaseMetadata {
    case_id: String,
    upstream_case_id: String,
    expected_verdict: String,
    min_obligations: usize,
}

fn referenced_array_const(file: &syn::File, const_name: &str) -> syn::ExprArray {
    let const_item = file
        .items
        .iter()
        .find_map(|item| match item {
            syn::Item::Const(item) if item.ident == const_name => Some(item),
            _ => None,
        })
        .unwrap_or_else(|| panic!("integers port should define {const_name}"));

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

fn metadata_entries(file: &syn::File) -> Vec<CaseMetadata> {
    let array = referenced_array_const(file, "INTEGERS_RS_EXPECTED_CASES");
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
            "duplicate integers metadata for {case_id}"
        );
        entries.push(CaseMetadata {
            case_id,
            upstream_case_id: literal_string(&tuple.elems[1]),
            expected_verdict: literal_string(&tuple.elems[2]),
            min_obligations: literal_usize(&tuple.elems[3]),
        });
    }

    entries
}

fn expected_metadata() -> Vec<CaseMetadata> {
    EXPECTED_CASES
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
            entry["upstream_path"].as_str() == Some("source/rust_verify_test/tests/integers.rs")
        })
        .expect("Verus manifest should contain integers.rs row");

    row["expected_cases"]
        .as_array()
        .expect("integers.rs row should contain expected_cases")
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
        })
        .collect()
}

fn verify_port_case(case: &str, upstream_case: &str) -> (VerifyResult, usize) {
    let path = integers_port_path();
    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|err| panic!("integers port should read: {err}"));
    let file =
        syn::parse_file(&source).unwrap_or_else(|err| panic!("integers port should parse: {err}"));
    let func = file
        .items
        .iter()
        .find_map(|item| match item {
            syn::Item::Fn(func) if func.sig.ident == case => Some(func),
            _ => None,
        })
        .unwrap_or_else(|| panic!("{case} ({upstream_case}) should exist in integers port"));

    let vc = extract_verification_conditions_with_file_context(&file, func)
        .unwrap_or_else(|err| panic!("{case} ({upstream_case}) should extract: {err}"));
    let obligation_count = vc.obligations().len();
    (vc.verify(), obligation_count)
}

#[test]
fn integers_rs_port_file_is_rust_syntax() {
    let source =
        std::fs::read_to_string(integers_port_path()).expect("integers port should be readable");
    syn::parse_file(&source).expect("integers port should parse as ordinary Rust syntax");
}

#[test]
fn integers_rs_pinned_upstream_case_shapes_are_present() {
    let path = pinned_upstream_integers_path();
    if !path.exists() {
        eprintln!(
            "skipping pinned upstream integers.rs shape check; missing {}",
            path.display()
        );
        return;
    }

    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", path.display()));
    for expected in [
        "#[test] test1",
        "#[test] test1_fails",
        "#[test] test2_fails",
        "#[test] test3_fails",
        "#[test] test_chained",
        "#[test] test_chained1",
        "#[test] test4",
        "#[test] test_literals",
        "#[test] test_literals_fails1",
        "#[test] test_literals_fails2",
        "#[test] test_literals_fails3",
        "#[test] test_literals_fails4",
        "#[test] test_spec_const",
        "#[test] test_bool_to_int",
        "#[test] test_enum_to_int",
        "#[test] test_enum_to_int_overflow",
    ] {
        assert!(
            source.contains(expected),
            "pinned upstream integers.rs should still contain {expected}"
        );
    }
}

#[test]
fn integers_rs_expected_case_metadata_is_exact() {
    let source =
        std::fs::read_to_string(integers_port_path()).expect("integers port should be readable");
    let file =
        syn::parse_file(&source).expect("integers port should parse as ordinary Rust syntax");
    assert_eq!(metadata_entries(&file), expected_metadata());
    assert!(
        source.contains("integers_rs_expected_cases"),
        "integers port should export expected-case metadata"
    );
    assert_eq!(
        EXPECTED_CASES,
        &[
            ("test1_int_nat_arithmetic", "test1", "verified", 17),
            (
                "test1_fails_wrapping_add_counterexample",
                "test1_fails",
                "counterexample",
                2,
            ),
            (
                "test1_symbolic_division_remainder_verified",
                "test1",
                "verified",
                4,
            ),
            (
                "test2_fails_u8_wrapped_256_counterexample",
                "test2_fails",
                "counterexample",
                2,
            ),
            (
                "test3_fails_signed_division_counterexample",
                "test3_fails",
                "counterexample",
                2,
            ),
            (
                "test_chained_nat_bounds_verified",
                "test_chained",
                "verified",
                4,
            ),
            (
                "test_chained_nat_bounds_counterexample",
                "test_chained",
                "counterexample",
                2,
            ),
            (
                "test_chained_equalities_verified",
                "test_chained1",
                "verified",
                7,
            ),
            (
                "test_chained_equalities_counterexample",
                "test_chained1",
                "counterexample",
                2,
            ),
            ("test4_explicit_cast_typing_surface", "test4", "verified", 8),
            ("test_literals_boundaries", "test_literals", "verified", 7),
            (
                "test_literals_fails_wrong_zero_boundary_counterexample",
                "test_literals_fails1",
                "counterexample",
                2,
            ),
            (
                "test_literals_fails_wrong_u8_boundary_counterexample",
                "test_literals_fails2",
                "counterexample",
                2,
            ),
            (
                "test_literals_fails_wrong_i8_low_boundary_counterexample",
                "test_literals_fails3",
                "counterexample",
                2,
            ),
            (
                "test_literals_fails_wrong_i8_high_boundary_counterexample",
                "test_literals_fails4",
                "counterexample",
                2,
            ),
            (
                "test_spec_const_like_large_arithmetic",
                "test_spec_const",
                "verified",
                4,
            ),
            ("test_bool_to_int", "test_bool_to_int", "verified", 5),
            (
                "test_enum_to_int_discriminant_constants",
                "test_enum_to_int",
                "verified",
                4,
            ),
            (
                "test_enum_to_int_discriminant_liar_counterexample",
                "test_enum_to_int",
                "counterexample",
                2,
            ),
            (
                "test_enum_to_int_symbolic_return",
                "test_enum_to_int",
                "verified",
                3,
            ),
            (
                "test_enum_to_int_symbolic_return_liar_counterexample",
                "test_enum_to_int",
                "counterexample",
                2,
            ),
            ("test_finite_unsigned_to_nat_casts", "test1", "verified", 6,),
            (
                "test_nat_to_finite_cast_wrap_constant",
                "test4",
                "verified",
                3,
            ),
            (
                "test_finite_signed_to_nat_cast_nonnegative",
                "finite_signed_to_nat_nonnegative",
                "verified",
                3,
            ),
        ]
    );
}

#[test]
fn integers_rs_expected_case_metadata_matches_manifest() {
    let source =
        std::fs::read_to_string(integers_port_path()).expect("integers port should be readable");
    let file =
        syn::parse_file(&source).expect("integers port should parse as ordinary Rust syntax");
    assert_eq!(metadata_entries(&file), manifest_expected_metadata());
}

#[test]
fn integers_rs_verified_subset_verifies_from_file() {
    for (case, upstream_case, expected_status, min_obligations) in EXPECTED_CASES
        .iter()
        .filter(|(_, _, expected_status, _)| *expected_status == "verified")
    {
        let (result, obligations) = verify_port_case(case, upstream_case);
        assert!(
            obligations >= *min_obligations,
            "{case} ({upstream_case}) should collect at least {min_obligations} obligation(s), got {obligations}"
        );
        assert!(
            matches!(result, VerifyResult::Verified),
            "{case} ({upstream_case}, {expected_status}) should verify, got: {result:?}"
        );
    }
}

#[test]
fn integers_rs_counterexample_subset_is_rejected_from_file() {
    for (case, upstream_case, expected_status, min_obligations) in EXPECTED_CASES
        .iter()
        .filter(|(_, _, expected_status, _)| *expected_status == "counterexample")
    {
        let (result, obligations) = verify_port_case(case, upstream_case);
        assert!(
            obligations >= *min_obligations,
            "{case} ({upstream_case}) should collect at least {min_obligations} obligation(s), got {obligations}"
        );
        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "{case} ({upstream_case}, {expected_status}) should be rejected, got: {result:?}"
        );
    }
}

#[test]
fn integers_rs_verify_function_from_file_entrypoint_still_covers_representative_cases() {
    let path = integers_port_path();
    let path = path.to_str().expect("integers port path should be UTF-8");

    for (case, upstream_case) in [
        ("test1_int_nat_arithmetic", "test1"),
        ("test_chained_equalities_verified", "test_chained1"),
        ("test1_fails_wrapping_add_counterexample", "test1_fails"),
        ("test_chained_equalities_counterexample", "test_chained1"),
    ] {
        let result = verify_function_from_file(path, case)
            .unwrap_or_else(|err| panic!("{case} ({upstream_case}) should extract: {err}"));
        assert!(
            matches!(
                (&result, case),
                (
                    VerifyResult::Verified,
                    "test1_int_nat_arithmetic" | "test_chained_equalities_verified"
                ) | (
                    VerifyResult::Counterexample { .. },
                    "test1_fails_wrapping_add_counterexample"
                        | "test_chained_equalities_counterexample"
                )
            ),
            "{case} ({upstream_case}) had unexpected verify_function_from_file result: {result:?}"
        );
    }
}

#[test]
fn integers_rs_fail_closed_subset_does_not_verify_from_file() {
    let path = integers_port_path();
    let path = path.to_str().expect("integers port path should be UTF-8");

    for (case, upstream_case) in FAIL_CLOSED_CASES {
        let result = verify_function_from_file(path, case)
            .unwrap_or_else(|err| panic!("{case} ({upstream_case}) should extract: {err}"));
        assert!(
            !matches!(result, VerifyResult::Verified),
            "{case} ({upstream_case}) should fail closed, got: {result:?}"
        );
    }
}
