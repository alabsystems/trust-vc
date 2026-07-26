// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Executable guards for the first upstream integer_ring.rs TrustVc scout slice.
//!
//! These tests intentionally keep
//! `source/rust_verify_test/tests/integer_ring.rs` as an unsupported gap. They
//! pin only Rust-valid TrustVc evidence for a focused arithmetic subset while
//! `by(integer_ring)`, Singular-backed modular algebra, warnings, diagnostics,
//! and full upstream parity remain unsupported.

mod common;

use std::{
    collections::{BTreeMap, BTreeSet},
    path::{Path, PathBuf},
};
use trust_vc_core::{
    extract_verification_conditions_with_file_context, verify_function_from_file, VerifyResult,
};

#[derive(Debug, Eq, PartialEq)]
struct CaseMetadata {
    case_id: String,
    upstream_case_id: String,
    expected_verdict: String,
    min_obligations: usize,
    expected_error_patterns: Vec<String>,
}

fn integer_ring_port_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/ported/integer_ring.rs")
}

fn pinned_upstream_integer_ring_path() -> PathBuf {
    common::pinned_verus_test_path("integer_ring.rs")
}

fn verus_manifest_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/verus-tests.json")
}

fn verify_port_case(case: &str, upstream_case: &str) -> (VerifyResult, usize) {
    let path = integer_ring_port_path();
    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|err| panic!("integer_ring port should read: {err}"));
    let file = syn::parse_file(&source)
        .unwrap_or_else(|err| panic!("integer_ring port should parse: {err}"));
    let func = file
        .items
        .iter()
        .find_map(|item| match item {
            syn::Item::Fn(func) if func.sig.ident == case => Some(func),
            _ => None,
        })
        .unwrap_or_else(|| panic!("{case} ({upstream_case}) should exist in integer_ring port"));

    let vc = extract_verification_conditions_with_file_context(&file, func)
        .unwrap_or_else(|err| panic!("{case} ({upstream_case}) should extract: {err}"));
    let obligations = vc.obligations().len();
    (vc.verify(), obligations)
}

fn referenced_array_const(file: &syn::File, const_name: &str) -> syn::ExprArray {
    let const_item = file
        .items
        .iter()
        .find_map(|item| match item {
            syn::Item::Const(item) if item.ident == const_name => Some(item),
            _ => None,
        })
        .unwrap_or_else(|| panic!("integer_ring port should define {const_name}"));

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
    let array = referenced_array_const(file, "INTEGER_RING_RS_EXPECTED_ERROR_PATTERNS");
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
    let array = referenced_array_const(file, "INTEGER_RING_RS_EXPECTED_CASES");
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
            "duplicate integer_ring metadata for {case_id}"
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
            entry["upstream_path"].as_str() == Some("source/rust_verify_test/tests/integer_ring.rs")
        })
        .expect("Verus manifest should contain integer_ring.rs row");

    row["expected_cases"]
        .as_array()
        .expect("integer_ring manifest row should contain expected_cases")
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
            expected_error_patterns: case["expected_error_patterns"]
                .as_array()
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

const UPSTREAM_CASES: &[&str] = &[
    "simple_1",
    "simple_2",
    "mont_mul_1",
    "mont_mul_2",
    "wide_mul",
    "uninterpreted_function",
    "simple_fail_1",
    "simple_fail_2",
    "wide_mul_fail",
    "type_fail",
    "reserved_keyword",
    "div_by_zero_fail",
    "mul_mod_noop",
    "mul_mod_noop_fail_1",
    "mul_mod_noop_fail_2",
    "gt_not_supported",
    "lt_not_supported",
    "warnings",
];

const VERIFIED_CASES: &[(&str, &str, usize)] = &[
    (
        "simple_1_modular_multiplication_concrete_verified",
        "simple_1",
        2,
    ),
    ("simple_2_bounded_factorization_verified", "simple_2", 1),
    ("simple_2_trinomial_square_concrete_verified", "simple_2", 1),
    (
        "simple_2_bounded_double_offset_factorization_verified",
        "simple_2",
        1,
    ),
    ("mont_mul_1_concrete_verified", "mont_mul_1", 4),
    ("mont_mul_2_concrete_verified", "mont_mul_2", 5),
    ("mul_mod_noop_concrete_verified", "mul_mod_noop", 3),
    (
        "uninterpreted_function_concrete_verified",
        "uninterpreted_function",
        2,
    ),
    (
        "type_fail_mixed_u32_modular_concrete_verified",
        "type_fail",
        2,
    ),
    (
        "reserved_keyword_name_polynomial_shape_verified",
        "reserved_keyword",
        1,
    ),
    ("wide_mul_limb_expansion_concrete_verified", "wide_mul", 1),
    ("warnings_modular_concrete_verified", "warnings", 6),
];

const COUNTEREXAMPLE_CASES: &[(&str, &str, usize)] = &[
    (
        "simple_2_bounded_factorization_wrong_increment_counterexample",
        "simple_fail_2",
        1,
    ),
    (
        "simple_2_bounded_double_offset_wrong_factor_counterexample",
        "simple_fail_2",
        1,
    ),
    (
        "simple_fail_2_trinomial_missing_square_concrete_counterexample",
        "simple_fail_2",
        1,
    ),
    (
        "simple_fail_1_modular_addition_concrete_counterexample",
        "simple_fail_1",
        2,
    ),
    (
        "mul_mod_noop_fail_1_concrete_counterexample",
        "mul_mod_noop_fail_1",
        2,
    ),
    (
        "mul_mod_noop_fail_2_concrete_counterexample",
        "mul_mod_noop_fail_2",
        2,
    ),
    (
        "wide_mul_wrong_limb_concrete_counterexample",
        "wide_mul_fail",
        1,
    ),
    (
        "gt_not_supported_concrete_counterexample",
        "gt_not_supported",
        2,
    ),
    (
        "lt_not_supported_concrete_counterexample",
        "lt_not_supported",
        2,
    ),
];

const FAIL_CLOSED_CASES: &[(&str, &str, &[&str])] = &[
    (
        "simple_1_modular_multiplication_singular_boundary",
        "simple_1",
        &[
            "unknown return type for function 'simple_1_modular_congruence'",
            "simple_1_modular_congruence",
        ],
    ),
    (
        "mont_mul_1_singular_boundary",
        "mont_mul_1",
        &[
            "unknown return type for function 'mont_mul_1_modular_congruence'",
            "mont_mul_1_modular_congruence",
        ],
    ),
    (
        "mont_mul_2_singular_boundary",
        "mont_mul_2",
        &[
            "unknown return type for function 'mont_mul_2_modular_zero'",
            "mont_mul_2_modular_zero",
        ],
    ),
    (
        "mul_mod_noop_singular_boundary",
        "mul_mod_noop",
        &[
            "unknown return type for function 'mul_mod_noop_identity'",
            "mul_mod_noop_identity",
        ],
    ),
    (
        "uninterpreted_function_singular_boundary",
        "uninterpreted_function",
        &[
            "unknown return type for function 'uninterpreted_function_modular_relation'",
            "uninterpreted_function_modular_relation",
        ],
    ),
    (
        "type_fail_mixed_u32_singular_boundary",
        "type_fail",
        &[
            "unknown return type for function 'type_fail_mixed_u32_modular_relation'",
            "type_fail_mixed_u32_modular_relation",
        ],
    ),
    (
        "warnings_singular_boundary",
        "warnings",
        &[
            "unknown return type for function 'warnings_modular_relation'",
            "warnings_modular_relation",
        ],
    ),
    (
        "gt_not_supported_singular_boundary",
        "gt_not_supported",
        &[
            "unknown return type for function 'integer_ring_gt_relation'",
            "integer_ring_gt_relation",
        ],
    ),
    (
        "lt_not_supported_singular_boundary",
        "lt_not_supported",
        &[
            "unknown return type for function 'integer_ring_lt_relation'",
            "integer_ring_lt_relation",
        ],
    ),
    (
        "div_by_zero_singular_boundary",
        "div_by_zero_fail",
        &[
            "unknown return type for function 'may_div_zero_relation'",
            "may_div_zero_relation",
        ],
    ),
];

#[test]
fn integer_ring_rs_port_file_is_rust_syntax() {
    let source =
        std::fs::read_to_string(integer_ring_port_path()).expect("integer_ring port should read");
    syn::parse_file(&source).expect("integer_ring port should parse as ordinary Rust syntax");
}

#[test]
fn integer_ring_rs_expected_case_metadata_matches_manifest() {
    let source =
        std::fs::read_to_string(integer_ring_port_path()).expect("integer_ring port should read");
    let file = syn::parse_file(&source).expect("integer_ring port should parse");
    assert!(
        source.contains("pub const INTEGER_RING_RS_EXPECTED_CASES")
            && source.contains("pub fn integer_ring_rs_expected_cases")
            && source.contains("pub const INTEGER_RING_RS_EXPECTED_ERROR_PATTERNS")
            && source.contains("pub fn integer_ring_rs_expected_error_patterns"),
        "integer_ring port should expose manifest-ready expected-case and error-pattern metadata helpers"
    );
    assert_eq!(
        metadata_entries(&file),
        manifest_expected_metadata(),
        "integer_ring manifest expected_cases should match port metadata and error patterns exactly"
    );
}

#[test]
fn integer_ring_rs_verified_subset_verifies_from_file() {
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
fn integer_ring_rs_counterexample_subset_is_rejected_from_file() {
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
fn integer_ring_rs_singular_boundary_fails_closed_from_file() {
    let path = integer_ring_port_path();
    let path = path
        .to_str()
        .expect("integer_ring port path should be UTF-8");

    for (case, upstream_case, expected_fragments) in FAIL_CLOSED_CASES {
        let message = match verify_function_from_file(path, case) {
            Err(err) => err.to_string(),
            Ok(VerifyResult::Error { message }) => message,
            Ok(VerifyResult::Unknown { reason, .. }) => {
                panic!("{case} ({upstream_case}) returned solver Unknown, which is not stable fail-closed evidence: {reason}")
            }
            Ok(other) => {
                panic!("{case} ({upstream_case}) should fail closed with Error, got: {other:?}")
            }
        };
        assert!(
            expected_fragments
                .iter()
                .any(|fragment| message.contains(fragment)),
            "{case} ({upstream_case}) error should contain one of {expected_fragments:?}, got: {message}"
        );
    }
}

#[test]
fn integer_ring_rs_pinned_upstream_shape_stays_expected() {
    let path = pinned_upstream_integer_ring_path();
    if !path.exists() {
        eprintln!(
            "skipping pinned upstream integer_ring.rs shape check; missing {}",
            path.display()
        );
        return;
    }

    let source =
        std::fs::read_to_string(&path).expect("pinned upstream integer_ring.rs should read");

    let mut previous = 0;
    for case in UPSTREAM_CASES {
        let marker = format!("\n    {case} verus_code! {{");
        let current = source
            .find(&marker)
            .unwrap_or_else(|| panic!("upstream integer_ring.rs should contain case {case}"));
        assert!(
            current >= previous,
            "upstream integer_ring.rs case {case} should stay in pinned order"
        );
        previous = current;
    }

    assert_eq!(
        source
            .matches("#[cfg_attr(not(feature = \"singular\"), ignore)]")
            .count(),
        UPSTREAM_CASES.len(),
        "each upstream integer_ring.rs case should remain singular-gated"
    );
    assert_eq!(
        source.matches("=> Ok(())").count(),
        8,
        "upstream verified-case count should stay pinned"
    );
    assert_eq!(
        source
            .matches("=> Err(err) => assert_one_fails(err)")
            .count(),
        9,
        "upstream one-failure case count should stay pinned"
    );
    assert!(
        source.contains("=> Ok(err) =>"),
        "upstream warnings case should remain a warning-success shape"
    );
}

#[test]
fn integer_ring_rs_port_inventory_stays_intentional() {
    let source =
        std::fs::read_to_string(integer_ring_port_path()).expect("integer_ring port should read");
    let parsed = syn::parse_file(&source).expect("integer_ring port should parse");

    for (case, _, _) in VERIFIED_CASES.iter().chain(COUNTEREXAMPLE_CASES.iter()) {
        let found = parsed.items.iter().any(|item| match item {
            syn::Item::Fn(function) => function.sig.ident == *case,
            _ => false,
        });
        assert!(
            found,
            "{case} should remain an explicit top-level port witness"
        );
    }

    for (case, _, _) in FAIL_CLOSED_CASES {
        let found = parsed.items.iter().any(|item| match item {
            syn::Item::Fn(function) => function.sig.ident == *case,
            _ => false,
        });
        assert!(
            found,
            "{case} should remain an explicit top-level fail-closed boundary"
        );
    }
}
