// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Executable guards for the current upstream generics.rs TrustVc scout slice.
//!
//! These tests intentionally keep `source/rust_verify_test/tests/generics.rs`
//! fail-closed in the manifest. They prove only local Rust-valid witnesses for
//! generic function contracts, generic spec-function identity, generic struct
//! field substitution/projection, u8 range facts adjacent to const-generic
//! ranges, stable counterexamples, and explicit unsupported boundaries.
//! Solver `Unknown` outcomes are not accepted as replacement evidence.

mod common;

use std::{
    collections::{BTreeMap, BTreeSet},
    path::{Path, PathBuf},
};
use trust_vc_core::{
    extract_verification_conditions_with_file_context, verify_function_from_file, VerifyResult,
};

fn generics_port_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/ported/generics.rs")
}

fn verus_manifest_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/verus-tests.json")
}

fn pinned_upstream_generics_path() -> PathBuf {
    common::pinned_verus_test_path("generics.rs")
}

fn verify_port_case(case: &str, upstream_case: &str) -> (VerifyResult, usize) {
    let path = generics_port_path();
    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|err| panic!("generics port should read: {err}"));
    let file =
        syn::parse_file(&source).unwrap_or_else(|err| panic!("generics port should parse: {err}"));
    let function = file
        .items
        .iter()
        .find_map(|item| match item {
            syn::Item::Fn(function) if function.sig.ident == case => Some(function),
            _ => None,
        })
        .unwrap_or_else(|| panic!("{case} ({upstream_case}) should exist in generics port"));

    let vc = extract_verification_conditions_with_file_context(&file, function)
        .unwrap_or_else(|err| panic!("{case} ({upstream_case}) should extract: {err}"));
    let obligation_count = vc.obligations().len();
    (vc.verify(), obligation_count)
}

fn fail_closed_message_for_case(
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

fn assert_verified(case: &str, upstream_case: &str, min_obligations: usize) {
    let (result, obligation_count) = verify_port_case(case, upstream_case);
    assert!(
        obligation_count >= min_obligations,
        "{case} ({upstream_case}) should collect at least {min_obligations} obligation(s), got {obligation_count}"
    );
    assert!(
        matches!(result, VerifyResult::Verified),
        "{case} ({upstream_case}) should verify, got: {result:?}"
    );
}

fn assert_counterexample(case: &str, upstream_case: &str, min_obligations: usize) {
    let (result, obligation_count) = verify_port_case(case, upstream_case);
    assert!(
        obligation_count >= min_obligations,
        "{case} ({upstream_case}) should collect at least {min_obligations} obligation(s), got {obligation_count}"
    );
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "{case} ({upstream_case}) should produce a counterexample, got: {result:?}"
    );
}

const VERIFIED_CASES: &[(&str, &str, usize)] = &[
    (
        "generic_exec_identity_contract",
        "test_decorated_datatype_encodings",
        1,
    ),
    (
        "generic_exec_concrete_return_contract",
        "test_decorated_datatype_encodings",
        1,
    ),
    (
        "generic_spec_identity_u64_round_trip",
        "test_decorated_datatype_encodings",
        1,
    ),
    (
        "generic_struct_field_projection_preserves_payload",
        "test_generic_primitive_has_type",
        1,
    ),
    (
        "generic_struct_concrete_field_projection_preserves_value",
        "test_generic_primitive_has_type",
        1,
    ),
    (
        "generic_struct_bool_field_projection_preserves_value",
        "",
        1,
    ),
    ("u8_const_generic_range_upper_bound_verified", "", 1),
    ("u8_broadcast_range_surrogate_verified", "", 1),
    (
        "const_generic_array_parameter_currently_blocked",
        "const_generic",
        1,
    ),
];

const COUNTEREXAMPLE_CASES: &[(&str, &str, usize)] = &[
    (
        "generic_struct_concrete_field_projection_wrong_value_counterexample",
        "",
        1,
    ),
    (
        "generic_struct_field_projection_wrong_payload_counterexample",
        "",
        1,
    ),
    (
        "generic_struct_bool_field_projection_wrong_counterexample",
        "",
        1,
    ),
    (
        "u8_const_generic_range_strict_upper_bound_counterexample",
        "",
        1,
    ),
    ("u16_broadcast_range_surrogate_counterexample", "", 1),
];

const FAIL_CLOSED_CASES: &[(&str, &str, &[&str])] = &[
    (
        "const_generic_value_parameter_currently_blocked",
        "",
        &["unresolved variable `N`", "const generic", "unsupported"],
    ),
    (
        "const_generic_bool_parameter_currently_blocked",
        "",
        &["unresolved variable `B`", "const generic", "unsupported"],
    ),
    (
        "generic_old_state_projection_currently_blocked",
        "",
        &[
            "Unsupported old-state expression",
            "unsupported expression `macro`",
            "old!",
            "macro",
        ],
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
        .unwrap_or_else(|| panic!("generics port should define {const_name}"));

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
    let array = referenced_array_const(file, "GENERICS_RS_EXPECTED_ERROR_PATTERNS");
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
    let array = referenced_array_const(file, "GENERICS_RS_EXPECTED_CASES");
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
            "duplicate generics metadata for {case_id}"
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
    let verified =
        VERIFIED_CASES.iter().map(
            |(case_id, upstream_case_id, min_obligations)| CaseMetadata {
                case_id: (*case_id).to_string(),
                upstream_case_id: (*upstream_case_id).to_string(),
                expected_verdict: "verified".to_string(),
                min_obligations: *min_obligations,
                expected_error_patterns: Vec::new(),
            },
        );
    let counterexamples =
        COUNTEREXAMPLE_CASES
            .iter()
            .map(
                |(case_id, upstream_case_id, min_obligations)| CaseMetadata {
                    case_id: (*case_id).to_string(),
                    upstream_case_id: (*upstream_case_id).to_string(),
                    expected_verdict: "counterexample".to_string(),
                    min_obligations: *min_obligations,
                    expected_error_patterns: Vec::new(),
                },
            );
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
            entry["upstream_path"].as_str() == Some("source/rust_verify_test/tests/generics.rs")
        })
        .expect("Verus manifest should contain generics.rs row");

    row["expected_cases"]
        .as_array()
        .expect("generics.rs row should contain expected_cases")
        .iter()
        .map(|entry| CaseMetadata {
            case_id: entry["case_id"]
                .as_str()
                .expect("case_id should be a string")
                .to_string(),
            upstream_case_id: entry["upstream_case_id"].as_str().unwrap_or("").to_string(),
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
fn generics_rs_port_file_is_rust_syntax() {
    let source =
        std::fs::read_to_string(generics_port_path()).expect("generics port should be readable");
    syn::parse_file(&source).expect("generics port should parse as ordinary Rust syntax");
}

#[test]
fn generics_rs_pinned_upstream_case_shapes_are_present() {
    let path = pinned_upstream_generics_path();
    if !path.exists() {
        eprintln!(
            "skipping pinned upstream generics.rs shape check; missing {}",
            path.display()
        );
        return;
    }

    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", path.display()));
    for expected in [
        "#[test] const_generic",
        "#[test] const_generic_bool",
        "#[test] test_decorated_types",
        "#[test] test_decorated_datatype_encodings",
        "#[test] test_generic_primitive_has_type",
        "#[test] const_generics_int_ranges",
        "#[test] const_generics_broadcast",
        "struct Array<A, const N: usize>",
        "spec fn f<const A: usize>() -> int",
        "fn test_arr_len(arr: &Array<u8, 100>)",
        "struct S<A, const B: bool>",
        "spec fn f<const B: bool>() -> bool",
        "spec fn sizeof<A>() -> nat",
        "uninterp spec fn f<B>(s: Seq<&S>) -> Seq<B>",
        "struct Data<T: 'static>",
        "fn test(x: &mut Obj<Node>)",
        "proof fn test<const N : u8>()",
        "pub broadcast proof fn broadcaster<const X: u8>()",
        "fn moo(z: u16)",
    ] {
        assert!(
            source.contains(expected),
            "pinned upstream generics.rs should still contain {expected}"
        );
    }
}

#[test]
fn generics_rs_expected_case_metadata_is_exact() {
    let source =
        std::fs::read_to_string(generics_port_path()).expect("generics port should be readable");
    let file = syn::parse_file(&source).expect("generics port should parse as ordinary Rust");
    assert_eq!(metadata_entries(&file), expected_metadata());
}

#[test]
fn generics_rs_expected_case_metadata_matches_manifest() {
    let source =
        std::fs::read_to_string(generics_port_path()).expect("generics port should be readable");
    let file = syn::parse_file(&source).expect("generics port should parse as ordinary Rust");
    assert_eq!(metadata_entries(&file), manifest_expected_metadata());
}

#[test]
fn generics_rs_verified_subset_verifies_from_file() {
    for (case, upstream_case, min_obligations) in VERIFIED_CASES {
        assert_verified(case, upstream_case, *min_obligations);
    }
}

#[test]
fn generics_rs_counterexample_subset_is_rejected_from_file() {
    for (case, upstream_case, min_obligations) in COUNTEREXAMPLE_CASES {
        assert_counterexample(case, upstream_case, *min_obligations);
    }
}

#[test]
fn generics_rs_unsupported_boundaries_fail_closed_from_file() {
    let path = generics_port_path();
    let path = path.to_str().expect("generics port path should be UTF-8");

    for (case, upstream_case, expected_fragments) in FAIL_CLOSED_CASES {
        fail_closed_message_for_case(path, case, upstream_case, expected_fragments);
    }
}
