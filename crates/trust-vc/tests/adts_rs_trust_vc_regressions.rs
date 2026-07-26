// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Executable guards for the currently ported upstream adts.rs subset.
//!
//! These tests intentionally do not claim full Verus adts.rs parity. They prove
//! the listed upstream-derived ADT construction, projection, helper, alias, and
//! update-expression slices execute through TrustVc while the manifest keeps
//! `source/rust_verify_test/tests/adts.rs` fail-closed.

mod common;

use std::{
    collections::BTreeSet,
    path::{Path, PathBuf},
};
use trust_vc_core::{
    extract_verification_conditions_with_file_context, verify_function_from_file, VerifyResult,
};

fn adts_port_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/ported/adts.rs")
}

fn verus_manifest_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/verus-tests.json")
}

fn pinned_upstream_adts_path() -> PathBuf {
    common::pinned_verus_test_path("adts.rs")
}

const VERIFIED_CASES: &[(&str, &str, usize)] = &[
    (
        "struct_literal_field_projection_preserves_named_field_order",
        "test_struct_1/test_struct_4",
        2,
    ),
    (
        "struct_parameter_projection_preserves_required_field",
        "test_struct_2",
        1,
    ),
    (
        "local_struct_binding_preserves_projected_fields",
        "test_struct_3/test_struct_4",
        2,
    ),
    ("compact_car_u8_field_is_nonnegative", "test_struct_u8", 1),
    ("struct_update_copies_omitted_fields", "test_update1", 2),
    (
        "struct_update_with_contract_call_preserves_ensured_field",
        "test_update2",
        2,
    ),
    (
        "type_alias_parameter_projection_preserves_field",
        "type_alias_basic",
        1,
    ),
    (
        "tuple_struct_projection_preserves_positional_field",
        "test_regression_tuple_1",
        1,
    ),
    (
        "enum_unit_variant_helper_on_constructed_left",
        "resolve_ctors_for_unit_syntax enum unit constructor prefix",
        1,
    ),
    (
        "enum_variant_helper_methods_on_constructed_tuple_variant",
        "simple enum is_Variant/get_Variant_field helper parity",
        1,
    ),
    (
        "enum_record_variant_match_extracts_named_field",
        "test_enum_adt_mod",
        1,
    ),
    (
        "enum_tuple_variant_match_extracts_payload",
        "test_enum_adt_mod tuple-variant match payload extraction",
        1,
    ),
    (
        "enum_named_field_helper_on_constructed_record_variant",
        "test_is_variant_get_named_field",
        1,
    ),
    (
        "generic_single_variant_helper_on_arbitrary_value",
        "generic single-variant helper",
        1,
    ),
];

const FAIL_CLOSED_CASES: &[(&str, &str)] = &[
    (
        "struct_literal_field_projection_wrong_value_fails_closed",
        "test_struct_1 false projection",
    ),
    (
        "enum_variant_helper_wrong_payload_fails_closed",
        "simple enum get_Variant_field false payload",
    ),
    (
        "enum_tuple_variant_match_wrong_payload_fails_closed",
        "test_enum_adt_mod tuple-variant match false payload",
    ),
];

const EXTRACTION_FAIL_CLOSED_CASES: &[(&str, &str)] = &[(
    "recursive_enum_helpers_fail_closed",
    "recursive source enums remain unsupported",
)];

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
        .unwrap_or_else(|| panic!("adts port should define {const_name}"));

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
    let array = referenced_array_const(file, "ADTS_RS_EXPECTED_CASES");
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
            "duplicate adts metadata for {case_id}"
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
    VERIFIED_CASES
        .iter()
        .map(
            |(case_id, upstream_case_id, min_obligations)| CaseMetadata {
                case_id: (*case_id).to_string(),
                upstream_case_id: (*upstream_case_id).to_string(),
                expected_verdict: "verified".to_string(),
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
            entry["upstream_path"].as_str() == Some("source/rust_verify_test/tests/adts.rs")
        })
        .expect("Verus manifest should contain adts.rs row");

    row["expected_cases"]
        .as_array()
        .expect("adts.rs row should contain expected_cases")
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

#[test]
fn adts_rs_port_file_is_rust_syntax() {
    let source = std::fs::read_to_string(adts_port_path()).expect("adts port should be readable");
    syn::parse_file(&source).expect("adts port should parse as ordinary Rust syntax");
}

#[test]
fn adts_rs_expected_case_metadata_is_exact() {
    let source = std::fs::read_to_string(adts_port_path()).expect("adts port should be readable");
    let file = syn::parse_file(&source).expect("adts port should parse as ordinary Rust syntax");
    assert_eq!(metadata_entries(&file), expected_metadata());
}

#[test]
fn adts_rs_expected_case_metadata_matches_manifest() {
    let source = std::fs::read_to_string(adts_port_path()).expect("adts port should be readable");
    let file = syn::parse_file(&source).expect("adts port should parse as ordinary Rust syntax");
    assert_eq!(metadata_entries(&file), manifest_expected_metadata());
}

#[test]
fn adts_rs_pinned_upstream_case_shapes_are_present() {
    let path = pinned_upstream_adts_path();
    if !path.exists() {
        eprintln!(
            "skipping pinned upstream adts.rs shape check; missing {}",
            path.display()
        );
        return;
    }

    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", path.display()));
    for expected in [
        "#[test] test_struct_1",
        "#[test] test_struct_2",
        "#[test] test_struct_3",
        "#[test] test_struct_4",
        "#[test] test_struct_u8",
        "#[test] test_update1",
        "#[test] test_update2",
        "#[test] test_enum_adt_mod",
        "#[test] test_is_variant_get_named_field",
        "#[test] resolve_ctors_for_unit_syntax",
        "#[test] test_regression_tuple_1",
        "#[test] type_alias_basic",
    ] {
        assert!(
            source.contains(expected),
            "pinned upstream adts.rs should still contain {expected}"
        );
    }
}

#[test]
fn adts_rs_verified_subset_verifies_from_file() {
    let path = adts_port_path();
    let path = path.to_str().expect("adts port path should be UTF-8");

    for (case, upstream_case, _) in VERIFIED_CASES {
        let result = verify_function_from_file(path, case)
            .unwrap_or_else(|err| panic!("{case} ({upstream_case}) should extract: {err}"));
        assert!(
            matches!(result, VerifyResult::Verified),
            "{case} ({upstream_case}) should verify, got: {result:?}"
        );
    }
}

#[test]
fn adts_rs_verified_subset_collects_obligations_from_file() {
    let path = adts_port_path();
    let source =
        std::fs::read_to_string(&path).unwrap_or_else(|err| panic!("adts port should read: {err}"));
    let file =
        syn::parse_file(&source).unwrap_or_else(|err| panic!("adts port should parse: {err}"));

    for (case, upstream_case, min_obligations) in VERIFIED_CASES {
        let function = file
            .items
            .iter()
            .find_map(|item| match item {
                syn::Item::Fn(function) if function.sig.ident == *case => Some(function),
                _ => None,
            })
            .unwrap_or_else(|| panic!("{case} ({upstream_case}) should exist in adts port"));
        let vc = extract_verification_conditions_with_file_context(&file, function)
            .unwrap_or_else(|err| panic!("{case} ({upstream_case}) should extract: {err}"));

        assert!(
            vc.obligations().len() >= *min_obligations,
            "{case} ({upstream_case}) should collect at least {min_obligations} obligation(s), got {}",
            vc.obligations().len()
        );
    }
}

#[test]
fn adts_rs_false_projection_subset_fails_closed_from_file() {
    let path = adts_port_path();
    let path = path.to_str().expect("adts port path should be UTF-8");

    for (case, upstream_case) in FAIL_CLOSED_CASES {
        let result = verify_function_from_file(path, case)
            .unwrap_or_else(|err| panic!("{case} ({upstream_case}) should extract: {err}"));
        assert!(
            matches!(
                result,
                VerifyResult::Counterexample { .. } | VerifyResult::Unknown { .. }
            ),
            "{case} ({upstream_case}) must not verify, got: {result:?}"
        );
    }
}

#[test]
fn adts_rs_unsupported_enum_shapes_fail_closed_from_file() {
    let path = adts_port_path();
    let path = path.to_str().expect("adts port path should be UTF-8");

    for (case, upstream_case) in EXTRACTION_FAIL_CLOSED_CASES {
        if let Ok(VerifyResult::Verified) = verify_function_from_file(path, case) {
            panic!("{case} ({upstream_case}) must not verify")
        }
    }
}
