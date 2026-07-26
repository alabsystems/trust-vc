// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Executable guards for the first upstream adts_opaque.rs TrustVc scout.
//!
//! These tests intentionally keep the upstream manifest entry unsupported-gap.
//! They prove only the Rust-valid transparent/opaque ADT accessor subset TrustVc
//! can extract today, reject wrong transparent fields plus wrong or unrevealed
//! opaque accessor claims, and pin qualified/associated reveal targets as
//! fail-closed unsupported boundaries.

use std::{
    collections::{BTreeMap, BTreeSet},
    path::PathBuf,
};
use trust_vc_core::{
    extract_verification_conditions_with_file_context, verify_function_from_file, VerifyResult,
};

fn adts_opaque_port_path() -> PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/ported/adts_opaque.rs")
}

fn verus_manifest_path() -> PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/verus-tests.json")
}

fn verify_case_with_obligations(case: &str, upstream_case: &str) -> (VerifyResult, usize) {
    let path = adts_opaque_port_path();
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
    let obligation_count = vc.obligations().len();

    (vc.verify(), obligation_count)
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

const VERIFIED_CASES: &[(&str, &str, usize)] = &[
    (
        "transparent_adt_field_projection_verified",
        "test_transparent_struct_1",
        1,
    ),
    (
        "opaque_adt_accessor_reveal_verified",
        "test_opaque_fn/test_opaque_struct_1",
        1,
    ),
    (
        "opaque_adt_reveal_preserves_constructor_facts_verified",
        "test_opaque_struct_1 constructor field facts after reveal",
        1,
    ),
    (
        "opaque_adt_precondition_fact_verified",
        "test_opaque_struct_1 requires get_passengers(c) == 12",
        1,
    ),
    (
        "opaque_adt_precondition_reveal_exposes_field_verified",
        "test_opaque_struct_1 reveal connects accessor precondition to field",
        1,
    ),
    (
        "opaque_enum_record_accessor_reveal_verified",
        "test_needs_pub_abstract3 concrete enum accessor after reveal",
        1,
    ),
    (
        "opaque_enum_unit_accessor_reveal_verified",
        "test_needs_pub_abstract3 concrete unit enum accessor after reveal",
        1,
    ),
    // Flipped from FAIL_CLOSED_CASES 2026-07-04: nested concrete ADT params are
    // supported since the native Sort::Datatype migration (0737e64) + the ay
    // congruence fix consumed via the 3a23c63 pin bump. Step-2 control ledger:
    // wrong-value twin (==13) -> Counterexample; reveal!-deletion mutation ->
    // Counterexample (nested opacity intact); recorded in the step-2 review notes.
    (
        "opaque_nested_adt_accessor_reveal_verified",
        "test_opaque_struct_1 nested concrete ADT accessor boundary",
        1,
    ),
];

const COUNTEREXAMPLE_CASES: &[(&str, &str, usize)] = &[(
    "transparent_adt_wrong_field_projection_compute_counterexample",
    "test_transparent_struct_1 false field projection",
    1,
)];

const MUST_NOT_VERIFY_CASES: &[(&str, &str, usize)] = &[
    (
        "opaque_adt_accessor_revealed_wrong_value_must_not_verify",
        "test_opaque_fn false revealed accessor assertion",
        1,
    ),
    (
        "opaque_adt_accessor_without_reveal_must_not_verify",
        "test_opaque_fn_modules_fail",
        1,
    ),
    (
        "opaque_adt_precondition_without_reveal_must_not_expose_field",
        "test_opaque_struct_1 opaque accessor precondition without reveal",
        1,
    ),
    (
        "opaque_enum_record_accessor_wrong_value_must_not_verify",
        "test_needs_pub_abstract3 concrete enum false accessor assertion",
        1,
    ),
    // Flipped from FAIL_CLOSED_CASES 2026-07-04 together with the nested reveal
    // case above: this FALSE twin (asserts ==13) now extracts and is refuted with
    // a concrete datatype counterexample (step-2 control ledger). Keeping it here
    // makes the nested-opacity soundness canary independently executed forever.
    (
        "opaque_nested_adt_accessor_wrong_value_must_not_verify",
        "test_opaque_struct_1 nested concrete ADT false accessor boundary",
        1,
    ),
];

const FAIL_CLOSED_CASES: &[(&str, &str, &[&str])] = &[
    (
        "qualified_opaque_adt_reveal_fails_closed",
        "test_opaque_fn_modules_pass qualified reveal boundary",
        &[
            "supports only unqualified function names",
            "module_car_passengers",
        ],
    ),
    (
        "associated_opaque_method_reveal_fails_closed",
        "test_opaque_fn associated method reveal boundary",
        &[
            "supports only unqualified function names",
            "OpaqueMethodWitness :: always",
        ],
    ),
];

const EXPECTED_CASES: &[(&str, &str, &str, usize)] = &[
    (
        "transparent_adt_field_projection_verified",
        "test_transparent_struct_1",
        "verified",
        1,
    ),
    (
        "opaque_adt_accessor_reveal_verified",
        "test_opaque_fn",
        "verified",
        1,
    ),
    (
        "opaque_adt_reveal_preserves_constructor_facts_verified",
        "test_opaque_struct_1",
        "verified",
        1,
    ),
    (
        "transparent_adt_wrong_field_projection_compute_counterexample",
        "test_transparent_struct_1",
        "counterexample",
        1,
    ),
    (
        "qualified_opaque_adt_reveal_fails_closed",
        "test_opaque_fn_modules_pass",
        "error",
        0,
    ),
    (
        "associated_opaque_method_reveal_fails_closed",
        "test_opaque_fn",
        "error",
        0,
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
        .unwrap_or_else(|| panic!("adts_opaque port should define {const_name}"));

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
    let array = referenced_array_const(file, "ADTS_OPAQUE_RS_FAIL_CLOSED_ERROR_PATTERNS");
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
    let array = referenced_array_const(file, "ADTS_OPAQUE_RS_EXPECTED_CASES");
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
            "duplicate adts_opaque metadata for {case_id}"
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
    let mut error_patterns = BTreeMap::new();
    for (case, _, expected_fragments) in FAIL_CLOSED_CASES.iter().take(2) {
        assert!(
            error_patterns
                .insert(
                    *case,
                    expected_fragments
                        .iter()
                        .map(|fragment| (*fragment).to_string())
                        .collect::<Vec<_>>(),
                )
                .is_none(),
            "duplicate error-case metadata for {case}"
        );
    }

    EXPECTED_CASES
        .iter()
        .map(
            |(case_id, upstream_case_id, expected_verdict, min_obligations)| CaseMetadata {
                case_id: (*case_id).to_string(),
                upstream_case_id: (*upstream_case_id).to_string(),
                expected_verdict: (*expected_verdict).to_string(),
                min_obligations: *min_obligations,
                expected_error_patterns: error_patterns.remove(case_id).unwrap_or_default(),
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
            entry["upstream_path"].as_str() == Some("source/rust_verify_test/tests/adts_opaque.rs")
        })
        .expect("Verus manifest should contain adts_opaque.rs row");

    row["expected_cases"]
        .as_array()
        .expect("adts_opaque.rs row should contain expected_cases")
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
fn adts_opaque_rs_expected_case_metadata_is_exact() {
    let path = adts_opaque_port_path();
    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|err| panic!("{} should be readable: {err}", path.display()));
    let file = syn::parse_file(&source)
        .unwrap_or_else(|err| panic!("{} should parse as Rust syntax: {err}", path.display()));
    assert_eq!(metadata_entries(&file), expected_metadata());
    assert!(
        source.contains("adts_opaque_rs_expected_cases")
            && source.contains("adts_opaque_rs_fail_closed_error_patterns"),
        "adts_opaque port should export expected-case and error-pattern metadata"
    );
}

#[test]
fn adts_opaque_rs_expected_case_metadata_matches_manifest() {
    let path = adts_opaque_port_path();
    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|err| panic!("{} should be readable: {err}", path.display()));
    let file = syn::parse_file(&source)
        .unwrap_or_else(|err| panic!("{} should parse as Rust syntax: {err}", path.display()));
    assert_eq!(metadata_entries(&file), manifest_expected_metadata());
}

#[test]
fn adts_opaque_rs_verified_subset_verifies_from_file() {
    for (case, upstream_case, min_obligations) in VERIFIED_CASES {
        let (result, obligation_count) = verify_case_with_obligations(case, upstream_case);
        assert!(
            obligation_count >= *min_obligations,
            "{case} ({upstream_case}) should collect at least {min_obligations} obligation(s), got {obligation_count}"
        );
        assert!(
            matches!(result, VerifyResult::Verified),
            "{case} ({upstream_case}) should verify, got: {result:?}"
        );
    }
}

#[test]
fn adts_opaque_rs_counterexample_subset_is_rejected_from_file() {
    for (case, upstream_case, min_obligations) in COUNTEREXAMPLE_CASES {
        let (result, obligation_count) = verify_case_with_obligations(case, upstream_case);
        assert!(
            obligation_count >= *min_obligations,
            "{case} ({upstream_case}) should collect at least {min_obligations} obligation(s), got {obligation_count}"
        );
        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "{case} ({upstream_case}) should be rejected, got: {result:?}"
        );
    }
}

#[test]
fn adts_opaque_rs_unrevealed_opaque_accessor_must_not_verify_from_file() {
    for (case, upstream_case, min_obligations) in MUST_NOT_VERIFY_CASES {
        let (result, obligation_count) = verify_case_with_obligations(case, upstream_case);
        assert!(
            obligation_count >= *min_obligations,
            "{case} ({upstream_case}) should collect at least {min_obligations} obligation(s), got {obligation_count}"
        );
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
fn adts_opaque_rs_qualified_reveal_boundary_fails_closed_from_file() {
    let path = adts_opaque_port_path();
    let path = path
        .to_str()
        .expect("adts_opaque port path should be UTF-8");

    for (case, upstream_case, expected_fragments) in FAIL_CLOSED_CASES {
        expect_fail_closed(path, case, upstream_case, expected_fragments);
    }
}
