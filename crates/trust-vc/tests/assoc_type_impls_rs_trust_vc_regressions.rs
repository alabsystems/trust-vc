// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Executable guards for the first upstream assoc_type_impls.rs TrustVc slice.
//!
//! These tests intentionally do not claim full Verus assoc_type_impls.rs
//! parity. They pin a small Rust-valid impl-associated-type witness through
//! `trust_vc_types::View`, one generic associated-output equality-constraint
//! method, concrete associated-type projection normalization, and stable
//! direct/non-direct view fail-closed guards while the manifest keeps
//! `source/rust_verify_test/tests/assoc_type_impls.rs` as `unsupported-gap`.

mod common;

use std::{
    collections::{BTreeMap, BTreeSet},
    path::{Path, PathBuf},
};
use trust_vc_core::{
    list_trait_conformance_obligations, verify_function_from_file,
    verify_trait_conformance_obligation, VerifyResult,
};

#[path = "../../../evals/verus/ported/assoc_type_impls.rs"]
mod assoc_type_impls_port;

fn assoc_type_impls_port_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/ported/assoc_type_impls.rs")
}

fn verus_manifest_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/verus-tests.json")
}

fn pinned_upstream_assoc_type_impls_path() -> PathBuf {
    common::pinned_verus_test_path("assoc_type_impls.rs")
}

fn verify_case(path: &str, case: &str, upstream_case: &str) -> VerifyResult {
    verify_function_from_file(path, case)
        .unwrap_or_else(|err| panic!("{case} ({upstream_case}) should extract: {err}"))
}

fn expect_error(path: &str, case: &str, upstream_case: &str, expected_fragment: &str) {
    let message = match verify_function_from_file(path, case) {
        Ok(VerifyResult::Error { message }) => message,
        Ok(result) => {
            panic!("{case} ({upstream_case}) should fail closed with Error, got: {result:?}")
        }
        Err(err) => err.to_string(),
    };

    assert!(
        message.contains(expected_fragment),
        "{case} ({upstream_case}) error should contain {expected_fragment:?}, got: {message}"
    );
}

const VERIFIED_CASES: &[(&str, &str)] = &[
    ("impl_associated_view_type_via_cow_verified", "trait_poly"),
    (
        "associated_type_equality_output_method_verified",
        "trait_typ_equality1",
    ),
    (
        "associated_type_local_projection_normalizes_to_u8_verified",
        "assoc_normalize",
    ),
    // Phase A3: a PARAMETER typed by a concrete `<S as Tr>::X` projection now
    // resolves to the impl's `type X = u8` binding and verifies `x <= 255u8`
    // (was fail-closed "unrecognized types" before A3).
    (
        "associated_type_parameter_projection_normalizes_to_u8_verified",
        "assoc_normalize",
    ),
    // Phase A3: a client consuming an associated-type-RETURNING trait method's
    // `ensures(result == 7u64)` verifies against the per-impl concrete axiom.
    (
        "associated_type_returning_method_client_consumes_ensures_verified",
        "ensures_projection_poly",
    ),
];

const COUNTEREXAMPLE_CASES: &[(&str, &str)] = &[
    (
        "associated_type_trait_default_false_assert_counterexample",
        "assoc_poly_different",
    ),
    (
        "associated_type_local_projection_too_strong_bound_counterexample",
        "assoc_normalize",
    ),
    // Control: the SAME client asserting the wrong value (`== 8`) is refuted —
    // the A3 axiom carries exactly `result == 7`, not a vacuous pass.
    (
        "associated_type_returning_method_client_wrong_value_counterexample",
        "ensures_projection_poly",
    ),
];

const ERROR_CASES: &[(&str, &str, &str)] = &[
    (
        "impl_associated_view_type_direct_currently_errors",
        "trait_poly",
        "collection operation 'view' requires a collection receiver",
    ),
    (
        "impl_associated_view_type_cow_variable_currently_errors",
        "trait_poly",
        "direct Cow::Owned",
    ),
];

const EXPECTED_CASES: &[(&str, &str, &str, usize)] = &[
    (
        "impl_associated_view_type_via_cow_verified",
        "trait_poly",
        "verified",
        1,
    ),
    (
        "associated_type_equality_output_method_verified",
        "trait_typ_equality1",
        "verified",
        1,
    ),
    (
        "associated_type_local_projection_normalizes_to_u8_verified",
        "assoc_normalize",
        "verified",
        1,
    ),
    (
        "associated_type_trait_default_false_assert_counterexample",
        "assoc_poly_different",
        "counterexample",
        1,
    ),
    (
        "associated_type_local_projection_too_strong_bound_counterexample",
        "assoc_normalize",
        "counterexample",
        1,
    ),
    (
        "impl_associated_view_type_cow_variable_currently_errors",
        "trait_poly",
        "error",
        1,
    ),
    (
        "impl_associated_view_type_direct_currently_errors",
        "trait_poly",
        "error",
        1,
    ),
    (
        "associated_type_parameter_projection_normalizes_to_u8_verified",
        "assoc_normalize",
        "verified",
        1,
    ),
    (
        "associated_type_returning_method_client_consumes_ensures_verified",
        "ensures_projection_poly",
        "verified",
        1,
    ),
    (
        "associated_type_returning_method_client_wrong_value_counterexample",
        "ensures_projection_poly",
        "counterexample",
        1,
    ),
];

const EXPECTED_ERROR_PATTERNS: &[(&str, &[&str])] = &[
    (
        "impl_associated_view_type_cow_variable_currently_errors",
        &["direct Cow::Owned"],
    ),
    (
        "impl_associated_view_type_direct_currently_errors",
        &["collection operation 'view' requires a collection receiver"],
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
        .unwrap_or_else(|| panic!("assoc_type_impls port should define {const_name}"));

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
    let array = referenced_array_const(file, "ASSOC_TYPE_IMPLS_RS_FAIL_CLOSED_ERROR_PATTERNS");
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
    let array = referenced_array_const(file, "ASSOC_TYPE_IMPLS_RS_EXPECTED_CASES");
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
            "duplicate assoc_type_impls metadata for {case_id}"
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
    let mut error_patterns = EXPECTED_ERROR_PATTERNS
        .iter()
        .map(|(case_id, patterns)| {
            (
                (*case_id).to_string(),
                patterns
                    .iter()
                    .map(|pattern| (*pattern).to_string())
                    .collect::<Vec<_>>(),
            )
        })
        .collect::<BTreeMap<_, _>>();

    EXPECTED_CASES
        .iter()
        .map(
            |(case_id, upstream_case_id, expected_verdict, min_obligations)| CaseMetadata {
                case_id: (*case_id).to_string(),
                upstream_case_id: (*upstream_case_id).to_string(),
                expected_verdict: (*expected_verdict).to_string(),
                min_obligations: *min_obligations,
                expected_error_patterns: error_patterns.remove(*case_id).unwrap_or_default(),
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
            entry["upstream_path"].as_str()
                == Some("source/rust_verify_test/tests/assoc_type_impls.rs")
        })
        .expect("Verus manifest should contain assoc_type_impls.rs row");

    row["expected_cases"]
        .as_array()
        .expect("assoc_type_impls.rs row should contain expected_cases")
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
            expected_error_patterns: entry["expected_error_patterns"]
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

#[test]
fn assoc_type_impls_rs_expected_case_metadata_is_exact() {
    let source = std::fs::read_to_string(assoc_type_impls_port_path())
        .expect("assoc_type_impls port should be readable");
    let file = syn::parse_file(&source)
        .expect("assoc_type_impls port should parse as ordinary Rust syntax");
    assert_eq!(metadata_entries(&file), expected_metadata());
    assert!(
        source.contains("assoc_type_impls_rs_fail_closed_error_patterns"),
        "assoc_type_impls port should export fail-closed error-pattern metadata"
    );
}

#[test]
fn assoc_type_impls_rs_expected_case_metadata_matches_manifest() {
    let source = std::fs::read_to_string(assoc_type_impls_port_path())
        .expect("assoc_type_impls port should be readable");
    let file = syn::parse_file(&source)
        .expect("assoc_type_impls port should parse as ordinary Rust syntax");
    assert_eq!(metadata_entries(&file), manifest_expected_metadata());
}

#[test]
fn assoc_type_impls_rs_port_file_is_rust_syntax() {
    let source = std::fs::read_to_string(assoc_type_impls_port_path())
        .expect("assoc_type_impls port should be readable");
    syn::parse_file(&source).expect("assoc_type_impls port should parse as ordinary Rust syntax");
}

#[test]
fn assoc_type_impls_rs_pinned_upstream_case_shapes_are_present() {
    let path = pinned_upstream_assoc_type_impls_path();
    if !path.exists() {
        eprintln!(
            "skipping pinned upstream assoc_type_impls.rs shape check; missing {}",
            path.display()
        );
        return;
    }

    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", path.display()));
    for expected in [
        "trait_poly",
        "assoc_normalize",
        "trait_typ_equality1",
        "trait_typ_equality_dispatch_spec",
    ] {
        assert!(
            source.contains(expected),
            "pinned upstream assoc_type_impls.rs should still contain {expected}"
        );
    }
}

#[test]
fn assoc_type_impls_rs_verified_subset_verifies_from_file() {
    let path = assoc_type_impls_port_path();
    let path = path
        .to_str()
        .expect("assoc_type_impls port path should be UTF-8");

    for (case, upstream_case) in VERIFIED_CASES {
        let result = verify_case(path, case, upstream_case);
        assert!(
            matches!(result, VerifyResult::Verified),
            "{case} ({upstream_case}) should verify, got: {result:?}"
        );
    }
}

#[test]
fn assoc_type_impls_rs_counterexample_subset_is_rejected_from_file() {
    let path = assoc_type_impls_port_path();
    let path = path
        .to_str()
        .expect("assoc_type_impls port path should be UTF-8");

    for (case, upstream_case) in COUNTEREXAMPLE_CASES {
        let result = verify_case(path, case, upstream_case);
        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "{case} ({upstream_case}) should be rejected, got: {result:?}"
        );
    }
}

// The A3 client-consume axiom for `AssocReturningEnsures::produce` is a FORGED
// fact unless the impl body discharges the trait `ensures`. It is justified
// ENTIRELY by the per-impl conformance obligation, which the file's verdict
// requires. This test witnesses, on the corpus surface, that the conforming
// impl's own conformance obligation Verifies — the load-bearing gate under the
// "verified" client case above.
#[test]
fn assoc_type_impls_rs_assoc_returning_ensures_conformance_obligation_verifies() {
    let path = assoc_type_impls_port_path();
    let path = path
        .to_str()
        .expect("assoc_type_impls port path should be UTF-8");

    let obligations = list_trait_conformance_obligations(path)
        .expect("assoc_type_impls port should list conformance obligations");
    let name = "trait impl conformance AssocReturningEnsures::produce for AssocProducer";
    assert!(
        obligations.iter().any(|o| o == name),
        "expected conformance obligation {name:?}, got: {obligations:?}"
    );

    let result = verify_trait_conformance_obligation(path, name)
        .expect("conformance obligation should be checkable");
    assert!(
        matches!(result, VerifyResult::Verified),
        "conforming produce()->Self::V impl must pass conformance, got: {result:?}"
    );
}

#[test]
fn assoc_type_impls_rs_fail_closed_cases_from_file() {
    let path = assoc_type_impls_port_path();
    let path = path
        .to_str()
        .expect("assoc_type_impls port path should be UTF-8");

    for (case, upstream_case, expected_fragment) in ERROR_CASES {
        expect_error(path, case, upstream_case, expected_fragment);
    }
}
