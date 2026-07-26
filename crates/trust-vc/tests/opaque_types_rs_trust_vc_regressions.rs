// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Executable guards for the first upstream opaque_types.rs TrustVc scout slice.
//!
//! These tests intentionally keep `source/rust_verify_test/tests/opaque_types.rs`
//! as an unsupported gap. They pin only a small Rust-valid type-boundary slice:
//! generic static dispatch over a trait method contract, a bad implementation
//! of a trait method contract, associated-output projection through a generic
//! trait bound, and return-position `impl Trait` boundaries that must fail
//! closed instead of being treated as replacement evidence.

mod common;

use std::{
    collections::BTreeSet,
    path::{Path, PathBuf},
};
use trust_vc_core::{verify_function_from_file, VerifyResult};

fn opaque_types_port_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/ported/opaque_types.rs")
}

fn verus_manifest_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/verus-tests.json")
}

fn pinned_upstream_opaque_types_path() -> PathBuf {
    common::pinned_verus_test_path("opaque_types.rs")
}

fn verify_case(path: &str, case: &str, upstream_case: &str) -> VerifyResult {
    verify_function_from_file(path, case)
        .unwrap_or_else(|err| panic!("{case} ({upstream_case}) should extract: {err}"))
}

fn expect_fail_closed(path: &str, case: &str, upstream_case: &str, expected_fragments: &[&str]) {
    let message = match verify_function_from_file(path, case) {
        Ok(VerifyResult::Error { message }) => message,
        Ok(VerifyResult::Unknown { reason, .. }) => reason,
        Ok(result) => {
            panic!("{case} ({upstream_case}) should fail closed, got: {result:?}")
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

const VERIFIED_CASES: &[(&str, &str)] = &[
    (
        "opaque_types_trait_method_contract_verified",
        "test_return_opaque_type_allows_trait_functions",
    ),
    (
        "opaque_types_associated_output_projection_verified",
        "test_return_opaque_type_reveal_real_type",
    ),
];

const COUNTEREXAMPLE_CASES: &[(&str, &str)] = &[
    (
        "opaque_types_trait_impl_wrong_return_counterexample",
        "test_return_opaque_type_allows_trait_functions",
    ),
    (
        "opaque_types_associated_output_wrong_return_counterexample",
        "test_return_opaque_type_reveal_real_type",
    ),
];

const FAIL_CLOSED_CASES: &[(&str, &str, &[&str])] = &[
    (
        "opaque_types_return_impl_trait_fails_closed",
        "test_return_opaque_type",
        &["unrecognized types", "implOpaqueTypesDummyTrait"],
    ),
    (
        "opaque_types_return_impl_trait_with_assoc_fails_closed",
        "test_return_opaque_type_reveal_real_type",
        &["unrecognized types", "implOpaqueTypesAssociatedOutputTrait"],
    ),
];

#[derive(Debug, Eq, PartialEq)]
struct CaseMetadata {
    case_id: String,
    upstream_case_id: String,
    expected_verdict: String,
    min_obligations: usize,
}

fn literal_string(expr: &syn::Expr) -> String {
    let syn::Expr::Lit(lit) = expr else {
        panic!("expected string literal in opaque_types metadata");
    };
    let syn::Lit::Str(value) = &lit.lit else {
        panic!("expected string literal in opaque_types metadata");
    };
    value.value()
}

fn literal_usize(expr: &syn::Expr) -> usize {
    let syn::Expr::Lit(lit) = expr else {
        panic!("expected integer literal in opaque_types metadata");
    };
    let syn::Lit::Int(value) = &lit.lit else {
        panic!("expected integer literal in opaque_types metadata");
    };
    value
        .base10_parse()
        .expect("min obligations should be a usize literal")
}

fn referenced_array_const(file: &syn::File, const_name: &str) -> syn::ExprArray {
    let const_item = file
        .items
        .iter()
        .find_map(|item| match item {
            syn::Item::Const(item) if item.ident == const_name => Some(item),
            _ => None,
        })
        .unwrap_or_else(|| panic!("opaque_types port should define {const_name}"));

    let syn::Expr::Reference(reference) = const_item.expr.as_ref() else {
        panic!("{const_name} should be a referenced array");
    };
    let syn::Expr::Array(array) = reference.expr.as_ref() else {
        panic!("{const_name} should reference an array");
    };
    array.clone()
}

fn metadata_entries(file: &syn::File, const_name: &str) -> Vec<CaseMetadata> {
    let array = referenced_array_const(file, const_name);
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
            "duplicate opaque_types metadata for {case_id} in {const_name}"
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
    let verified = VERIFIED_CASES
        .iter()
        .map(|(case_id, upstream_case_id)| CaseMetadata {
            case_id: (*case_id).to_string(),
            upstream_case_id: (*upstream_case_id).to_string(),
            expected_verdict: "verified".to_string(),
            min_obligations: 1,
        });
    let counterexamples = COUNTEREXAMPLE_CASES
        .iter()
        .map(|(case_id, upstream_case_id)| CaseMetadata {
            case_id: (*case_id).to_string(),
            upstream_case_id: (*upstream_case_id).to_string(),
            expected_verdict: "counterexample".to_string(),
            min_obligations: 1,
        });
    verified.chain(counterexamples).collect()
}

fn expected_blocker_metadata() -> Vec<CaseMetadata> {
    FAIL_CLOSED_CASES
        .iter()
        .map(|(case_id, upstream_case_id, _)| CaseMetadata {
            case_id: (*case_id).to_string(),
            upstream_case_id: (*upstream_case_id).to_string(),
            expected_verdict: "blocked".to_string(),
            min_obligations: 0,
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
            entry["upstream_path"].as_str() == Some("source/rust_verify_test/tests/opaque_types.rs")
        })
        .expect("Verus manifest should contain opaque_types.rs row")
        .clone()
}

fn manifest_expected_case_metadata() -> Vec<CaseMetadata> {
    manifest_row()["expected_cases"]
        .as_array()
        .expect("opaque_types manifest row should contain expected_cases")
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

fn manifest_known_gaps() -> Vec<String> {
    manifest_row()["known_gaps"]
        .as_array()
        .expect("opaque_types manifest row should contain known_gaps")
        .iter()
        .map(|gap| {
            gap.as_str()
                .expect("known_gaps entries should be strings")
                .to_string()
        })
        .collect()
}

#[test]
fn opaque_types_rs_port_file_is_rust_syntax() {
    let source = std::fs::read_to_string(opaque_types_port_path())
        .expect("opaque_types port should be readable");
    syn::parse_file(&source).expect("opaque_types port should parse as ordinary Rust syntax");
}

#[test]
fn opaque_types_rs_pinned_upstream_case_shapes_are_present() {
    let path = pinned_upstream_opaque_types_path();
    if !path.exists() {
        eprintln!(
            "skipping pinned upstream opaque_types.rs shape check; missing {}",
            path.display()
        );
        return;
    }

    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", path.display()));
    for expected in [
        "test_return_opaque_type",
        "test_return_opaque_type_hides_real_type",
        "test_return_opaque_type_allows_trait_functions",
        "test_return_opaque_type_reveal_real_type",
        "test_opaque_function_return_value_type",
        "test_opaque_type_projection_with_annotation",
    ] {
        assert!(
            source.contains(expected),
            "pinned upstream opaque_types.rs should still contain {expected}"
        );
    }
}

#[test]
fn opaque_types_rs_expected_case_metadata_matches_manifest() {
    let source = std::fs::read_to_string(opaque_types_port_path())
        .expect("opaque_types port should be readable");
    let file =
        syn::parse_file(&source).expect("opaque_types port should parse as ordinary Rust syntax");
    assert_eq!(
        metadata_entries(&file, "OPAQUE_TYPES_RS_EXPECTED_CASES"),
        expected_metadata(),
        "opaque_types accepted evidence metadata should match the focused regression inventory exactly"
    );
    assert_eq!(
        metadata_entries(&file, "OPAQUE_TYPES_RS_BLOCKED_CASES"),
        expected_blocker_metadata(),
        "opaque_types blocked boundary metadata should match the focused regression inventory exactly"
    );
    assert_eq!(
        manifest_expected_case_metadata(),
        expected_metadata(),
        "opaque_types manifest should match stable verified/counterexample metadata exactly"
    );

    let manifest_cases = manifest_expected_case_metadata();
    let known_gaps = manifest_known_gaps();
    for blocked in expected_blocker_metadata() {
        assert!(
            !manifest_cases
                .iter()
                .any(|case| case.case_id == blocked.case_id),
            "{} should stay out of manifest expected_cases while it is blocked",
            blocked.case_id
        );
        assert!(
            known_gaps.iter().any(|gap| gap.contains(&blocked.case_id)),
            "{} should remain called out in opaque_types manifest known_gaps",
            blocked.case_id
        );
    }
}

#[test]
fn opaque_types_rs_verified_subset_verifies_from_file() {
    let path = opaque_types_port_path();
    let path = path
        .to_str()
        .expect("opaque_types port path should be UTF-8");

    for (case, upstream_case) in VERIFIED_CASES {
        let result = verify_case(path, case, upstream_case);
        assert!(
            matches!(result, VerifyResult::Verified),
            "{case} ({upstream_case}) should verify, got: {result:?}"
        );
    }
}

#[test]
fn opaque_types_rs_counterexample_subset_is_rejected_from_file() {
    let path = opaque_types_port_path();
    let path = path
        .to_str()
        .expect("opaque_types port path should be UTF-8");

    for (case, upstream_case) in COUNTEREXAMPLE_CASES {
        let result = verify_case(path, case, upstream_case);
        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "{case} ({upstream_case}) should be rejected, got: {result:?}"
        );
    }
}

#[test]
fn opaque_types_rs_impl_trait_boundary_fails_closed_from_file() {
    let path = opaque_types_port_path();
    let path = path
        .to_str()
        .expect("opaque_types port path should be UTF-8");

    for (case, upstream_case, expected_fragments) in FAIL_CLOSED_CASES {
        expect_fail_closed(path, case, upstream_case, expected_fragments);
    }
}
