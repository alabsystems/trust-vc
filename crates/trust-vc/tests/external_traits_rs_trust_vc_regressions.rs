// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Executable guards for the first upstream external_traits.rs scout slice.
//!
//! These tests intentionally keep the upstream file as an unsupported gap. They
//! prove the closest current TrustVc surface: external-annotated impl blocks can
//! inherit local trait_spec contracts when also marked trait_impl, inherited
//! requires/returns obligations are checked on impl methods, trait-bound callers
//! can use inherited ensures when inherited requires hold, bad bodies in that
//! surface are rejected, a bad inherited exact-return postcondition fails
//! closed, a simple associated-type declaration can coexist with a concrete
//! external impl method contract, impl-side contract extensions fail closed, and
//! duplicate matching trait specs fail closed.

use std::{
    collections::{BTreeMap, BTreeSet},
    path::PathBuf,
};
use trust_vc_core::{verify_function_from_file, VerifyResult};

fn external_traits_port_path() -> PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../evals/verus/ported/external_traits.rs")
}

fn verus_manifest_path() -> PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/verus-tests.json")
}

fn verify_case(path: &str, case: &str, upstream_case: &str) -> VerifyResult {
    verify_function_from_file(path, case)
        .unwrap_or_else(|err| panic!("{case} ({upstream_case}) should extract: {err}"))
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

const VERIFIED_CASES: &[(&str, &str)] = &[
    (
        "external_trait_impl_contract_verified",
        "test_trait_ok / external trait impl method specification",
    ),
    (
        "external_trait_requires_contract_verified",
        "test_trait3 / impl satisfies inherited requires and returns",
    ),
    (
        "external_trait_bound_caller_uses_inherited_ensures_verified",
        "test_trait1 / trait-bound caller uses inherited postcondition",
    ),
    (
        "external_trait_associated_type_declaration_verified",
        "test_trait5 / associated-type declaration coexists with concrete impl contract",
    ),
];

const COUNTEREXAMPLE_CASES: &[(&str, &str)] = &[(
    "external_trait_impl_false_assert_counterexample",
    "test_trait3 bad impl body in external trait implementation",
)];

const REJECTED_CASES: &[(&str, &str)] = &[(
    "external_trait_impl_wrong_postcondition_currently_unknown",
    "test_trait3 bad impl return currently fails closed instead of verifying",
)];

const FAIL_CLOSED_CASES: &[(&str, &str, &[&str])] = &[
    (
        "external_trait_impl_side_requires_currently_blocked",
        "test_trait_extension / impl-side external trait contract extension boundary",
        &["trait method implementation cannot declare requires"],
    ),
    // The duplicate-spec case fails closed EARLIER than it used to, and for a
    // stricter reason. The port writes the upstream `test_trait_dupe` shape as two
    // `#[trait_spec]` traits declaring the same method name plus two `#[trait_impl]`
    // blocks for the same concrete type — so the bare name
    // `external_trait_duplicate_spec_currently_fails_closed` denotes TWO bodies,
    // which is what `resolve_function_in_file` now says (`0a4c9f00`). Before that
    // it silently took the source-order-first body and the ambiguity was caught one
    // layer down, at contract inheritance ("ambiguous trait method contract
    // inheritance"). Detecting it at RESOLUTION is strictly stronger: it cannot be
    // reached past, it does not depend on the two impls carrying matching contract
    // attributes, and it holds for any pair of same-named bodies, not just
    // trait-inherited ones. The requirement the row encodes — a duplicate external
    // trait specification must fail closed, naming ambiguity as the reason — is
    // unchanged; both fragments below are pinned so a regression to a "not found"
    // string, or to silently picking one of the two, still reddens this row.
    (
        "external_trait_duplicate_spec_currently_fails_closed",
        "test_trait_dupe / duplicate external trait specification",
        &["is ambiguous in", "2 definitions share that name"],
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
        .unwrap_or_else(|| panic!("external_traits port should define {const_name}"));

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
    let array = referenced_array_const(file, "EXTERNAL_TRAITS_RS_EXPECTED_ERROR_PATTERNS");
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
    let array = referenced_array_const(file, "EXTERNAL_TRAITS_RS_EXPECTED_CASES");
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
            "duplicate external_traits metadata for {case_id}"
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
    let verified = VERIFIED_CASES
        .iter()
        .map(|(case_id, upstream_case_id)| CaseMetadata {
            case_id: (*case_id).to_string(),
            upstream_case_id: (*upstream_case_id).to_string(),
            expected_verdict: "verified".to_string(),
            min_obligations: 1,
            expected_error_patterns: Vec::new(),
        });
    let counterexamples = COUNTEREXAMPLE_CASES
        .iter()
        .map(|(case_id, upstream_case_id)| CaseMetadata {
            case_id: (*case_id).to_string(),
            upstream_case_id: (*upstream_case_id).to_string(),
            expected_verdict: "counterexample".to_string(),
            min_obligations: 1,
            expected_error_patterns: Vec::new(),
        });
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
            entry["upstream_path"].as_str()
                == Some("source/rust_verify_test/tests/external_traits.rs")
        })
        .expect("Verus manifest should contain external_traits.rs row");

    row["expected_cases"]
        .as_array()
        .expect("external_traits.rs row should contain expected_cases")
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
fn external_traits_rs_expected_case_metadata_is_exact() {
    let source = std::fs::read_to_string(external_traits_port_path())
        .expect("external_traits port should be readable");
    let file = syn::parse_file(&source)
        .expect("external_traits port should parse as ordinary Rust syntax");
    assert_eq!(metadata_entries(&file), expected_metadata());
}

#[test]
fn external_traits_rs_expected_case_metadata_matches_manifest() {
    let source = std::fs::read_to_string(external_traits_port_path())
        .expect("external_traits port should be readable");
    let file = syn::parse_file(&source)
        .expect("external_traits port should parse as ordinary Rust syntax");
    assert_eq!(metadata_entries(&file), manifest_expected_metadata());
}

#[test]
fn external_traits_rs_verified_subset_verifies_from_file() {
    let path = external_traits_port_path();
    let path = path
        .to_str()
        .expect("external_traits port path should be UTF-8");

    for (case, upstream_case) in VERIFIED_CASES {
        let result = verify_case(path, case, upstream_case);
        assert!(
            matches!(result, VerifyResult::Verified),
            "{case} ({upstream_case}) should verify, got: {result:?}"
        );
    }
}

#[test]
fn external_traits_rs_counterexample_subset_is_rejected_from_file() {
    let path = external_traits_port_path();
    let path = path
        .to_str()
        .expect("external_traits port path should be UTF-8");

    for (case, upstream_case) in COUNTEREXAMPLE_CASES {
        let result = verify_case(path, case, upstream_case);
        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "{case} ({upstream_case}) should be rejected, got: {result:?}"
        );
    }
}

#[test]
fn external_traits_rs_nonaccepted_boundaries_do_not_verify_from_file() {
    let path = external_traits_port_path();
    let path = path
        .to_str()
        .expect("external_traits port path should be UTF-8");

    for (case, upstream_case) in REJECTED_CASES {
        let result = verify_case(path, case, upstream_case);
        assert!(
            matches!(
                result,
                VerifyResult::Counterexample { .. } | VerifyResult::Unknown { .. }
            ),
            "{case} ({upstream_case}) should not verify, got: {result:?}"
        );
    }
}

#[test]
fn external_traits_rs_duplicate_contracts_fail_closed_from_file() {
    let path = external_traits_port_path();
    let path = path
        .to_str()
        .expect("external_traits port path should be UTF-8");

    for (case, upstream_case, expected_fragments) in FAIL_CLOSED_CASES {
        expect_fail_closed(path, case, upstream_case, expected_fragments);
    }
}
