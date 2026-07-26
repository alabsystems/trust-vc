// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Executable guards for the upstream recursive_types.rs TrustVc scout slice.
//!
//! These tests intentionally keep the upstream file as an unsupported gap. They
//! pin only the Rust-valid recursive enum/struct/Box and decreases-adjacent
//! witnesses listed in the port metadata, reject stable false claims, and keep
//! Verus positivity/external_body/boxed-inspection/diagnostic behavior
//! fail-closed. Solver `Unknown` is not accepted as evidence.

mod common;

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};
use trust_vc_core::{
    extract_verification_conditions_with_file_context, verify_function_from_file, VerifyResult,
};

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
struct ExpectedCase {
    case: String,
    upstream_case: String,
    status: String,
    min_obligations: usize,
    expected_error_patterns: Vec<String>,
}

fn recursive_types_port_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/ported/recursive_types.rs")
}

fn pinned_upstream_recursive_types_path() -> PathBuf {
    common::pinned_verus_test_path("recursive_types.rs")
}

#[allow(dead_code)]
fn verus_manifest_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/verus-tests.json")
}

fn port_file() -> syn::File {
    let source = std::fs::read_to_string(recursive_types_port_path())
        .expect("recursive_types port should be readable");
    syn::parse_file(&source).expect("recursive_types port should parse as ordinary Rust syntax")
}

fn port_function<'a>(file: &'a syn::File, case: &str, upstream_case: &str) -> &'a syn::ItemFn {
    file.items
        .iter()
        .find_map(|item| match item {
            syn::Item::Fn(function) if function.sig.ident == case => Some(function),
            _ => None,
        })
        .unwrap_or_else(|| panic!("{case} ({upstream_case}) should exist in recursive_types port"))
}

fn verify_case_with_obligations(case: &str, upstream_case: &str) -> (VerifyResult, usize) {
    let file = port_file();
    let function = port_function(&file, case, upstream_case);
    let vc = extract_verification_conditions_with_file_context(&file, function)
        .unwrap_or_else(|err| panic!("{case} ({upstream_case}) should extract VCs: {err}"));
    let obligations = vc.obligations().len();

    (vc.verify(), obligations)
}

fn reject_unknown(result: &VerifyResult, case: &str, upstream_case: &str) {
    if let VerifyResult::Unknown { reason, .. } = result {
        panic!(
            "{case} ({upstream_case}) returned solver Unknown, which is not stable evidence: {reason}"
        );
    }
}

fn fail_closed_message(path: &str, case: &str, upstream_case: &str) -> String {
    match verify_function_from_file(path, case) {
        Err(err) => err.to_string(),
        Ok(VerifyResult::Error { message }) => message,
        Ok(VerifyResult::Unknown { reason, .. }) => {
            panic!(
                "{case} ({upstream_case}) returned solver Unknown, which is not stable fail-closed evidence: {reason}"
            )
        }
        Ok(other) => {
            panic!("{case} ({upstream_case}) should fail closed with Error, got: {other:?}")
        }
    }
}

fn literal_string(expr: &syn::Expr) -> String {
    match expr {
        syn::Expr::Lit(syn::ExprLit {
            lit: syn::Lit::Str(lit),
            ..
        }) => lit.value(),
        _ => panic!("expected string literal in recursive_types metadata"),
    }
}

fn literal_usize(expr: &syn::Expr) -> usize {
    match expr {
        syn::Expr::Lit(syn::ExprLit {
            lit: syn::Lit::Int(lit),
            ..
        }) => lit.base10_parse::<usize>().unwrap_or_else(|err| {
            panic!("expected usize literal in recursive_types metadata: {err}")
        }),
        _ => panic!("expected usize literal in recursive_types metadata"),
    }
}

fn referenced_array_const(file: &syn::File, const_name: &str) -> syn::ExprArray {
    let const_item = file
        .items
        .iter()
        .find_map(|item| match item {
            syn::Item::Const(item) if item.ident == const_name => Some(item),
            _ => None,
        })
        .unwrap_or_else(|| panic!("recursive_types port should define {const_name}"));

    let syn::Expr::Reference(reference) = const_item.expr.as_ref() else {
        panic!("{const_name} should be a referenced array");
    };
    let syn::Expr::Array(array) = reference.expr.as_ref() else {
        panic!("{const_name} should reference an array");
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

    array.elems.iter().map(literal_string).collect()
}

fn error_pattern_entries(file: &syn::File) -> BTreeMap<String, Vec<String>> {
    let array = referenced_array_const(file, "RECURSIVE_TYPES_RS_EXPECTED_ERROR_PATTERNS");
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
            "duplicate recursive_types error-pattern metadata for {case_id}"
        );
    }

    entries
}

fn parse_expected_case_metadata(file: &syn::File) -> Vec<ExpectedCase> {
    let array = referenced_array_const(file, "RECURSIVE_TYPES_RS_EXPECTED_CASES");
    let mut error_patterns = error_pattern_entries(file);
    let mut seen = BTreeSet::new();

    let entries = array
        .elems
        .iter()
        .map(|entry| {
            let syn::Expr::Tuple(tuple) = entry else {
                panic!("expected tuple recursive_types metadata entry");
            };
            assert_eq!(
                tuple.elems.len(),
                4,
                "metadata entries should have case, upstream case, status, and min obligations"
            );
            let case = literal_string(&tuple.elems[0]);
            assert!(
                seen.insert(case.clone()),
                "recursive_types metadata should not duplicate case {case}"
            );
            let expected_error_patterns = error_patterns.remove(&case).unwrap_or_default();
            ExpectedCase {
                case,
                upstream_case: literal_string(&tuple.elems[1]),
                status: literal_string(&tuple.elems[2]),
                min_obligations: literal_usize(&tuple.elems[3]),
                expected_error_patterns,
            }
        })
        .collect::<Vec<_>>();

    assert!(
        error_patterns.is_empty(),
        "error-pattern metadata should not contain orphan cases: {error_patterns:?}"
    );
    entries
}

fn expected_metadata_from_tests() -> Vec<ExpectedCase> {
    let mut error_patterns = ERROR_FRAGMENT_METADATA
        .iter()
        .map(|(case, patterns)| {
            (
                *case,
                patterns
                    .iter()
                    .map(|pattern| (*pattern).to_string())
                    .collect::<Vec<_>>(),
            )
        })
        .collect::<BTreeMap<_, _>>();

    EXPECTED_CASE_METADATA
        .iter()
        .map(
            |(case, upstream_case, status, min_obligations)| ExpectedCase {
                case: (*case).to_string(),
                upstream_case: (*upstream_case).to_string(),
                status: (*status).to_string(),
                min_obligations: *min_obligations,
                expected_error_patterns: error_patterns.remove(case).unwrap_or_default(),
            },
        )
        .collect()
}

#[allow(dead_code)]
fn manifest_expected_metadata() -> Vec<ExpectedCase> {
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
                == Some("source/rust_verify_test/tests/recursive_types.rs")
        })
        .expect("Verus manifest should contain recursive_types.rs row");

    row["expected_cases"]
        .as_array()
        .expect("recursive_types.rs row should contain expected_cases")
        .iter()
        .map(|case| ExpectedCase {
            case: case["case_id"]
                .as_str()
                .expect("manifest case should contain case_id")
                .to_string(),
            upstream_case: case
                .get("upstream_case_id")
                .and_then(serde_json::Value::as_str)
                .unwrap_or("")
                .to_string(),
            status: case["expected_verdict"]
                .as_str()
                .expect("manifest case should contain expected_verdict")
                .to_string(),
            min_obligations: case["min_obligations"]
                .as_u64()
                .expect("manifest case should contain min_obligations")
                .try_into()
                .expect("min_obligations should fit usize"),
            expected_error_patterns: case
                .get("expected_error_patterns")
                .and_then(serde_json::Value::as_array)
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

fn error_fragments(case: &str) -> Option<&'static [&'static str]> {
    ERROR_FRAGMENT_METADATA
        .iter()
        .find_map(|(fragment_case, fragments)| (*fragment_case == case).then_some(*fragments))
}

const ERROR_FRAGMENT_METADATA: &[(&str, &[&str])] = &[
    (
        "recursive_type_reject_recursive_types_attr_currently_errors",
        &[
            "Unsupported nested struct item",
            "nested items are rejected",
        ],
    ),
    (
        "recursive_type_external_body_attr_currently_errors",
        &[
            "Unsupported nested struct item",
            "nested items are rejected",
        ],
    ),
    (
        "recursive_type_external_body_missing_reject_attr_currently_errors",
        &[
            "Unsupported nested struct item",
            "nested items are rejected",
        ],
    ),
    (
        "recursive_type_boxed_payload_local_inspector_currently_errors",
        &["Unsupported nested fn item", "nested items are rejected"],
    ),
    (
        "recursive_type_fnspec_positivity_diagnostic_currently_errors",
        &[
            "Unsupported nested struct item",
            "nested items are rejected",
        ],
    ),
];

const EXPECTED_CASE_METADATA: &[(&str, &str, &str, usize)] = &[
    (
        "recursive_enum_constructor_match_all_branches_safe",
        "",
        "verified",
        3,
    ),
    (
        "recursive_struct_wrapper_field_match_all_branches_safe",
        "",
        "verified",
        3,
    ),
    (
        "recursive_box_variant_constructor_smoke_safe",
        "",
        "verified",
        3,
    ),
    (
        "recursive_box_payload_opaque_transfer_verified",
        "",
        "verified",
        3,
    ),
    (
        "mutually_recursive_enum_constructor_match_all_branches_safe",
        "",
        "verified",
        3,
    ),
    (
        "recursive_type_decrease_adjacent_countdown_verified",
        "",
        "verified",
        1,
    ),
    (
        "recursive_enum_wrong_variant_counterexample",
        "",
        "counterexample",
        3,
    ),
    (
        "recursive_box_variant_wrong_outer_counterexample",
        "",
        "counterexample",
        3,
    ),
    (
        "recursive_struct_wrapper_wrong_field_counterexample",
        "",
        "counterexample",
        3,
    ),
    (
        "mutually_recursive_enum_wrong_variant_counterexample",
        "",
        "counterexample",
        3,
    ),
    (
        "recursive_type_decrease_adjacent_wrong_value_counterexample",
        "",
        "counterexample",
        1,
    ),
    (
        "recursive_type_reject_recursive_types_attr_currently_errors",
        "",
        "error",
        0,
    ),
    (
        "recursive_type_external_body_attr_currently_errors",
        "",
        "error",
        0,
    ),
    (
        "recursive_type_external_body_missing_reject_attr_currently_errors",
        "",
        "error",
        0,
    ),
    (
        "recursive_type_boxed_payload_local_inspector_currently_errors",
        "",
        "error",
        0,
    ),
    (
        "recursive_type_fnspec_positivity_diagnostic_currently_errors",
        "",
        "error",
        0,
    ),
];

#[test]
fn recursive_types_rs_port_file_is_rust_syntax() {
    let source = std::fs::read_to_string(recursive_types_port_path())
        .expect("recursive_types port should be readable");
    syn::parse_file(&source).expect("recursive_types port should parse as ordinary Rust syntax");
}

#[test]
fn recursive_types_rs_pinned_upstream_case_shapes_are_present() {
    let path = pinned_upstream_recursive_types_path();
    if !path.exists() {
        eprintln!(
            "skipping pinned upstream recursive_types.rs shape check; missing {}",
            path.display()
        );
        return;
    }

    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", path.display()));
    for expected in [
        "#[test] test1",
        "#[test] test2",
        "#[test] test3",
        "#[test] test4",
        "#[test] test1_ok",
        "#[test] test1_fails",
        "#[test] test2_ok",
        "#[test] test2_fails",
        "#[test] test3_ok",
        "#[test] test3_fails",
        "#[test] test5_ok",
        "#[test] test5_fails1",
        "#[test] test5_fails2",
        "#[test] test5_fails3",
        "#[test] lifetimes_no_positivity",
        "#[test] fnspec_positivity",
        "enum E1",
        "enum E2",
        "struct List<A>",
        "E(Box<E1>)",
        "E(Box<E2>)",
        "F(List<Box<E1>>)",
        "#[verifier::reject_recursive_types(A)]",
        "#[verifier(external_body)]",
        "#[verifier::accept_recursive_types(V)]",
        "struct Map<K, V>",
        "struct D<A, B>",
        "dummy: std::marker::PhantomData<(K, V)>",
        "in a non-positive position",
        "external_body datatype",
        "Type parameter A",
        "spec_fn(S) -> int",
    ] {
        assert!(
            source.contains(expected),
            "pinned upstream recursive_types.rs should still contain {expected}"
        );
    }
}

#[test]
fn recursive_types_rs_expected_case_metadata_is_schema_valid_and_exact() {
    let source = std::fs::read_to_string(recursive_types_port_path())
        .expect("recursive_types port should be readable");
    assert!(
        source.contains("UPSTREAM_RECURSIVE_TYPES_RS_PINNED_CASES")
            && source.contains("upstream_recursive_types_rs_pinned_cases"),
        "recursive_types port should expose pinned upstream case metadata"
    );
    assert!(
        source.contains("RECURSIVE_TYPES_RS_EXPECTED_CASES")
            && source.contains("recursive_types_rs_expected_cases")
            && source.contains("RECURSIVE_TYPES_RS_EXPECTED_ERROR_PATTERNS")
            && source.contains("recursive_types_rs_expected_error_patterns"),
        "recursive_types port should expose expected-case and error-pattern metadata"
    );

    let file = port_file();
    let actual = parse_expected_case_metadata(&file);
    let expected = expected_metadata_from_tests();
    assert_eq!(
        actual, expected,
        "recursive_types expected-case metadata should match the regression inventory"
    );

    let mut seen = BTreeSet::new();
    for expected in actual {
        assert!(
            seen.insert(expected.case.clone()),
            "recursive_types metadata should not duplicate case {}",
            expected.case
        );
        assert!(
            matches!(
                expected.status.as_str(),
                "verified" | "counterexample" | "error"
            ),
            "{} should use only verified/counterexample/error status, got {}",
            expected.case,
            expected.status
        );
        assert_ne!(
            expected.status.to_ascii_lowercase(),
            "unknown",
            "{} must not list Unknown as replacement evidence",
            expected.case
        );
        if expected.status == "error" {
            assert_eq!(
                expected.min_obligations, 0,
                "{} error metadata should declare zero obligations",
                expected.case
            );
            assert!(
                error_fragments(&expected.case).is_some(),
                "{} error metadata should have pinned diagnostic fragments",
                expected.case
            );
        } else {
            assert!(
                expected.min_obligations > 0,
                "{} non-error metadata should declare an obligation floor",
                expected.case
            );
            port_function(&file, &expected.case, &expected.upstream_case);
        }
    }
}

#[test]
fn recursive_types_rs_expected_case_metadata_matches_manifest() {
    assert_eq!(
        parse_expected_case_metadata(&port_file()),
        manifest_expected_metadata(),
        "recursive_types.rs manifest expected_cases should match port metadata and error patterns exactly"
    );
}

#[test]
fn recursive_types_rs_expected_cases_match_statuses_and_obligation_counts() {
    let path = recursive_types_port_path();
    let path = path
        .to_str()
        .expect("recursive_types port path should be UTF-8");

    for expected in parse_expected_case_metadata(&port_file()) {
        match expected.status.as_str() {
            "verified" | "counterexample" => {
                let (result, obligations) =
                    verify_case_with_obligations(&expected.case, &expected.upstream_case);
                reject_unknown(&result, &expected.case, &expected.upstream_case);
                assert!(
                    obligations >= expected.min_obligations,
                    "{} ({}) should collect at least {} obligation(s), got {}",
                    expected.case,
                    expected.upstream_case,
                    expected.min_obligations,
                    obligations
                );
                match expected.status.as_str() {
                    "verified" => assert!(
                        matches!(result, VerifyResult::Verified),
                        "{} ({}) should verify, got: {result:?}",
                        expected.case,
                        expected.upstream_case
                    ),
                    "counterexample" => assert!(
                        matches!(result, VerifyResult::Counterexample { .. }),
                        "{} ({}) should produce a counterexample, got: {result:?}",
                        expected.case,
                        expected.upstream_case
                    ),
                    _ => unreachable!(),
                }
            }
            "error" => {
                let expected_fragments = error_fragments(&expected.case).unwrap_or_else(|| {
                    panic!(
                        "{} ({}) should have expected diagnostic fragments",
                        expected.case, expected.upstream_case
                    )
                });
                let message = fail_closed_message(path, &expected.case, &expected.upstream_case);
                assert!(
                    expected_fragments
                        .iter()
                        .any(|expected_fragment| message.contains(expected_fragment)),
                    "{} ({}) error should contain one of {:?}, got: {message}",
                    expected.case,
                    expected.upstream_case,
                    expected_fragments
                );
            }
            other => panic!(
                "{} ({}) has unsupported expected status {other}",
                expected.case, expected.upstream_case
            ),
        }
    }
}
