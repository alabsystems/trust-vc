// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Executable guards for the expanded upstream proph.rs TrustVc scout slice.
//!
//! These tests intentionally keep `source/rust_verify_test/tests/proph.rs` as
//! an unsupported gap. They pin only stable verified surrogate cases, stable
//! counterexamples, and fail-closed prophecy/proph/future/resolvedness
//! boundaries. Solver `Unknown` outcomes are not accepted as evidence.

mod common;

use std::{
    collections::{BTreeMap, BTreeSet},
    path::{Path, PathBuf},
};
use trust_vc_core::{
    extract_verification_conditions_with_file_context, verify_function_from_file, VerifyResult,
};

fn proph_port_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/ported/proph.rs")
}

fn pinned_upstream_proph_path() -> PathBuf {
    common::pinned_verus_test_path("proph.rs")
}

fn verus_manifest_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/verus-tests.json")
}

fn port_file() -> syn::File {
    let source = std::fs::read_to_string(proph_port_path()).expect("proph port should be readable");
    syn::parse_file(&source).expect("proph port should parse as ordinary Rust syntax")
}

fn port_function<'a>(file: &'a syn::File, case: &str, upstream_case: &str) -> &'a syn::ItemFn {
    file.items
        .iter()
        .find_map(|item| match item {
            syn::Item::Fn(function) if function.sig.ident == case => Some(function),
            _ => None,
        })
        .unwrap_or_else(|| panic!("{case} ({upstream_case}) should exist in proph port"))
}

fn verify_case(path: &Path, case: &str, upstream_case: &str) -> (VerifyResult, usize) {
    let path = path.to_str().expect("proph port path should be UTF-8");
    let result = verify_function_from_file(path, case)
        .unwrap_or_else(|err| panic!("{case} ({upstream_case}) should extract: {err}"));

    if let VerifyResult::Unknown { reason, .. } = &result {
        panic!(
            "{case} ({upstream_case}) returned solver Unknown, which is not stable evidence: {reason}"
        );
    }

    let file = port_file();
    let function = port_function(&file, case, upstream_case);
    let vc = extract_verification_conditions_with_file_context(&file, function)
        .unwrap_or_else(|err| panic!("{case} ({upstream_case}) should extract VCs: {err}"));

    (result, vc.obligations().len())
}

fn expect_fail_closed(path: &Path, case: &str, upstream_case: &str, expected_fragments: &[&str]) {
    let path = path.to_str().expect("proph port path should be UTF-8");
    let message = match verify_function_from_file(path, case) {
        Err(err) => err.to_string(),
        Ok(VerifyResult::Error { message }) => message,
        Ok(VerifyResult::Unknown { reason, .. }) => {
            panic!("{case} ({upstream_case}) returned solver Unknown, which is not stable evidence: {reason}")
        }
        Ok(result) => {
            panic!("{case} ({upstream_case}) should fail closed with Error, got: {result:?}")
        }
    };

    assert!(
        expected_fragments
            .iter()
            .any(|expected_fragment| message.contains(expected_fragment)),
        "{case} ({upstream_case}) error should contain one of {expected_fragments:?}, got: {message}"
    );
}

fn literal_string(expr: &syn::Expr) -> String {
    match expr {
        syn::Expr::Lit(syn::ExprLit {
            lit: syn::Lit::Str(lit),
            ..
        }) => lit.value(),
        _ => panic!("expected string literal in metadata"),
    }
}

fn literal_usize(expr: &syn::Expr) -> usize {
    match expr {
        syn::Expr::Lit(syn::ExprLit {
            lit: syn::Lit::Int(lit),
            ..
        }) => lit
            .base10_parse::<usize>()
            .unwrap_or_else(|err| panic!("expected usize literal in metadata: {err}")),
        _ => panic!("expected usize literal in metadata"),
    }
}

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
        .unwrap_or_else(|| panic!("proph port should define {const_name}"));

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
    let array = referenced_array_const(file, "PROPH_RS_EXPECTED_ERROR_PATTERNS");
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
            "duplicate proph error-pattern metadata for {case_id}"
        );
    }

    entries
}

fn parse_expected_case_metadata(file: &syn::File) -> Vec<CaseMetadata> {
    let array = referenced_array_const(file, "PROPH_RS_EXPECTED_CASES");
    let mut error_patterns = error_pattern_entries(file);
    let mut seen = BTreeSet::new();

    let entries = array
        .elems
        .iter()
        .map(|entry| {
            let syn::Expr::Tuple(tuple) = entry else {
                panic!("expected tuple metadata entry");
            };
            assert_eq!(
                tuple.elems.len(),
                4,
                "metadata entries should have case, upstream case, status, and min obligations"
            );
            let case_id = literal_string(&tuple.elems[0]);
            assert!(
                seen.insert(case_id.clone()),
                "duplicate proph metadata for {case_id}"
            );
            let expected_error_patterns = error_patterns.remove(&case_id).unwrap_or_default();
            CaseMetadata {
                case_id,
                upstream_case_id: literal_string(&tuple.elems[1]),
                expected_verdict: literal_string(&tuple.elems[2]),
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

fn expected_metadata_from_tests() -> Vec<CaseMetadata> {
    let mut error_patterns = FAIL_CLOSED_CASES
        .iter()
        .map(|(case, _, patterns)| {
            (
                *case,
                patterns
                    .iter()
                    .map(|pattern| (*pattern).to_string())
                    .collect::<Vec<_>>(),
            )
        })
        .collect::<BTreeMap<_, _>>();
    let mut metadata = Vec::new();
    for (case, upstream_case, min_obligations) in VERIFIED_CASES {
        metadata.push(CaseMetadata {
            case_id: (*case).to_string(),
            upstream_case_id: (*upstream_case).to_string(),
            expected_verdict: "verified".to_string(),
            min_obligations: *min_obligations,
            expected_error_patterns: Vec::new(),
        });
    }
    for (case, upstream_case, min_obligations) in COUNTEREXAMPLE_CASES {
        metadata.push(CaseMetadata {
            case_id: (*case).to_string(),
            upstream_case_id: (*upstream_case).to_string(),
            expected_verdict: "counterexample".to_string(),
            min_obligations: *min_obligations,
            expected_error_patterns: Vec::new(),
        });
    }
    for (case, upstream_case, _) in FAIL_CLOSED_CASES {
        metadata.push(CaseMetadata {
            case_id: (*case).to_string(),
            upstream_case_id: (*upstream_case).to_string(),
            expected_verdict: "error".to_string(),
            min_obligations: 0,
            expected_error_patterns: error_patterns.remove(case).unwrap_or_default(),
        });
    }
    assert!(
        error_patterns.is_empty(),
        "expected error-pattern inventory should not contain orphan cases: {error_patterns:?}"
    );
    metadata.sort_by(|left, right| left.case_id.cmp(&right.case_id));
    metadata
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
            entry["upstream_path"].as_str() == Some("source/rust_verify_test/tests/proph.rs")
        })
        .expect("Verus manifest should contain proph.rs row");

    let mut metadata = row["expected_cases"]
        .as_array()
        .expect("proph.rs row should contain expected_cases")
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
        .collect::<Vec<_>>();
    metadata.sort_by(|left, right| left.case_id.cmp(&right.case_id));
    metadata
}

fn collect_port_function_names(file: &syn::File) -> Vec<String> {
    let mut names = Vec::new();
    for item in &file.items {
        if let syn::Item::Fn(function) = item {
            let name = function.sig.ident.to_string();
            if !HELPER_FUNCTIONS.contains(&name.as_str()) {
                names.push(name);
            }
        }
    }
    names.sort();
    names
}

const HELPER_FUNCTIONS: &[&str] = &[
    "proph_bool_resolution_boundary",
    "proph_rs_expected_cases",
    "proph_rs_expected_error_patterns",
];

const VERIFIED_CASES: &[(&str, &str, usize)] = &[
    (
        "proph_bool_resolution_boundary_true_verified",
        "prophecy_expected_use_3",
        2,
    ),
    (
        "proph_bool_resolution_boundary_false_verified",
        "prophecy_expected_use_3",
        2,
    ),
    (
        "proph_branch_on_resolved_bool_surrogate_verified",
        "prophecy_expected_use_1",
        2,
    ),
    (
        "proph_struct_payload_resolution_surrogate_verified",
        "prophecy_expected_use_2",
        4,
    ),
];

const COUNTEREXAMPLE_CASES: &[(&str, &str, usize)] = &[
    (
        "proph_bool_resolution_boundary_wrong_value_counterexample",
        "prophecy_expected_use_3",
        1,
    ),
    (
        "proph_branch_wrong_future_value_counterexample",
        "prophecy_expected_use_1",
        1,
    ),
    (
        "proph_struct_payload_wrong_field_counterexample",
        "prophecy_expected_use_2",
        1,
    ),
    (
        "proph_ghost_payload_wrong_view_counterexample",
        "prophecy_ghost_disallowed",
        1,
    ),
];

const FAIL_CLOSED_CASES: &[(&str, &str, &[&str])] = &[
    (
        "prophecy_api_surface_currently_blocked",
        "",
        &[
            "Prophecy",
            "unknown return type",
            "unresolved",
            "view",
            "resolve",
        ],
    ),
    (
        "proph_bool_view_assert_currently_blocked",
        "prophecy_expected_use_3",
        &["unresolved variable `p`"],
    ),
    (
        "proph_bool_view_binding_currently_blocked",
        "prophecy_expected_use_1",
        &["collection operation 'view' requires a collection receiver"],
    ),
    (
        "proph_struct_payload_view_currently_blocked",
        "prophecy_expected_use_2",
        &["collection operation 'view' requires a collection receiver"],
    ),
    (
        "proph_future_snapshot_currently_blocked",
        "",
        &["future", "unresolved"],
    ),
    (
        "proph_resolvedness_query_currently_blocked",
        "",
        &["is_resolved", "method", "unsupported", "unresolved"],
    ),
    (
        "proph_double_resolve_currently_blocked",
        "",
        &["unresolved variable `p`", "view", "resolve"],
    ),
    (
        "proph_ghost_payload_surface_currently_blocked",
        "prophecy_ghost_disallowed",
        &["Ghost", "view", "unresolved"],
    ),
];

#[test]
fn proph_rs_port_file_is_rust_syntax() {
    let source = std::fs::read_to_string(proph_port_path()).expect("proph port should be readable");
    syn::parse_file(&source).expect("proph port should parse as ordinary Rust syntax");
}

#[test]
fn proph_rs_pinned_upstream_case_shapes_are_present() {
    let path = pinned_upstream_proph_path();
    if !path.exists() {
        eprintln!(
            "skipping pinned upstream proph.rs shape check; missing {}",
            path.display()
        );
        return;
    }

    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", path.display()));
    for expected in [
        "#[test] prophecy_expected_use_1",
        "#[test] prophecy_expected_use_2",
        "#[test] prophecy_expected_use_3",
        "#[test] prophecy_ghost_disallowed",
        "use vstd::proph::*",
        "let p = Prophecy::<bool>::new()",
        "if p@",
        "p.resolve(&true)",
        "assert(x == 2)",
        "#[derive(PartialEq, Eq, Structural)]",
        "struct S",
        "p.resolve(&S{a: 1u64, b: 2u8, c: false})",
        "assert(p@ == S{a: 1u64, b: 2u8, c: false})",
        "Prophecy::<Ghost<bool>>::new()",
        "p.resolve(&Ghost(!p.view().view()))",
        "trait bounds were not satisfied",
    ] {
        assert!(
            source.contains(expected),
            "pinned upstream proph.rs should still contain {expected}"
        );
    }

    assert_eq!(
        source.matches("#[test] prophecy_expected_use_").count(),
        3,
        "pinned upstream proph.rs should still expose exactly three expected-use tests"
    );
    assert_eq!(
        source.matches("#[test] prophecy_ghost_disallowed").count(),
        1,
        "pinned upstream proph.rs should still expose one Ghost payload rejection"
    );
}

#[test]
fn proph_rs_expected_case_metadata_is_complete_and_excludes_unknown() {
    let file = port_file();
    let mut actual = parse_expected_case_metadata(&file);
    actual.sort_by(|left, right| left.case_id.cmp(&right.case_id));

    let expected = expected_metadata_from_tests();

    assert_eq!(actual, expected);
    assert!(
        actual
            .iter()
            .all(|case| case.expected_verdict != "unknown" && case.expected_verdict != "Unknown"),
        "proph metadata must not accept Unknown as evidence"
    );
}

#[test]
fn proph_rs_expected_case_metadata_matches_manifest() {
    let mut actual = parse_expected_case_metadata(&port_file());
    actual.sort_by(|left, right| left.case_id.cmp(&right.case_id));
    assert_eq!(
        actual,
        manifest_expected_metadata(),
        "proph.rs manifest expected_cases should match port metadata and error patterns exactly"
    );
}

#[test]
fn proph_rs_port_inventory_stays_intentional() {
    let file = port_file();
    let observed = collect_port_function_names(&file);
    let mut expected: Vec<String> = expected_metadata_from_tests()
        .into_iter()
        .map(|case| case.case_id)
        .collect();
    expected.sort();

    assert_eq!(observed, expected);
}

#[test]
fn proph_rs_verified_subset_verifies_from_file() {
    let path = proph_port_path();

    for (case, upstream_case, min_obligations) in VERIFIED_CASES {
        let (result, obligations) = verify_case(&path, case, upstream_case);
        assert!(
            matches!(result, VerifyResult::Verified),
            "{case} ({upstream_case}) should verify, got: {result:?}"
        );
        assert!(
            obligations >= *min_obligations,
            "{case} ({upstream_case}) should expose at least {min_obligations} obligations, got {obligations}"
        );
    }
}

#[test]
fn proph_rs_counterexample_subset_is_rejected_from_file() {
    let path = proph_port_path();

    for (case, upstream_case, min_obligations) in COUNTEREXAMPLE_CASES {
        let (result, obligations) = verify_case(&path, case, upstream_case);
        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "{case} ({upstream_case}) should be rejected, got: {result:?}"
        );
        assert!(
            obligations >= *min_obligations,
            "{case} ({upstream_case}) should expose at least {min_obligations} obligations, got {obligations}"
        );
    }
}

#[test]
fn proph_rs_unsupported_boundaries_fail_closed_from_file() {
    let path = proph_port_path();

    for (case, upstream_case, expected_fragments) in FAIL_CLOSED_CASES {
        expect_fail_closed(&path, case, upstream_case, expected_fragments);
    }
}
