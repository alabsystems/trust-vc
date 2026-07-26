// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Executable guards for the upstream marker_traits.rs TrustVc scout slice.
//!
//! These tests intentionally keep `source/rust_verify_test/tests/marker_traits.rs`
//! fail-closed in the manifest. They prove only the Rust-valid subset TrustVc can
//! express today: extraction preserves marker trait bounds, bounded identities
//! verify, a concrete derived-Copy caller verifies through a generic Copy-bound
//! helper, bad bounded bodies are rejected, unsupported upstream-shaped marker
//! wrapper/object/variance surfaces fail closed, and Copy-bound const-generic
//! array shapes still report a stable extraction error.

use quote::ToTokens;
use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};
use trust_vc_core::{
    extract_verification_conditions_with_file_context, verify_function_from_file, VerifyResult,
};

const EXPECTED_CASE_METADATA: &[(&str, &str, &str, usize)] = &[
    (
        "copy_bound_identity_verified",
        "check_not_copy",
        "verified",
        1,
    ),
    (
        "send_sync_where_bound_identity_verified",
        "check_send_sync",
        "verified",
        1,
    ),
    ("send_bound_identity_verified", "check_send", "verified", 1),
    ("sync_bound_identity_verified", "check_sync", "verified", 1),
    (
        "copy_send_sync_bound_identity_verified",
        "check_send_sync",
        "verified",
        1,
    ),
    (
        "concrete_copy_witness_caller_verified",
        "check_not_copy",
        "verified",
        1,
    ),
    (
        "concrete_send_witness_caller_verified",
        "check_send",
        "verified",
        1,
    ),
    (
        "concrete_sync_witness_caller_verified",
        "check_sync",
        "verified",
        1,
    ),
    (
        "concrete_send_sync_witness_caller_verified",
        "check_send_sync",
        "verified",
        1,
    ),
    (
        "shared_reference_lifetime_identity_verified",
        "",
        "verified",
        1,
    ),
    (
        "copy_bound_false_assert_counterexample",
        "check_not_copy",
        "counterexample",
        1,
    ),
    (
        "send_bound_false_assert_counterexample",
        "check_send",
        "counterexample",
        1,
    ),
    (
        "sync_bound_false_assert_counterexample",
        "check_sync",
        "counterexample",
        1,
    ),
    (
        "send_sync_bound_false_assert_counterexample",
        "check_send_sync",
        "counterexample",
        1,
    ),
    (
        "copy_send_sync_bound_false_assert_counterexample",
        "check_send_sync",
        "counterexample",
        1,
    ),
    (
        "copy_bound_const_generic_array_currently_errors",
        "",
        "error",
        0,
    ),
    (
        "rust_moved_value_marker_diagnostic_text_currently_errors",
        "",
        "error",
        0,
    ),
    (
        "rust_send_sync_marker_diagnostic_text_currently_errors",
        "",
        "error",
        0,
    ),
    (
        "verus_variance_lifetime_marker_diagnostic_text_currently_errors",
        "",
        "error",
        0,
    ),
];

const EXPECTED_ERROR_FRAGMENTS: &[(&str, &[&str])] = &[
    (
        "copy_bound_const_generic_array_currently_errors",
        &["unsupported const-generic array length"],
    ),
    (
        "rust_moved_value_marker_diagnostic_text_currently_errors",
        &["Unsupported debug_assert!()"],
    ),
    (
        "rust_send_sync_marker_diagnostic_text_currently_errors",
        &["Unsupported debug_assert!()"],
    ),
    (
        "verus_variance_lifetime_marker_diagnostic_text_currently_errors",
        &["Unsupported debug_assert!()"],
    ),
];

const FAIL_CLOSED_FRAGMENTS: &[(&str, &str, &[&str])] = &[
    (
        "vstd_raw_ptr_points_to_send_sync_currently_errors",
        "raw_ptr_points_to_send_sync",
        &["unrecognized types", "vstd::raw_ptr::PointsTo<T>"],
    ),
    (
        "vstd_raw_ptr_points_to_send_currently_errors",
        "raw_ptr_points_to_send",
        &["unrecognized types", "vstd::raw_ptr::PointsTo<T>"],
    ),
    (
        "vstd_raw_ptr_points_to_sync_currently_errors",
        "raw_ptr_points_to_sync",
        &["unrecognized types", "vstd::raw_ptr::PointsTo<T>"],
    ),
    (
        "vstd_cell_points_to_send_sync_currently_errors",
        "cell_points_to_send_sync",
        &["unrecognized types", "vstd::cell::PointsTo<T>"],
    ),
    (
        "vstd_cell_points_to_send_currently_errors",
        "cell_points_to_send",
        &["unrecognized types", "vstd::cell::PointsTo<T>"],
    ),
    (
        "vstd_cell_points_to_sync_currently_errors",
        "cell_points_to_sync",
        &["unrecognized types", "vstd::cell::PointsTo<T>"],
    ),
    (
        "vstd_cell_pcell_send_sync_currently_errors",
        "pcell",
        &["unrecognized types", "vstd::cell::pcell::PCell<T>"],
    ),
    (
        "vstd_tracked_marker_wrapper_currently_errors",
        "trk_sync",
        &["unrecognized types", "vstd::prelude::Tracked<T>"],
    ),
    (
        "vstd_ghost_marker_wrapper_currently_errors",
        "gho",
        &["unrecognized types", "vstd::prelude::Ghost<T>"],
    ),
    (
        "vstd_local_invariant_marker_wrapper_currently_errors",
        "local_send",
        &["unrecognized types", "LocalInvariant"],
    ),
    (
        "vstd_atomic_invariant_marker_wrapper_currently_errors",
        "atomic_send",
        &["unrecognized types", "AtomicInvariant"],
    ),
    (
        "vstd_atomic_invariant_send_sync_currently_errors",
        "atomic_send_sync",
        &["unrecognized types", "AtomicInvariant"],
    ),
    (
        "copy_bound_const_generic_array_currently_errors",
        "check_not_copy const-generic array boundary",
        &["unsupported const-generic array length"],
    ),
    (
        "dyn_send_marker_trait_object_currently_errors",
        "Send marker-trait object boundary",
        &["unrecognized types", "dyn"],
    ),
    (
        "dyn_send_sync_marker_trait_object_currently_errors",
        "Send + Sync marker-trait object boundary",
        &["unrecognized types", "dyn"],
    ),
    (
        "vstd_tracked_covariant_shape_currently_errors",
        "trk_covariant",
        &["unrecognized types", "vstd::prelude::Tracked"],
    ),
    (
        "vstd_ghost_covariant_shape_currently_errors",
        "gho_covariant",
        &["unrecognized types", "vstd::prelude::Ghost"],
    ),
    (
        "vstd_local_invariant_variance_shape_currently_errors",
        "local_invariant/local_invariant2",
        &["unrecognized types", "LocalInvariant"],
    ),
    (
        "vstd_atomic_invariant_variance_shape_currently_errors",
        "atomic_invariant/atomic_invariant2",
        &["unrecognized types", "AtomicInvariant"],
    ),
    (
        "rust_moved_value_marker_diagnostic_text_currently_errors",
        "check_not_copy exact Rust diagnostic text boundary",
        &["Unsupported debug_assert!()"],
    ),
    (
        "rust_send_sync_marker_diagnostic_text_currently_errors",
        "check_send/check_sync exact Rust diagnostic text boundary",
        &["Unsupported debug_assert!()"],
    ),
    (
        "verus_variance_lifetime_marker_diagnostic_text_currently_errors",
        "check_covariant/check_invariant exact Verus diagnostic text boundary",
        &["Unsupported debug_assert!()"],
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

fn marker_traits_port_path() -> PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../evals/verus/ported/marker_traits.rs")
}

fn verus_manifest_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/verus-tests.json")
}

fn marker_traits_port_source() -> String {
    let path = marker_traits_port_path();
    std::fs::read_to_string(&path)
        .unwrap_or_else(|err| panic!("marker_traits port should read: {err}"))
}

fn parse_marker_traits_port() -> syn::File {
    let source = marker_traits_port_source();
    syn::parse_file(&source).unwrap_or_else(|err| panic!("marker_traits port should parse: {err}"))
}

fn port_function(case: &str) -> syn::ItemFn {
    let file = parse_marker_traits_port();
    file.items
        .iter()
        .find_map(|item| match item {
            syn::Item::Fn(function) if function.sig.ident == case => Some(function.clone()),
            _ => None,
        })
        .unwrap_or_else(|| panic!("{case} should exist in marker_traits port"))
}

fn string_lit(expr: &syn::Expr) -> String {
    match expr {
        syn::Expr::Lit(syn::ExprLit {
            lit: syn::Lit::Str(lit),
            ..
        }) => lit.value(),
        _ => panic!("expected string literal in marker_traits expected-case metadata"),
    }
}

fn usize_lit(expr: &syn::Expr) -> usize {
    match expr {
        syn::Expr::Lit(syn::ExprLit {
            lit: syn::Lit::Int(lit),
            ..
        }) => lit.base10_parse().unwrap_or_else(|err| {
            panic!("expected usize literal in marker_traits metadata: {err}")
        }),
        _ => panic!("expected usize literal in marker_traits expected-case metadata"),
    }
}

fn parse_expected_case_metadata() -> Vec<(String, String, String, usize)> {
    let file = parse_marker_traits_port();
    let expected_cases_expr = file
        .items
        .iter()
        .find_map(|item| match item {
            syn::Item::Const(item) if item.ident == "MARKER_TRAITS_RS_EXPECTED_CASES" => {
                Some(&*item.expr)
            }
            _ => None,
        })
        .unwrap_or_else(|| panic!("MARKER_TRAITS_RS_EXPECTED_CASES should exist"));

    let syn::Expr::Reference(reference) = expected_cases_expr else {
        panic!("MARKER_TRAITS_RS_EXPECTED_CASES should be a borrowed array");
    };
    let syn::Expr::Array(array) = &*reference.expr else {
        panic!("MARKER_TRAITS_RS_EXPECTED_CASES should be a borrowed array");
    };

    array
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
            (
                string_lit(&tuple.elems[0]),
                string_lit(&tuple.elems[1]),
                string_lit(&tuple.elems[2]),
                usize_lit(&tuple.elems[3]),
            )
        })
        .collect()
}

fn expected_case_metadata() -> Vec<(String, String, String, usize)> {
    EXPECTED_CASE_METADATA
        .iter()
        .map(|(case, upstream_case, status, min_obligations)| {
            (
                (*case).to_string(),
                (*upstream_case).to_string(),
                (*status).to_string(),
                *min_obligations,
            )
        })
        .collect()
}

fn expected_metadata() -> Vec<CaseMetadata> {
    let mut error_patterns = EXPECTED_ERROR_FRAGMENTS
        .iter()
        .map(|(case_id, patterns)| {
            (
                *case_id,
                patterns
                    .iter()
                    .map(|pattern| (*pattern).to_string())
                    .collect::<Vec<_>>(),
            )
        })
        .collect::<BTreeMap<_, _>>();

    let entries = EXPECTED_CASE_METADATA
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
        .collect::<Vec<_>>();

    assert!(
        error_patterns.is_empty(),
        "expected error fragments should not contain orphan cases: {error_patterns:?}"
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
            entry["upstream_path"].as_str()
                == Some("source/rust_verify_test/tests/marker_traits.rs")
        })
        .expect("Verus manifest should contain marker_traits.rs row");

    row["expected_cases"]
        .as_array()
        .expect("marker_traits.rs row should contain expected_cases")
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
        .collect()
}

fn verify_case(path: &str, case: &str, upstream_case: &str) -> VerifyResult {
    verify_function_from_file(path, case)
        .unwrap_or_else(|err| panic!("{case} ({upstream_case}) should extract: {err}"))
}

fn verify_case_with_obligation_count(case: &str, upstream_case: &str) -> (VerifyResult, usize) {
    let file = parse_marker_traits_port();
    let function = file
        .items
        .iter()
        .find_map(|item| match item {
            syn::Item::Fn(function) if function.sig.ident == case => Some(function),
            _ => None,
        })
        .unwrap_or_else(|| panic!("{case} should exist in marker_traits port"));

    let vc = extract_verification_conditions_with_file_context(&file, function)
        .unwrap_or_else(|err| panic!("{case} ({upstream_case}) should extract: {err}"));
    let obligation_count = vc.obligations().len();
    (vc.verify(), obligation_count)
}

fn trait_bounds_for_case(case: &str) -> Vec<(String, String)> {
    let file = parse_marker_traits_port();
    let function = file
        .items
        .iter()
        .find_map(|item| match item {
            syn::Item::Fn(function) if function.sig.ident == case => Some(function),
            _ => None,
        })
        .unwrap_or_else(|| panic!("{case} should exist in marker_traits port"));

    let vc = extract_verification_conditions_with_file_context(&file, function)
        .unwrap_or_else(|err| panic!("{case} should extract: {err}"));
    let context = vc
        .function_context()
        .unwrap_or_else(|| panic!("{case} should record a function context for marker bounds"));

    context
        .trait_bounds()
        .iter()
        .map(|bound| (bound.type_param.clone(), bound.trait_name.clone()))
        .collect()
}

fn compact_tokens(tokens: impl ToTokens) -> String {
    let mut rendered = tokens.to_token_stream().to_string();
    for (from, to) in [
        (" :: ", "::"),
        (" < ", "<"),
        (" >", ">"),
        (" ,", ","),
        (", ", ","),
        ("& ", "&"),
        (" + ", "+"),
        ("dyn ", "dyn"),
    ] {
        rendered = rendered.replace(from, to);
    }
    rendered
}

fn signature_type_tokens_for_case(case: &str) -> (Vec<String>, Option<String>) {
    let function = port_function(case);
    let inputs = function
        .sig
        .inputs
        .iter()
        .filter_map(|input| match input {
            syn::FnArg::Typed(pat_type) => Some(compact_tokens(&pat_type.ty)),
            syn::FnArg::Receiver(_) => None,
        })
        .collect();
    let output = match &function.sig.output {
        syn::ReturnType::Type(_, ty) => Some(compact_tokens(ty)),
        syn::ReturnType::Default => None,
    };

    (inputs, output)
}

fn assert_message_contains_all(case: &str, upstream_case: &str, message: &str, fragments: &[&str]) {
    for expected_fragment in fragments {
        assert!(
            message.contains(expected_fragment),
            "{case} ({upstream_case}) message should contain {expected_fragment:?}, got: {message}"
        );
    }
}

fn expected_error_fragments(case: &str) -> &'static [&'static str] {
    EXPECTED_ERROR_FRAGMENTS
        .iter()
        .find_map(|(fragment_case, fragments)| (*fragment_case == case).then_some(*fragments))
        .unwrap_or_else(|| panic!("{case} should have pinned expected-error fragments"))
}

fn expect_error(path: &str, case: &str, upstream_case: &str, expected_fragments: &[&str]) {
    let message = match verify_function_from_file(path, case) {
        Ok(VerifyResult::Error { message }) => message,
        Ok(result) => panic!("{case} ({upstream_case}) should error, got: {result:?}"),
        Err(err) => err.to_string(),
    };

    assert_message_contains_all(case, upstream_case, &message, expected_fragments);
}

fn expect_fail_closed(path: &str, case: &str, upstream_case: &str, expected_fragments: &[&str]) {
    let message = match verify_function_from_file(path, case) {
        Ok(VerifyResult::Error { message }) => message,
        Ok(VerifyResult::Unknown { reason, .. }) => reason,
        Ok(result) => panic!("{case} ({upstream_case}) should fail closed, got: {result:?}"),
        Err(err) => err.to_string(),
    };

    assert_message_contains_all(case, upstream_case, &message, expected_fragments);
}

#[test]
fn marker_traits_rs_expected_case_metadata_is_schema_valid_and_exact() {
    let source = marker_traits_port_source();
    assert!(
        source.contains("MARKER_TRAITS_RS_EXPECTED_CASES")
            && source.contains("marker_traits_rs_expected_cases")
            && source.contains("MARKER_TRAITS_RS_EXPECTED_ERROR_PATTERNS")
            && source.contains("marker_traits_rs_expected_error_patterns"),
        "marker_traits port should expose manifest-ready expected-case and error-pattern metadata helpers"
    );

    let actual = parse_expected_case_metadata();
    assert_eq!(
        actual,
        expected_case_metadata(),
        "marker_traits port metadata should exactly match the regression inventory"
    );

    let mut seen = BTreeSet::new();
    let mut statuses = BTreeSet::new();
    for (case, upstream_case, status, min_obligations) in &actual {
        assert!(
            seen.insert(case.clone()),
            "marker_traits expected-case metadata should not duplicate {case}"
        );
        statuses.insert(status.clone());
        assert!(
            matches!(status.as_str(), "verified" | "counterexample" | "error"),
            "{case} ({upstream_case}) should use a schema-valid status, got {status}"
        );
        assert!(
            !status.eq_ignore_ascii_case("unknown"),
            "{case} ({upstream_case}) must not inventory Unknown as evidence"
        );
        let function = port_function(case);
        assert_eq!(function.sig.ident, case);
        if status == "error" {
            assert_eq!(
                *min_obligations, 0,
                "{case} ({upstream_case}) error metadata should not count obligations"
            );
            assert!(
                EXPECTED_ERROR_FRAGMENTS
                    .iter()
                    .any(|(fragment_case, _)| fragment_case == case),
                "{case} ({upstream_case}) error metadata should have pinned diagnostic fragments"
            );
        } else {
            assert!(
                *min_obligations > 0,
                "{case} ({upstream_case}) non-error metadata should declare an obligation floor"
            );
        }
    }

    for required_status in ["verified", "counterexample", "error"] {
        assert!(
            statuses.contains(required_status),
            "marker_traits metadata should include at least one {required_status} expected case"
        );
    }

    for (case, _, _) in FAIL_CLOSED_FRAGMENTS {
        if !EXPECTED_CASE_METADATA
            .iter()
            .any(|(expected_case, _, _, _)| expected_case == case)
        {
            assert!(
                !actual.iter().any(|(actual_case, _, _, _)| actual_case == case),
                "{case} currently returns fail-closed Unknown/OpaqueTypes and must not be claimed as expected-case evidence"
            );
        }
    }
}

#[test]
fn marker_traits_rs_expected_case_metadata_matches_manifest() {
    assert_eq!(
        expected_metadata(),
        manifest_expected_metadata(),
        "marker_traits.rs manifest expected_cases should match regression metadata and error fragments exactly"
    );
}

#[test]
fn marker_traits_rs_exact_upstream_diagnostic_text_stays_fail_closed() {
    let source = marker_traits_port_source();
    for diagnostic in [
        "use of moved value",
        "between threads safely",
        "lifetime may not live long enough",
    ] {
        assert!(
            source.contains(diagnostic),
            "marker_traits diagnostic boundary should pin upstream diagnostic text {diagnostic:?}"
        );
    }
}

#[test]
fn marker_traits_rs_marker_bounds_are_preserved_in_function_context() {
    for (case, expected) in [
        (
            "copy_bound_identity_verified",
            vec![("T".to_string(), "Copy".to_string())],
        ),
        (
            "send_sync_where_bound_identity_verified",
            vec![
                ("T".to_string(), "Send".to_string()),
                ("T".to_string(), "Sync".to_string()),
            ],
        ),
        (
            "send_bound_identity_verified",
            vec![("T".to_string(), "Send".to_string())],
        ),
        (
            "sync_bound_identity_verified",
            vec![("T".to_string(), "Sync".to_string())],
        ),
        (
            "copy_send_sync_bound_identity_verified",
            vec![
                ("T".to_string(), "Copy".to_string()),
                ("T".to_string(), "Send".to_string()),
                ("T".to_string(), "Sync".to_string()),
            ],
        ),
        (
            "send_sync_bound_false_assert_counterexample",
            vec![
                ("T".to_string(), "Send".to_string()),
                ("T".to_string(), "Sync".to_string()),
            ],
        ),
        (
            "copy_send_sync_bound_false_assert_counterexample",
            vec![
                ("T".to_string(), "Copy".to_string()),
                ("T".to_string(), "Send".to_string()),
                ("T".to_string(), "Sync".to_string()),
            ],
        ),
        (
            "phantom_data_marker_bound_currently_errors",
            vec![("T".to_string(), "Copy".to_string())],
        ),
        (
            "vstd_raw_ptr_points_to_send_sync_currently_errors",
            vec![
                ("T".to_string(), "Send".to_string()),
                ("T".to_string(), "Sync".to_string()),
            ],
        ),
        (
            "vstd_raw_ptr_points_to_send_currently_errors",
            vec![("T".to_string(), "Send".to_string())],
        ),
        (
            "vstd_raw_ptr_points_to_sync_currently_errors",
            vec![("T".to_string(), "Sync".to_string())],
        ),
        (
            "vstd_cell_points_to_send_sync_currently_errors",
            vec![
                ("T".to_string(), "Send".to_string()),
                ("T".to_string(), "Sync".to_string()),
            ],
        ),
        (
            "vstd_cell_points_to_send_currently_errors",
            vec![("T".to_string(), "Send".to_string())],
        ),
        (
            "vstd_cell_points_to_sync_currently_errors",
            vec![("T".to_string(), "Sync".to_string())],
        ),
        (
            "vstd_cell_pcell_send_sync_currently_errors",
            vec![
                ("T".to_string(), "Send".to_string()),
                ("T".to_string(), "Sync".to_string()),
            ],
        ),
        (
            "vstd_tracked_marker_wrapper_currently_errors",
            vec![("T".to_string(), "Sync".to_string())],
        ),
        (
            "vstd_ghost_marker_wrapper_currently_errors",
            vec![
                ("T".to_string(), "Send".to_string()),
                ("T".to_string(), "Sync".to_string()),
            ],
        ),
        (
            "vstd_local_invariant_marker_wrapper_currently_errors",
            vec![("T".to_string(), "Send".to_string())],
        ),
        (
            "vstd_atomic_invariant_marker_wrapper_currently_errors",
            vec![("T".to_string(), "Send".to_string())],
        ),
        (
            "vstd_atomic_invariant_send_sync_currently_errors",
            vec![
                ("T".to_string(), "Send".to_string()),
                ("T".to_string(), "Sync".to_string()),
            ],
        ),
    ] {
        assert_eq!(
            trait_bounds_for_case(case),
            expected,
            "{case} should preserve marker bounds before verification or fail-closed rejection"
        );
    }
}

#[test]
fn marker_traits_rs_verified_subset_verifies_from_file() {
    for (case, upstream_case, status, min_obligations) in EXPECTED_CASE_METADATA
        .iter()
        .filter(|(_, _, status, _)| *status == "verified")
    {
        let (result, obligation_count) = verify_case_with_obligation_count(case, upstream_case);
        assert!(
            obligation_count >= *min_obligations,
            "{case} ({upstream_case}) should collect at least {min_obligations} obligation(s), got {obligation_count}"
        );
        assert!(
            matches!(result, VerifyResult::Verified),
            "{case} ({upstream_case}) should verify, got: {result:?}"
        );
        assert_eq!(*status, "verified");
    }
}

#[test]
fn marker_traits_rs_counterexample_subset_is_rejected_from_file() {
    let path = marker_traits_port_path();
    let path = path
        .to_str()
        .expect("marker_traits port path should be UTF-8");

    for (case, upstream_case, status, _) in EXPECTED_CASE_METADATA
        .iter()
        .filter(|(_, _, status, _)| *status == "counterexample")
    {
        let result = verify_case(path, case, upstream_case);
        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "{case} ({upstream_case}) should be rejected, got: {result:?}"
        );
        assert_eq!(*status, "counterexample");
    }
}

#[test]
fn marker_traits_rs_expected_error_cases_fail_closed_without_unknown_evidence() {
    let path = marker_traits_port_path();
    let path = path
        .to_str()
        .expect("marker_traits port path should be UTF-8");

    for (case, upstream_case, _status, min_obligations) in EXPECTED_CASE_METADATA
        .iter()
        .filter(|(_, _, status, _)| *status == "error")
    {
        assert_eq!(
            *min_obligations, 0,
            "{case} ({upstream_case}) error cases should have zero obligation metadata"
        );
        expect_error(path, case, upstream_case, expected_error_fragments(case));
    }
}

#[test]
fn marker_traits_rs_unsupported_marker_boundaries_fail_closed_from_file() {
    let path = marker_traits_port_path();
    let path = path
        .to_str()
        .expect("marker_traits port path should be UTF-8");

    for (case, upstream_case, expected_fragments) in FAIL_CLOSED_FRAGMENTS {
        expect_fail_closed(path, case, upstream_case, expected_fragments);
    }
}

/// Flipped from FAIL_CLOSED_FRAGMENTS 2026-07-04: PhantomData<T> parameters are
/// accepted since the PhantomData-as-unit lowering (3f619f0); the trivially TRUE
/// body (assert!(true)) now Verifies. False-mutation control (assert!(false) in
/// a mutated copy) returned Counterexample assertion_0 (control ledger
/// 2026-07-04). Not manifest-embedded; kept out of expected-case metadata so it
/// is not claimed as replacement evidence.
#[test]
fn marker_traits_rs_phantom_data_marker_bound_verifies_from_file() {
    let path = marker_traits_port_path();
    let path = path
        .to_str()
        .expect("marker_traits port path should be UTF-8");

    let result = verify_case(
        path,
        "phantom_data_marker_bound_currently_errors",
        "PhantomData marker-wrapper boundary",
    );
    assert!(
        matches!(result, VerifyResult::Verified),
        "phantom_data_marker_bound_currently_errors (PhantomData marker-wrapper boundary) should verify, got: {result:?}"
    );
}

#[test]
fn marker_traits_rs_upstream_shape_pins_stay_intentional() {
    let (inputs, output) =
        signature_type_tokens_for_case("phantom_data_marker_bound_currently_errors");
    assert_eq!(inputs, vec!["std::marker::PhantomData<T>".to_string()]);
    assert_eq!(output, None);

    let (inputs, output) =
        signature_type_tokens_for_case("vstd_raw_ptr_points_to_send_sync_currently_errors");
    assert_eq!(inputs, vec!["vstd::raw_ptr::PointsTo<T>".to_string()]);
    assert_eq!(output, None);

    let (inputs, output) =
        signature_type_tokens_for_case("vstd_raw_ptr_points_to_send_currently_errors");
    assert_eq!(inputs, vec!["vstd::raw_ptr::PointsTo<T>".to_string()]);
    assert_eq!(output, None);

    let (inputs, output) =
        signature_type_tokens_for_case("vstd_raw_ptr_points_to_sync_currently_errors");
    assert_eq!(inputs, vec!["vstd::raw_ptr::PointsTo<T>".to_string()]);
    assert_eq!(output, None);

    let (inputs, output) =
        signature_type_tokens_for_case("vstd_cell_points_to_send_sync_currently_errors");
    assert_eq!(inputs, vec!["vstd::cell::PointsTo<T>".to_string()]);
    assert_eq!(output, None);

    let (inputs, output) =
        signature_type_tokens_for_case("vstd_cell_points_to_send_currently_errors");
    assert_eq!(inputs, vec!["vstd::cell::PointsTo<T>".to_string()]);
    assert_eq!(output, None);

    let (inputs, output) =
        signature_type_tokens_for_case("vstd_cell_points_to_sync_currently_errors");
    assert_eq!(inputs, vec!["vstd::cell::PointsTo<T>".to_string()]);
    assert_eq!(output, None);

    let (inputs, output) =
        signature_type_tokens_for_case("vstd_cell_pcell_send_sync_currently_errors");
    assert_eq!(inputs, vec!["vstd::cell::pcell::PCell<T>".to_string()]);
    assert_eq!(output, None);

    let (inputs, output) =
        signature_type_tokens_for_case("vstd_tracked_marker_wrapper_currently_errors");
    assert_eq!(inputs, vec!["vstd::prelude::Tracked<T>".to_string()]);
    assert_eq!(output, None);

    let (inputs, output) =
        signature_type_tokens_for_case("vstd_ghost_marker_wrapper_currently_errors");
    assert_eq!(inputs, vec!["vstd::prelude::Ghost<T>".to_string()]);
    assert_eq!(output, None);

    let (inputs, output) =
        signature_type_tokens_for_case("vstd_local_invariant_marker_wrapper_currently_errors");
    assert_eq!(
        inputs,
        vec!["vstd::invariant::LocalInvariant<(),T,Pred<(),T>>".to_string()]
    );
    assert_eq!(output, None);

    let (inputs, output) =
        signature_type_tokens_for_case("vstd_atomic_invariant_marker_wrapper_currently_errors");
    assert_eq!(
        inputs,
        vec!["vstd::invariant::AtomicInvariant<(),T,Pred<(),T>>".to_string()]
    );
    assert_eq!(output, None);

    let (inputs, output) =
        signature_type_tokens_for_case("vstd_atomic_invariant_send_sync_currently_errors");
    assert_eq!(
        inputs,
        vec!["vstd::invariant::AtomicInvariant<(),T,Pred<(),T>>".to_string()]
    );
    assert_eq!(output, None);

    let (inputs, output) =
        signature_type_tokens_for_case("copy_bound_const_generic_array_currently_errors");
    assert_eq!(inputs, vec!["[T ; N]".to_string()]);
    assert_eq!(output, None);

    let (inputs, output) =
        signature_type_tokens_for_case("dyn_send_marker_trait_object_currently_errors");
    assert_eq!(inputs, vec!["&dynSend".to_string()]);
    assert_eq!(output, None);

    let (inputs, output) =
        signature_type_tokens_for_case("dyn_send_sync_marker_trait_object_currently_errors");
    assert_eq!(inputs, vec!["&(dynSend+Sync)".to_string()]);
    assert_eq!(output, None);

    let (inputs, output) =
        signature_type_tokens_for_case("shared_reference_lifetime_identity_verified");
    assert_eq!(inputs, vec!["&'a u8".to_string()]);
    assert_eq!(output, Some("&'a u8".to_string()));

    let (inputs, output) =
        signature_type_tokens_for_case("vstd_tracked_covariant_shape_currently_errors");
    assert_eq!(
        inputs,
        vec!["vstd::prelude::Tracked<&'static u8>".to_string()]
    );
    assert_eq!(output, Some("vstd::prelude::Tracked<&'a u8>".to_string()));

    let (inputs, output) =
        signature_type_tokens_for_case("vstd_ghost_covariant_shape_currently_errors");
    assert_eq!(
        inputs,
        vec!["vstd::prelude::Ghost<&'static u8>".to_string()]
    );
    assert_eq!(output, Some("vstd::prelude::Ghost<&'a u8>".to_string()));

    let (inputs, output) =
        signature_type_tokens_for_case("vstd_local_invariant_variance_shape_currently_errors");
    assert_eq!(
        inputs,
        vec!["vstd::invariant::LocalInvariant<(),&'static u8,Pred2>".to_string()]
    );
    assert_eq!(
        output,
        Some("vstd::invariant::LocalInvariant<(),&'a u8,Pred2>".to_string())
    );

    let (inputs, output) =
        signature_type_tokens_for_case("vstd_atomic_invariant_variance_shape_currently_errors");
    assert_eq!(
        inputs,
        vec!["vstd::invariant::AtomicInvariant<(),&'static u8,Pred2>".to_string()]
    );
    assert_eq!(
        output,
        Some("vstd::invariant::AtomicInvariant<(),&'a u8,Pred2>".to_string())
    );
}

#[test]
fn marker_traits_rs_port_inventory_stays_intentional() {
    let file = parse_marker_traits_port();
    let actual: BTreeSet<_> = file
        .items
        .iter()
        .filter_map(|item| match item {
            syn::Item::Fn(function)
                if function.sig.ident != "marker_traits_rs_expected_cases"
                    && function.sig.ident != "marker_traits_rs_expected_error_patterns" =>
            {
                Some(function.sig.ident.to_string())
            }
            _ => None,
        })
        .collect();
    let expected: BTreeSet<_> = EXPECTED_CASE_METADATA
        .iter()
        .map(|(case, _, _, _)| (*case).to_string())
        .chain(
            FAIL_CLOSED_FRAGMENTS
                .iter()
                .map(|(case, _, _)| (*case).to_string()),
        )
        // Flipped 2026-07-04 (see marker_traits_rs_phantom_data_marker_bound_
        // verifies_from_file): still a top-level witness, no longer fail-closed.
        .chain(std::iter::once(
            "phantom_data_marker_bound_currently_errors".to_string(),
        ))
        .collect();

    assert_eq!(
        actual, expected,
        "marker_traits top-level witness inventory should stay intentional"
    );

    let helper = port_function("marker_traits_rs_expected_cases");
    assert_eq!(helper.sig.ident, "marker_traits_rs_expected_cases");
    let helper = port_function("marker_traits_rs_expected_error_patterns");
    assert_eq!(helper.sig.ident, "marker_traits_rs_expected_error_patterns");
}
