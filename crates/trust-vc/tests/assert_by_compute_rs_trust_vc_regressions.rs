// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Executable guards for the currently ported upstream assert_by_compute.rs
//! subset.
//!
//! These tests intentionally do not claim full Verus compute parity. They prove
//! the listed upstream-derived slices execute through TrustVc while the manifest
//! keeps `source/rust_verify_test/tests/assert_by_compute.rs` fail-closed.

mod common;

use std::{
    collections::{BTreeMap, BTreeSet},
    path::PathBuf,
};
use trust_vc_core::{verify_function_from_file, VerifyResult};

fn assert_by_compute_port_path() -> PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../evals/verus/ported/assert_by_compute.rs")
}

fn assert_by_compute_upstream_path() -> PathBuf {
    common::pinned_verus_test_path("assert_by_compute.rs")
}

fn verus_manifest_path() -> PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/verus-tests.json")
}

fn verify_port_case(case: &str, upstream_case: &str) -> VerifyResult {
    let path = assert_by_compute_port_path();
    let path = path
        .to_str()
        .expect("assert_by_compute port path should be UTF-8");
    verify_function_from_file(path, case)
        .unwrap_or_else(|err| panic!("{case} ({upstream_case}) should extract: {err}"))
}

fn fail_closed_message(case: &str, upstream_case: &str) -> String {
    match verify_port_case(case, upstream_case) {
        VerifyResult::Error { message } => message,
        other => {
            panic!("{case} ({upstream_case}) should fail closed with Error, got: {other:?}")
        }
    }
}

const VERIFIED_CASES: &[(&str, &str)] = &[
    ("lets_bool", "lets"),
    ("lets_arith", "lets"),
    ("lets_upstream_comparisons_compute_only", "lets"),
    ("bitwise_and_constants", "bit_vectors"),
    ("bitwise_basic_constants", "bit_vectors"),
    (
        "bitwise_wide_and_signed_shift_constants_compute_only",
        "bit_vectors",
    ),
    ("bitwise_recursive_shift_compute_only", "bit_vectors"),
    (
        "datatype_struct_tuple_constants_compute_only",
        "datatypes/tuples/structs",
    ),
    ("datatype_option_match_compute_only", "datatype"),
    ("tuple_projection_constants_compute_only", "tuples"),
    ("sequence_constants_compute_only", "sequences"),
    ("sequence_upstream_literals_compute_only", "sequences"),
    ("sequence_subrange_compute_only", "sequences/subrange"),
    (
        "sequence_push_last_update_add_compute_only",
        "sequences/push-last-update-add",
    ),
    ("array_constants_compute_only", "arrays"),
    ("array_literal_index_compute_only", "array_literals"),
    ("local_array_index_compute_only", "array_literals"),
    ("bounded_forall_compute_only", "bounded forall"),
    (
        "char_casts_and_comparisons_compute_only",
        "char casts/comparisons",
    ),
    ("if_then_else_compute_only", "if_then_else"),
    ("compute_only_arith", "arith"),
    ("compute_only_euclidean_div_mod_arith", "arith"),
    ("compute_only_euclidean_div_mod_small_boundaries", "arith"),
    (
        "compute_only_recursive_spec_function",
        "recursive_spec_fn/fn_calls_good",
    ),
    ("fn_calls_upstream_nested_compute_only", "fn_calls_good"),
    (
        "depth_tracking_deep_but_finite_compute_only",
        "depth_tracking_deep_but_finite",
    ),
];

const COUNTEREXAMPLE_CASES: &[(&str, &str)] = &[
    ("lets_bad", "lets_bad"),
    ("lets_upstream_comparisons_counterexample", "lets"),
    (
        "datatype_struct_tuple_constants_counterexample",
        "datatypes/tuples/structs",
    ),
    ("datatype_option_match_counterexample", "datatype"),
    ("tuple_projection_counterexample", "tuples"),
    ("struct_constants_counterexample", "structs"),
    ("sequence_constants_counterexample", "sequences"),
    ("sequence_upstream_literals_counterexample", "sequences"),
    ("sequence_subrange_counterexample", "sequences/subrange"),
    (
        "sequence_push_last_update_add_counterexample",
        "sequences/push-last-update-add",
    ),
    ("array_constants_counterexample", "arrays"),
    ("array_literal_index_counterexample", "array_literals"),
    ("local_array_index_counterexample", "array_literals"),
    ("bounded_forall_counterexample", "bounded forall"),
    ("char_casts_counterexample", "char casts/comparisons"),
    ("if_then_else_counterexample", "if_then_else"),
    ("compute_only_euclidean_div_mod_counterexample", "arith"),
    (
        "compute_only_euclidean_div_mod_small_boundary_counterexample",
        "arith",
    ),
    ("bitwise_wide_constants_counterexample", "bit_vectors"),
    ("bitwise_recursive_shift_counterexample", "bit_vectors"),
    ("fn_calls_upstream_nested_counterexample", "fn_calls_good"),
    (
        "depth_tracking_deep_but_finite_counterexample",
        "depth_tracking_deep_but_finite",
    ),
];

const FAIL_CLOSED_CASES: &[(&str, &str, &[&str])] = &[(
    "const_in_another_module_compute_only",
    "const_in_another_module",
    &[
        "unsupported expression `assert_by_compute_const_module::BIN_HUGE`",
        "only pure, side-effect-free expressions",
    ],
)];

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
        .unwrap_or_else(|| panic!("assert_by_compute port should define {const_name}"));

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
    let array = referenced_array_const(file, "ASSERT_BY_COMPUTE_RS_FAIL_CLOSED_ERROR_PATTERNS");
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
    let array = referenced_array_const(file, "ASSERT_BY_COMPUTE_RS_EXPECTED_CASES");
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
            "duplicate assert_by_compute metadata for {case_id}"
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

fn manifest_metadata() -> Vec<CaseMetadata> {
    let source =
        std::fs::read_to_string(verus_manifest_path()).expect("Verus manifest should be readable");
    let manifest: serde_json::Value =
        serde_json::from_str(&source).expect("Verus manifest should parse as JSON");
    let entries = manifest["entries"]
        .as_array()
        .expect("Verus manifest should contain entries");
    let row = entries
        .iter()
        .find(|entry| {
            entry["upstream_path"].as_str()
                == Some("source/rust_verify_test/tests/assert_by_compute.rs")
        })
        .expect("Verus manifest should contain assert_by_compute.rs row");

    row["expected_cases"]
        .as_array()
        .expect("assert_by_compute.rs row should contain expected_cases")
        .iter()
        .map(|case| CaseMetadata {
            case_id: case["case_id"]
                .as_str()
                .expect("case should contain case_id")
                .to_string(),
            upstream_case_id: case["upstream_case_id"]
                .as_str()
                .expect("case should contain upstream_case_id")
                .to_string(),
            expected_verdict: case["expected_verdict"]
                .as_str()
                .expect("case should contain expected_verdict")
                .to_string(),
            min_obligations: case["min_obligations"]
                .as_u64()
                .expect("case should contain min_obligations")
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
                                .expect("error pattern should be a string")
                                .to_string()
                        })
                        .collect()
                })
                .unwrap_or_default(),
        })
        .collect()
}

#[test]
fn assert_by_compute_rs_expected_case_metadata_matches_manifest() {
    let source = std::fs::read_to_string(assert_by_compute_port_path())
        .expect("assert_by_compute port should be readable");
    let file = syn::parse_file(&source)
        .expect("assert_by_compute port should parse as ordinary Rust syntax");
    assert_eq!(metadata_entries(&file), manifest_metadata());
    assert!(
        source.contains("assert_by_compute_rs_expected_cases"),
        "assert_by_compute port should export expected-case metadata"
    );
    assert!(
        source.contains("assert_by_compute_rs_fail_closed_error_patterns"),
        "assert_by_compute port should export fail-closed error-pattern metadata"
    );
}

#[test]
fn assert_by_compute_rs_port_file_is_rust_syntax() {
    let source = std::fs::read_to_string(assert_by_compute_port_path())
        .expect("assert_by_compute port should be readable");
    syn::parse_file(&source).expect("assert_by_compute port should parse as ordinary Rust syntax");
}

#[test]
fn assert_by_compute_rs_pinned_upstream_case_shapes_are_present() {
    let path = assert_by_compute_upstream_path();
    if !path.exists() {
        eprintln!(
            "skipping pinned upstream assert_by_compute.rs shape check; missing {}",
            path.display()
        );
        return;
    }

    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", path.display()));
    for expected in [
        "#[test] bit_vectors",
        "#[test] arith",
        "#[test] if_then_else",
        "#[test] lets",
        "#[test] lets_bad",
        "#[test] datatype",
        "#[test] tuples",
        "#[test] structs",
        "#[test] fn_calls_good",
        "#[test] sequences",
        "#[test] array_literals",
        "#[test] const_in_another_module",
        "#[test] depth_tracking_deep_but_finite",
        "assert(match Option::Some(true)",
        "spec fn mk_tuple() -> (u32, u32, u64, bool)",
        "assert(mk_tuple().2 - 0xFFFF_FFFF == 1) by (compute_only)",
        "assert(sum(20) == 20) by (compute_only)",
        "assert(seq![1int, 2, 3].update(1, 5).index(1) == 5) by (compute_only)",
        "assert(BIN_HUGE == 12) by(compute_only)",
    ] {
        assert!(
            source.contains(expected),
            "pinned upstream assert_by_compute.rs should still contain {expected}"
        );
    }
}

#[test]
fn assert_by_compute_rs_verified_subset_verifies_from_file() {
    for (case, upstream_case) in VERIFIED_CASES {
        let result = verify_port_case(case, upstream_case);
        assert!(
            matches!(result, VerifyResult::Verified),
            "{case} ({upstream_case}) should verify, got: {result:?}"
        );
    }
}

#[test]
fn assert_by_compute_rs_counterexample_subset_is_rejected_from_file() {
    for (case, upstream_case) in COUNTEREXAMPLE_CASES {
        let result = verify_port_case(case, upstream_case);
        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "{case} ({upstream_case}) should be rejected, got: {result:?}"
        );
    }
}

#[test]
fn assert_by_compute_rs_unsupported_surfaces_fail_closed_from_file() {
    for (case, upstream_case, expected_fragments) in FAIL_CLOSED_CASES {
        let message = fail_closed_message(case, upstream_case);
        assert!(
            expected_fragments
                .iter()
                .all(|expected_fragment| message.contains(expected_fragment)),
            "{case} ({upstream_case}) error should contain {expected_fragments:?}, got: {message}"
        );
    }
}
