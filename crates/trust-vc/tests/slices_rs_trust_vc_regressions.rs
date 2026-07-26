// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Executable guards for the first upstream slices.rs TrustVc scout.
//!
//! These tests intentionally keep `source/rust_verify_test/tests/slices.rs` as
//! an unsupported gap. They pin only stable Rust-valid TrustVc behavior available
//! today: shared-slice indexing, fixed slice/array view length/index/contains
//! and subrange witnesses, direct mutable-slice indexed assignment, stable
//! wrong-value/view counterexamples, and fail-closed range/Index, Vec, and
//! mutability boundaries. Solver `Unknown` is rejected rather than counted as
//! evidence.

mod common;

use std::{
    collections::{BTreeMap, BTreeSet},
    path::{Path, PathBuf},
};
use trust_vc_core::{verify_function_from_file, VerifyResult};

fn slices_port_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/ported/slices.rs")
}

fn pinned_upstream_slices_path() -> PathBuf {
    common::pinned_verus_test_path("slices.rs")
}

fn verus_manifest_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/verus-tests.json")
}

#[derive(Debug, Eq, PartialEq)]
struct CaseMetadata {
    case_id: String,
    upstream_case_id: String,
    expected_verdict: String,
    min_obligations: usize,
    expected_error_patterns: Vec<String>,
}

fn verify_case(path: &str, case: &str, upstream_case: &str) -> VerifyResult {
    verify_function_from_file(path, case)
        .unwrap_or_else(|err| panic!("{case} ({upstream_case}) should extract: {err}"))
}

fn active_upstream_cases(source: &str) -> Vec<String> {
    source
        .lines()
        .filter_map(|line| {
            let trimmed = line.trim();
            let rest = trimmed.strip_prefix("#[test] ")?;
            rest.split_whitespace().next().map(str::to_string)
        })
        .collect()
}

fn referenced_array_const(file: &syn::File, const_name: &str) -> syn::ExprArray {
    let const_item = file
        .items
        .iter()
        .find_map(|item| match item {
            syn::Item::Const(item_const) if item_const.ident == const_name => Some(item_const),
            _ => None,
        })
        .unwrap_or_else(|| panic!("slices port should define {const_name}"));

    let syn::Expr::Reference(reference) = const_item.expr.as_ref() else {
        panic!("{const_name} should be a borrowed array");
    };
    let syn::Expr::Array(array) = reference.expr.as_ref() else {
        panic!("{const_name} should be a borrowed array");
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

    array
        .elems
        .iter()
        .map(|expr| string_literal(expr, "error_pattern"))
        .collect()
}

fn error_pattern_entries(file: &syn::File) -> BTreeMap<String, Vec<String>> {
    let array = referenced_array_const(file, "SLICES_RS_EXPECTED_ERROR_PATTERNS");
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

        let case_id = string_literal(&tuple.elems[0], "case");
        let patterns = string_slice(&tuple.elems[1]);
        assert!(
            entries.insert(case_id.clone(), patterns).is_none(),
            "duplicate slices error-pattern metadata for {case_id}"
        );
    }

    entries
}

fn ported_expected_cases(source: &str) -> Vec<CaseMetadata> {
    let file = syn::parse_file(source).expect("slices port should parse as ordinary Rust syntax");
    let array = referenced_array_const(&file, "SLICES_RS_EXPECTED_CASES");
    let mut error_patterns = error_pattern_entries(&file);
    let mut seen = BTreeSet::new();

    let entries = array
        .elems
        .iter()
        .map(|entry| {
            let syn::Expr::Tuple(tuple) = entry else {
                panic!("expected-case entry should be a tuple");
            };
            assert_eq!(
                tuple.elems.len(),
                4,
                "expected-case entry should have schema (case, upstream, status, min_obligations)"
            );

            let case = string_literal(&tuple.elems[0], "case");
            assert!(
                seen.insert(case.clone()),
                "duplicate slices metadata for {case}"
            );
            CaseMetadata {
                expected_error_patterns: error_patterns.remove(&case).unwrap_or_default(),
                case_id: case,
                upstream_case_id: string_literal(&tuple.elems[1], "upstream_case"),
                expected_verdict: string_literal(&tuple.elems[2], "expected_status"),
                min_obligations: usize_literal(&tuple.elems[3], "min_obligations"),
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
        "expected error-pattern inventory should not contain orphan cases: {error_patterns:?}"
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
            entry["upstream_path"].as_str() == Some("source/rust_verify_test/tests/slices.rs")
        })
        .expect("Verus manifest should contain slices.rs row");

    row["expected_cases"]
        .as_array()
        .expect("slices.rs row should contain expected_cases")
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

fn string_literal(expr: &syn::Expr, field: &str) -> String {
    let syn::Expr::Lit(expr_lit) = expr else {
        panic!("{field} should be a string literal");
    };
    let syn::Lit::Str(lit) = &expr_lit.lit else {
        panic!("{field} should be a string literal");
    };
    lit.value()
}

fn usize_literal(expr: &syn::Expr, field: &str) -> usize {
    let syn::Expr::Lit(expr_lit) = expr else {
        panic!("{field} should be a usize literal");
    };
    let syn::Lit::Int(lit) = &expr_lit.lit else {
        panic!("{field} should be a usize literal");
    };
    lit.base10_parse()
        .unwrap_or_else(|err| panic!("{field} should parse as usize: {err}"))
}

fn expect_fail_closed_error_contains_any(
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

const EXPECTED_CASE_METADATA: &[(&str, &str, &str, usize)] = &[
    (
        "slices_shared_index_from_requires_verified",
        "",
        "verified",
        1,
    ),
    ("slices_view_len_from_requires_verified", "", "verified", 1),
    (
        "slices_literal_view_len_and_index_verified",
        "",
        "verified",
        2,
    ),
    ("slices_literal_view_contains_verified", "", "verified", 3),
    ("slices_literal_view_subrange_verified", "", "verified", 3),
    (
        "slices_array_view_len_index_contains_verified",
        "",
        "verified",
        4,
    ),
    ("slices_array_view_subrange_verified", "", "verified", 3),
    ("slices_mut_index_assignment_verified", "", "verified", 3),
    (
        "slices_mut_index_assignment_wrong_value_counterexample",
        "",
        "counterexample",
        1,
    ),
    (
        "slices_literal_view_wrong_len_counterexample",
        "",
        "counterexample",
        1,
    ),
    (
        "slices_literal_view_wrong_index_counterexample",
        "",
        "counterexample",
        1,
    ),
    (
        "slices_literal_view_subrange_wrong_index_counterexample",
        "",
        "counterexample",
        1,
    ),
    (
        "slices_array_view_wrong_index_counterexample",
        "",
        "counterexample",
        1,
    ),
    (
        "slices_array_view_subrange_wrong_len_counterexample",
        "",
        "counterexample",
        1,
    ),
    ("slices_range_index_currently_blocked", "", "error", 0),
    ("slices_std_index_method_currently_blocked", "", "error", 0),
    ("slices_array_range_index_currently_blocked", "", "error", 0),
    (
        "slices_array_std_index_method_currently_blocked",
        "",
        "error",
        0,
    ),
    ("slices_vec_range_index_currently_blocked", "", "error", 0),
    (
        "slices_vec_std_range_index_method_currently_blocked",
        "",
        "error",
        0,
    ),
    ("slices_slice_first_mut_currently_blocked", "", "error", 0),
    (
        "slices_slice_split_at_mut_currently_blocked",
        "",
        "error",
        0,
    ),
];

const VERIFIED_CASES: &[(&str, &str)] = &[
    ("slices_shared_index_from_requires_verified", ""),
    ("slices_view_len_from_requires_verified", ""),
    ("slices_literal_view_len_and_index_verified", ""),
    ("slices_literal_view_contains_verified", ""),
    ("slices_literal_view_subrange_verified", ""),
    ("slices_array_view_len_index_contains_verified", ""),
    ("slices_array_view_subrange_verified", ""),
    ("slices_mut_index_assignment_verified", ""),
];

const COUNTEREXAMPLE_CASES: &[(&str, &str)] = &[
    ("slices_mut_index_assignment_wrong_value_counterexample", ""),
    ("slices_literal_view_wrong_len_counterexample", ""),
    ("slices_literal_view_wrong_index_counterexample", ""),
    (
        "slices_literal_view_subrange_wrong_index_counterexample",
        "",
    ),
    ("slices_array_view_wrong_index_counterexample", ""),
    ("slices_array_view_subrange_wrong_len_counterexample", ""),
];

const FAIL_CLOSED_CASES: &[(&str, &str, &[&str])] = &[
    (
        "slices_range_index_currently_blocked",
        "",
        &["range", "unsupported", "index", "slice"],
    ),
    (
        "slices_std_index_method_currently_blocked",
        "",
        &["Index", "index", "unsupported", "method"],
    ),
    (
        "slices_array_range_index_currently_blocked",
        "",
        &["range", "unsupported", "index", "slice"],
    ),
    (
        "slices_array_std_index_method_currently_blocked",
        "",
        &["Index", "index", "unsupported", "method"],
    ),
    (
        "slices_vec_range_index_currently_blocked",
        "",
        &["range", "unsupported", "Vec", "index"],
    ),
    (
        "slices_vec_std_range_index_method_currently_blocked",
        "",
        &["Index", "range", "unsupported", "method"],
    ),
    (
        "slices_slice_first_mut_currently_blocked",
        "",
        &["first_mut", "unwrap", "unsupported", "mutable", "Vec"],
    ),
    (
        "slices_slice_split_at_mut_currently_blocked",
        "",
        &[
            "split_at_mut",
            "unsupported",
            "mutable",
            "Vec",
            "unresolved variable `v`",
        ],
    ),
];

#[test]
fn slices_rs_port_file_is_rust_syntax() {
    let source =
        std::fs::read_to_string(slices_port_path()).expect("slices port should be readable");
    syn::parse_file(&source).expect("slices port should parse as ordinary Rust syntax");
}

#[test]
fn slices_rs_pinned_upstream_case_shapes_are_present() {
    let path = pinned_upstream_slices_path();
    if !path.exists() {
        eprintln!(
            "skipping pinned upstream slices.rs shape check; missing {}",
            path.display()
        );
        return;
    }

    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", path.display()));
    assert_eq!(
        active_upstream_cases(&source),
        [
            "test1",
            "test_recursion_checks",
            "test_slice_iter",
            "test_slices_arrays_extensionality",
            "test_slice_index",
            "test_array_index",
            "test_vec_index",
            "test_other_index",
        ],
        "pinned upstream slices.rs active harness inventory changed"
    );

    for expected in [
        "#[test] test1",
        "#[test] test_recursion_checks",
        "#[test] test_slice_iter",
        "#[test] test_slices_arrays_extensionality",
        "#[test] test_slice_index",
        "#[test] test_array_index",
        "#[test] test_vec_index",
        "#[test] test_other_index",
        "use vstd::{slice::*, prelude::*};",
        "fn foo_index",
        "requires x@.len() == 2, x[0] == 19,",
        "fn foo_generic_index<T>(x: &[T])",
        "fn test_set",
        "fn test_is_empty",
        "struct Foo",
        "field: Box<[ Map<Foo, int> ]>",
        "for x in it: iter",
        "fn test_slice()",
        "fn test_array()",
        "fn test_array_views(a: &[u64; 3], b: &[u64; 3])",
        "fn test_slice_views(a: &[u64], b: &[u64])",
        "fn element(s: &[u8])",
        "fn element_bounds(s: &[u8])",
        "fn range(s: &[u8])",
        "fn range_index(s: &[u8])",
        "fn range_index_bounds(s: &[u8])",
        "fn element(a: &[u8; 5])",
        "fn range(a: &[u8; 5])",
        "fn range_index(a: &[u8; 5])",
        "fn element(v: &Vec<u8>)",
        "fn range(v: &Vec<u8>)",
        "fn range_arc(v: std::sync::Arc<Vec<u8>>)",
        "fn range_deref<A: std::ops::Deref<Target = Vec<u8>>>(v: &A)",
        "fn element_index<I: Index<usize, Output = u8>>(v: &I)",
        "fn range_index<I: Index<std::ops::Range<usize>, Output = u8>>(v: &I)",
        "fn element_index(s: &[u8])",
    ] {
        assert!(
            source.contains(expected),
            "pinned upstream slices.rs should still contain {expected}"
        );
    }
}

#[test]
fn slices_rs_expected_case_metadata_is_exact() {
    let source =
        std::fs::read_to_string(slices_port_path()).expect("slices port should be readable");
    assert!(
        source.contains("pub fn slices_rs_expected_cases")
            && source.contains("pub fn slices_rs_expected_error_patterns"),
        "slices port should expose expected-case and error-pattern metadata helpers"
    );
    let parsed_metadata = ported_expected_cases(&source);
    assert_eq!(parsed_metadata, expected_metadata_from_tests());
    assert_eq!(
        ported_expected_cases(&source),
        manifest_expected_metadata(),
        "slices.rs manifest expected_cases should match port metadata and error patterns exactly"
    );

    for (case, upstream_case, expected_status, min_obligations) in EXPECTED_CASE_METADATA {
        assert!(
            matches!(*expected_status, "verified" | "counterexample" | "error"),
            "{case} ({upstream_case}) has schema-invalid status {expected_status}"
        );
        assert_ne!(
            *expected_status, "unknown",
            "{case} ({upstream_case}) must not use Unknown as expected evidence"
        );
        match *expected_status {
            "verified" | "counterexample" => assert!(
                *min_obligations >= 1,
                "{case} ({upstream_case}) should record at least one obligation"
            ),
            "error" => assert_eq!(
                *min_obligations, 0,
                "{case} ({upstream_case}) error metadata should record zero obligations"
            ),
            _ => unreachable!(),
        }
    }
}

#[test]
fn slices_rs_verified_subset_verifies_from_file() {
    let path = slices_port_path();
    let path = path.to_str().expect("slices port path should be UTF-8");

    for (case, upstream_case) in VERIFIED_CASES {
        let result = verify_case(path, case, upstream_case);
        assert!(
            matches!(result, VerifyResult::Verified),
            "{case} ({upstream_case}) should verify, got: {result:?}"
        );
    }
}

#[test]
fn slices_rs_wrong_value_subset_is_rejected_from_file() {
    let path = slices_port_path();
    let path = path.to_str().expect("slices port path should be UTF-8");

    for (case, upstream_case) in COUNTEREXAMPLE_CASES {
        let result = verify_case(path, case, upstream_case);
        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "{case} ({upstream_case}) should produce a counterexample, got: {result:?}"
        );
    }
}

#[test]
fn slices_rs_range_and_std_index_boundaries_fail_closed_from_file() {
    let path = slices_port_path();
    let path = path.to_str().expect("slices port path should be UTF-8");

    for (case, upstream_case, expected_fragments) in FAIL_CLOSED_CASES {
        expect_fail_closed_error_contains_any(path, case, upstream_case, expected_fragments);
    }
}
