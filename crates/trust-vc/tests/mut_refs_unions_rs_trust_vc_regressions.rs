// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Executable guards for the first upstream mut_refs_unions.rs TrustVc scout.
//!
//! These tests intentionally keep
//! `source/rust_verify_test/tests/mut_refs_unions.rs` as an unsupported gap.
//! They pin only stable tagged-surrogate executable behavior TrustVc verifies,
//! stale-value and struct-update-tail counterexamples, and fail-closed native
//! union/Verus helper boundaries. `Unknown` is not accepted as evidence.

mod common;

use std::{
    collections::{BTreeMap, BTreeSet},
    path::{Path, PathBuf},
};
use trust_vc_core::{
    extract_verification_conditions_with_file_context, verify_function_from_file, VerifyResult,
};

#[derive(Debug, Eq, PartialEq)]
struct CaseMetadata {
    case_id: String,
    upstream_case_id: String,
    expected_verdict: String,
    min_obligations: usize,
    expected_error_patterns: Vec<String>,
}

fn mut_refs_unions_port_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/ported/mut_refs_unions.rs")
}

fn verus_manifest_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/verus-tests.json")
}

fn pinned_upstream_mut_refs_unions_path() -> PathBuf {
    common::pinned_verus_test_path("mut_refs_unions.rs")
}

fn verify_case(path: &Path, case: &str, upstream_case: &str) -> (VerifyResult, usize) {
    let path_str = path
        .to_str()
        .expect("mut_refs_unions port path should be UTF-8");
    let result = verify_function_from_file(path_str, case)
        .unwrap_or_else(|err| panic!("{case} ({upstream_case}) should extract: {err}"));

    let source = std::fs::read_to_string(path)
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

    (result, vc.obligations().len())
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

fn referenced_array_const(file: &syn::File, const_name: &str) -> syn::ExprArray {
    let const_item = file
        .items
        .iter()
        .find_map(|item| match item {
            syn::Item::Const(item) if item.ident == const_name => Some(item),
            _ => None,
        })
        .unwrap_or_else(|| panic!("mut_refs_unions port should define {const_name}"));

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
    let array = referenced_array_const(file, "MUT_REFS_UNIONS_RS_EXPECTED_ERROR_PATTERNS");
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
            "duplicate mut_refs_unions error-pattern metadata for {case_id}"
        );
    }

    entries
}

fn metadata_entries(file: &syn::File) -> Vec<CaseMetadata> {
    let array = referenced_array_const(file, "MUT_REFS_UNIONS_RS_EXPECTED_CASES");
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
            "duplicate mut_refs_unions metadata for {case_id}"
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
                == Some("source/rust_verify_test/tests/mut_refs_unions.rs")
        })
        .expect("Verus manifest should contain mut_refs_unions.rs row");

    row["expected_cases"]
        .as_array()
        .expect("mut_refs_unions.rs row should contain expected_cases")
        .iter()
        .map(|entry| CaseMetadata {
            case_id: entry["case_id"]
                .as_str()
                .expect("case_id should be a string")
                .to_string(),
            upstream_case_id: entry
                .get("upstream_case_id")
                .and_then(serde_json::Value::as_str)
                .unwrap_or("")
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

const VERIFIED_CASES: &[(&str, &str, usize)] = &[
    (
        "mut_refs_unions_tagged_a_mut_ref_update_verified",
        "test_basic::test_mut_ref correct a-variant mut-ref field update surrogate",
        4,
    ),
    (
        "mut_refs_unions_tagged_a_field_update_verified",
        "test_basic::test_assign correct a-variant field update surrogate",
        3,
    ),
    (
        "mut_refs_unions_tagged_b_nested_mut_ref_update_verified",
        "test_basic::test_mut_ref_nested correct b-variant nested mut-ref update surrogate",
        4,
    ),
    (
        "mut_refs_unions_tagged_b_nested_update_verified",
        "test_basic::test_assign_nested correct b-variant nested update surrogate",
        4,
    ),
    (
        "mut_refs_unions_two_phase_scalar_update_verified",
        "two_phase_borrows_to_union_fields::test2 scalar field-ref update surrogate",
        4,
    ),
    (
        "mut_refs_unions_two_phase_struct_update_verified",
        "two_phase_borrows_to_union_fields2::test1 struct field update surrogate",
        4,
    ),
    (
        "mut_refs_unions_tagged_b_struct_update_tail_verified",
        "ctor_update_tail::test_update tagged b-variant struct-update-tail surrogate",
        2,
    ),
];

const COUNTEREXAMPLE_CASES: &[(&str, &str, usize)] = &[
    (
        "mut_refs_unions_tagged_a_stale_value_counterexample",
        "test_basic::fails_assign stale a-field assertion surrogate",
        1,
    ),
    (
        "mut_refs_unions_tagged_b_struct_update_tail_counterexample",
        "ctor_update_tail::fails_update tagged b-variant false-tail surrogate",
        1,
    ),
];

// WHAT THESE PATTERNS MEASURE, and what they no longer can. Every native-union
// case is now refused at EXTRACTION ENTRY (the union taint closure in
// `vc_extraction::reject_union_use`), which PREEMPTS the four later boundaries
// these cases used to land on — the `get_union_field` builtin, `is_variant`, the
// native destructuring pattern, and the unsafe-block/unknown-type path. Those
// downstream messages are unreachable for a union-declaring file and cannot be
// asserted here any more; asserting them would be asserting a diagnostic the
// engine no longer emits. `expected_error_patterns` is an AND-conjunction over
// the case's own joined diagnostic context, so each case instead pins the
// blanket boundary AND its own SUBJECT line, which keeps the eight assertions
// distinguishable: a case passes only when the refusal named THAT function and
// the union it reached, not merely when some union refusal appeared somewhere.
const FAIL_CLOSED_CASES: &[(&str, &str, &[&str])] = &[
    (
        "mut_refs_unions_native_field_access_currently_blocked",
        "test_basic::test_assign native union field access boundary",
        &[
            "does not model Rust unions",
            "`mut_refs_unions_native_field_access_currently_blocked` names the union `MutRefsUnionsNative`",
        ],
    ),
    (
        "mut_refs_unions_is_variant_currently_blocked",
        "two_phase_borrows_to_union_fields is_variant boundary",
        &[
            "does not model Rust unions",
            "`mut_refs_unions_is_variant_currently_blocked` names the union `MutRefsUnionsNative`",
        ],
    ),
    (
        "mut_refs_unions_has_resolved_currently_blocked",
        "union_has_resolved::test native has_resolved boundary",
        &["has_resolved", "unknown return type for function"],
    ),
    (
        "mut_refs_unions_get_union_field_currently_blocked",
        "two_phase_borrows_to_union_fields get_union_field boundary",
        &[
            "does not model Rust unions",
            "`mut_refs_unions_get_union_field_currently_blocked` names the union `MutRefsUnionsNative`",
        ],
    ),
    (
        "mut_refs_unions_native_struct_update_tail_wrong_variant_currently_blocked",
        "ctor_update_tail::wrong_variant native union struct-update-tail boundary",
        &[
            "does not model Rust unions",
            "`mut_refs_unions_native_struct_update_tail_wrong_variant_currently_blocked` names the union `MutRefsUnionsNative`",
        ],
    ),
];

#[test]
fn mut_refs_unions_rs_port_file_is_rust_syntax() {
    let source = std::fs::read_to_string(mut_refs_unions_port_path())
        .expect("mut_refs_unions port should be readable");
    syn::parse_file(&source).expect("mut_refs_unions port should parse as ordinary Rust syntax");
}

#[test]
fn mut_refs_unions_rs_pinned_upstream_case_shapes_are_present() {
    let path = pinned_upstream_mut_refs_unions_path();
    if !path.exists() {
        eprintln!(
            "skipping pinned upstream mut_refs_unions.rs shape check; missing {}",
            path.display()
        );
        return;
    }

    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", path.display()));

    for expected in [
        "#[test] test_basic",
        "#[test] test_wrong_variant_mut_ref",
        "fn test_mut_ref()",
        "fn test_mut_ref_nested()",
        "#[test] ctor_update_tail",
        "#[test] union_has_resolved",
        "#[test] union_with_mut_ref_in_fields",
        "#[test] eval_order_union_array_issue1",
        "#[test] two_phase_borrows_to_union_fields",
    ] {
        assert!(
            source.contains(expected),
            "pinned upstream mut_refs_unions.rs should still contain {expected}"
        );
    }
}

#[test]
fn mut_refs_unions_rs_expected_case_metadata_is_exact() {
    let source = std::fs::read_to_string(mut_refs_unions_port_path())
        .expect("mut_refs_unions port should be readable");
    let file = syn::parse_file(&source)
        .expect("mut_refs_unions port should parse as ordinary Rust syntax");
    assert_eq!(metadata_entries(&file), manifest_expected_metadata());
    assert!(
        source.contains("mut_refs_unions_rs_expected_cases")
            && source.contains("mut_refs_unions_rs_expected_error_patterns"),
        "mut_refs_unions port should expose case and error-pattern metadata accessors"
    );
}

#[test]
fn mut_refs_unions_rs_verified_subset_verifies_from_file() {
    let path = mut_refs_unions_port_path();

    for (case, upstream_case, min_obligations) in VERIFIED_CASES {
        let (result, obligations) = verify_case(&path, case, upstream_case);
        assert!(
            obligations >= *min_obligations,
            "{case} ({upstream_case}) should collect at least {min_obligations} obligation(s), got {obligations}"
        );
        assert!(
            matches!(result, VerifyResult::Verified),
            "{case} ({upstream_case}) should verify, got: {result:?}"
        );
    }
}

#[test]
fn mut_refs_unions_rs_stale_tagged_value_is_rejected_from_file() {
    let path = mut_refs_unions_port_path();

    for (case, upstream_case, min_obligations) in COUNTEREXAMPLE_CASES {
        let (result, obligations) = verify_case(&path, case, upstream_case);
        assert!(
            obligations >= *min_obligations,
            "{case} ({upstream_case}) should collect at least {min_obligations} obligation(s), got {obligations}"
        );
        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "{case} ({upstream_case}) should produce a counterexample, got: {result:?}"
        );
    }
}

#[test]
fn mut_refs_unions_rs_native_union_boundaries_fail_closed_from_file() {
    let path = mut_refs_unions_port_path();
    let path = path
        .to_str()
        .expect("mut_refs_unions port path should be UTF-8");

    for (case, upstream_case, expected_fragments) in FAIL_CLOSED_CASES {
        expect_fail_closed_error_contains_any(path, case, upstream_case, expected_fragments);
    }
}
