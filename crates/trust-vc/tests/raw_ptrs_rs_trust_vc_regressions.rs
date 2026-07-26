// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Executable guards for the first upstream raw_ptrs.rs TrustVc scout slice.
//!
//! These tests intentionally keep `source/rust_verify_test/tests/raw_ptrs.rs`
//! as an unsupported gap. They pin only stable TrustVc behavior available today:
//! scalar address/provenance/metadata/null-address/PointsTo witnesses, stable
//! counterexamples for false upstream-shaped claims, and fail-closed raw
//! pointer/provenance/PointsTo/allocate boundaries. Solver `Unknown` is rejected
//! as replacement evidence.

#![allow(dead_code)]

mod common;

use std::{
    collections::{BTreeMap, BTreeSet},
    path::{Path, PathBuf},
};
use trust_vc_core::{
    extract_verification_conditions_with_file_context, verify_function_from_file, VerifyResult,
};

fn raw_ptrs_port_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/ported/raw_ptrs.rs")
}

fn pinned_upstream_raw_ptrs_path() -> PathBuf {
    common::pinned_verus_test_path("raw_ptrs.rs")
}

fn verus_manifest_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/verus-tests.json")
}

#[derive(Clone, Copy)]
struct ExpectedCase {
    case: &'static str,
    upstream_case: &'static str,
    evidence_status: &'static str,
    min_obligations: usize,
}

#[derive(Clone, Copy)]
struct FailClosedCase {
    case: &'static str,
    upstream_case: &'static str,
    local_blocker: &'static str,
    expected_fragments: &'static [&'static str],
}

#[derive(Debug, Eq, PartialEq)]
struct CaseMetadata {
    case_id: String,
    upstream_case_id: String,
    expected_verdict: String,
    min_obligations: usize,
    expected_error_patterns: Vec<String>,
}

fn verify_case_with_obligations(
    path: &Path,
    case: &str,
    upstream_case: &str,
) -> (VerifyResult, usize) {
    let source = std::fs::read_to_string(path)
        .unwrap_or_else(|err| panic!("raw_ptrs port should be readable: {err}"));
    let file =
        syn::parse_file(&source).unwrap_or_else(|err| panic!("raw_ptrs port should parse: {err}"));
    let func = file
        .items
        .iter()
        .find_map(|item| match item {
            syn::Item::Fn(func) if func.sig.ident == case => Some(func),
            _ => None,
        })
        .unwrap_or_else(|| panic!("{case} ({upstream_case}) should exist in raw_ptrs port"));

    let vc = extract_verification_conditions_with_file_context(&file, func)
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

fn expect_fail_closed_error_contains_any(
    path: &str,
    case: &str,
    upstream_case: &str,
    local_blocker: &str,
    expected_fragments: &[&str],
) {
    let message = match verify_function_from_file(path, case) {
        Err(err) => err.to_string(),
        Ok(VerifyResult::Error { message }) => message,
        Ok(VerifyResult::Unknown { reason, .. }) => {
            panic!(
                "{case} ({upstream_case}) returned solver Unknown for {local_blocker}, which is not stable fail-closed evidence: {reason}"
            )
        }
        Ok(other) => {
            panic!(
                "{case} ({upstream_case}) should fail closed with Error for {local_blocker}, got: {other:?}"
            )
        }
    };

    assert!(
        expected_fragments
            .iter()
            .any(|expected_fragment| message.contains(expected_fragment)),
        "{case} ({upstream_case}) error for {local_blocker} should contain one of {expected_fragments:?}, got: {message}"
    );
}

fn literal_string(expr: &syn::Expr) -> String {
    let syn::Expr::Lit(lit) = expr else {
        panic!("expected string literal in raw_ptrs metadata");
    };
    let syn::Lit::Str(value) = &lit.lit else {
        panic!("expected string literal in raw_ptrs metadata");
    };
    value.value()
}

fn literal_usize(expr: &syn::Expr) -> usize {
    let syn::Expr::Lit(lit) = expr else {
        panic!("expected integer literal in raw_ptrs metadata");
    };
    let syn::Lit::Int(value) = &lit.lit else {
        panic!("expected integer literal in raw_ptrs metadata");
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

fn referenced_array_const(file: &syn::File, const_name: &str) -> syn::ExprArray {
    let const_item = file
        .items
        .iter()
        .find_map(|item| match item {
            syn::Item::Const(item) if item.ident == const_name => Some(item),
            _ => None,
        })
        .unwrap_or_else(|| panic!("raw_ptrs port should define {const_name}"));

    let syn::Expr::Reference(reference) = const_item.expr.as_ref() else {
        panic!("{const_name} should be a referenced array");
    };
    let syn::Expr::Array(array) = reference.expr.as_ref() else {
        panic!("{const_name} should reference an array");
    };
    array.clone()
}

fn struct_field<'a>(item: &'a syn::ExprStruct, field_name: &str) -> &'a syn::Expr {
    item.fields
        .iter()
        .find_map(|field| match &field.member {
            syn::Member::Named(ident) if ident == field_name => Some(&field.expr),
            _ => None,
        })
        .unwrap_or_else(|| panic!("raw_ptrs metadata should contain {field_name}"))
}

fn error_pattern_entries(file: &syn::File) -> BTreeMap<String, Vec<String>> {
    let array = referenced_array_const(file, "RAW_PTRS_RS_EXPECTED_ERROR_PATTERNS");
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
            "duplicate raw_ptrs error-pattern metadata for {case_id}"
        );
    }

    entries
}

fn metadata_entries(file: &syn::File) -> Vec<CaseMetadata> {
    let array = referenced_array_const(file, "RAW_PTRS_RS_EXPECTED_CASES");
    let mut error_patterns = error_pattern_entries(file);
    let mut seen = BTreeSet::new();
    let mut entries = Vec::new();

    for entry in &array.elems {
        let syn::Expr::Struct(item) = entry else {
            panic!("expected RawPtrsExpectedCase struct metadata entry");
        };
        let case_id = literal_string(struct_field(item, "case"));
        assert!(
            seen.insert(case_id.clone()),
            "duplicate raw_ptrs metadata for {case_id}"
        );
        entries.push(CaseMetadata {
            expected_error_patterns: error_patterns.remove(&case_id).unwrap_or_default(),
            case_id,
            upstream_case_id: literal_string(struct_field(item, "upstream_case")),
            expected_verdict: literal_string(struct_field(item, "evidence_status")),
            min_obligations: literal_usize(struct_field(item, "min_obligations")),
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
            entry["upstream_path"].as_str() == Some("source/rust_verify_test/tests/raw_ptrs.rs")
        })
        .expect("Verus manifest should contain raw_ptrs.rs row");

    row["expected_cases"]
        .as_array()
        .expect("raw_ptrs.rs row should contain expected_cases")
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

const EXPECTED_CASES: &[ExpectedCase] = &[
    ExpectedCase {
        case: "raw_ptr_addr_view_surrogate_verified",
        upstream_case: "basics",
        evidence_status: "verified",
        min_obligations: 4,
    },
    ExpectedCase {
        case: "raw_ptr_null_addr_boundary_surrogate_verified",
        upstream_case: "test_null",
        evidence_status: "verified",
        min_obligations: 2,
    },
    ExpectedCase {
        case: "raw_ptr_mut_const_cast_surrogate_verified",
        upstream_case: "basics",
        evidence_status: "verified",
        min_obligations: 4,
    },
    ExpectedCase {
        case: "raw_ptr_strict_provenance_with_addr_surrogate_verified",
        upstream_case: "basics",
        evidence_status: "verified",
        min_obligations: 4,
    },
    ExpectedCase {
        case: "raw_ptr_slice_metadata_cast_surrogate_verified",
        upstream_case: "basics",
        evidence_status: "verified",
        min_obligations: 4,
    },
    ExpectedCase {
        case: "raw_ptr_pointer_int_cast_surrogate_verified",
        upstream_case: "pointer_cast_to_ints",
        evidence_status: "verified",
        min_obligations: 2,
    },
    ExpectedCase {
        case: "raw_ptr_compare_addr_surrogate_verified",
        upstream_case: "compare_const_mut_pointers",
        evidence_status: "verified",
        min_obligations: 2,
    },
    ExpectedCase {
        case: "raw_ptr_points_to_write_read_surrogate_verified",
        upstream_case: "basics",
        evidence_status: "verified",
        min_obligations: 6,
    },
    ExpectedCase {
        case: "raw_ptr_addr_distinct_counterexample",
        upstream_case: "basics",
        evidence_status: "counterexample",
        min_obligations: 1,
    },
    ExpectedCase {
        case: "raw_ptr_strict_provenance_addr_change_counterexample",
        upstream_case: "basics",
        evidence_status: "counterexample",
        min_obligations: 1,
    },
    ExpectedCase {
        case: "raw_ptr_pointer_int_truncation_counterexample",
        upstream_case: "pointer_cast_to_ints",
        evidence_status: "counterexample",
        min_obligations: 1,
    },
    ExpectedCase {
        case: "raw_ptr_exec_eq_not_spec_eq_counterexample",
        upstream_case: "pointer_exec_eq_is_not_spec_eq",
        evidence_status: "counterexample",
        min_obligations: 1,
    },
    ExpectedCase {
        case: "raw_ptr_points_to_uninit_read_counterexample",
        upstream_case: "basics",
        evidence_status: "counterexample",
        min_obligations: 1,
    },
    ExpectedCase {
        case: "raw_ptr_points_to_wrong_ptr_counterexample",
        upstream_case: "basics",
        evidence_status: "counterexample",
        min_obligations: 1,
    },
    ExpectedCase {
        case: "raw_ptr_int_to_mut_ptr_cast_currently_blocked",
        upstream_case: "not_supported_int_to_ptr_cast",
        evidence_status: "error",
        min_obligations: 0,
    },
    ExpectedCase {
        case: "raw_ptr_null_constructor_currently_blocked",
        upstream_case: "test_null",
        evidence_status: "error",
        min_obligations: 0,
    },
    ExpectedCase {
        case: "raw_ptr_null_mut_constructor_currently_blocked",
        upstream_case: "basics",
        evidence_status: "error",
        min_obligations: 0,
    },
    ExpectedCase {
        case: "raw_ptr_const_deref_currently_blocked",
        upstream_case: "not_supported_deref_ptr",
        evidence_status: "error",
        min_obligations: 0,
    },
    ExpectedCase {
        case: "raw_ptr_mut_deref_currently_blocked",
        upstream_case: "not_supported_deref_ptr",
        evidence_status: "error",
        min_obligations: 0,
    },
    ExpectedCase {
        case: "raw_ptr_mut_to_const_cast_currently_blocked",
        upstream_case: "basics",
        evidence_status: "error",
        min_obligations: 0,
    },
    ExpectedCase {
        case: "raw_ptr_addr_method_currently_blocked",
        upstream_case: "basics",
        evidence_status: "error",
        min_obligations: 0,
    },
    ExpectedCase {
        case: "raw_ptr_with_addr_method_currently_blocked",
        upstream_case: "basics",
        evidence_status: "error",
        min_obligations: 0,
    },
    ExpectedCase {
        case: "raw_ptr_compare_const_mut_native_currently_blocked",
        upstream_case: "compare_const_mut_pointers",
        evidence_status: "error",
        min_obligations: 0,
    },
    ExpectedCase {
        case: "raw_ptr_points_to_token_methods_verified",
        upstream_case: "basics",
        evidence_status: "verified",
        min_obligations: 7,
    },
    ExpectedCase {
        case: "raw_ptr_points_to_write_api_currently_blocked",
        upstream_case: "basics",
        evidence_status: "error",
        min_obligations: 0,
    },
    ExpectedCase {
        case: "raw_ptr_allocate_helper_currently_blocked",
        upstream_case: "allocate_in_bounds",
        evidence_status: "error",
        min_obligations: 0,
    },
    ExpectedCase {
        case: "raw_ptr_extensionality_sized_surrogate_verified",
        upstream_case: "basics",
        evidence_status: "verified",
        min_obligations: 4,
    },
    ExpectedCase {
        case: "raw_ptr_extensionality_unsized_metadata_counterexample",
        upstream_case: "basics",
        evidence_status: "counterexample",
        min_obligations: 1,
    },
];

const FAIL_CLOSED_CASES: &[FailClosedCase] = &[
    FailClosedCase {
        case: "raw_ptr_int_to_mut_ptr_cast_currently_blocked",
        upstream_case: "not_supported_int_to_ptr_cast",
        local_blocker: "native int-to-raw-pointer cast",
        expected_fragments: &["unsupported cast from", "*mutu8"],
    },
    FailClosedCase {
        case: "raw_ptr_null_constructor_currently_blocked",
        upstream_case: "test_null",
        local_blocker: "native null raw-pointer constructor",
        expected_fragments: &["unknown return type", "core::ptr::null"],
    },
    FailClosedCase {
        case: "raw_ptr_null_mut_constructor_currently_blocked",
        upstream_case: "basics",
        local_blocker: "native null_mut raw-pointer constructor",
        expected_fragments: &["unknown return type", "core::ptr::null_mut"],
    },
    FailClosedCase {
        case: "raw_ptr_const_deref_currently_blocked",
        upstream_case: "not_supported_deref_ptr",
        local_blocker: "native const raw-pointer dereference",
        expected_fragments: &["dereference expressions are not supported", "*x"],
    },
    FailClosedCase {
        case: "raw_ptr_mut_deref_currently_blocked",
        upstream_case: "not_supported_deref_ptr",
        local_blocker: "native mut raw-pointer dereference",
        expected_fragments: &["dereference expressions are not supported", "*x"],
    },
    FailClosedCase {
        case: "raw_ptr_mut_to_const_cast_currently_blocked",
        upstream_case: "basics",
        local_blocker: "native raw-pointer-to-raw-pointer cast",
        expected_fragments: &["unsupported cast", "*constu8", "*mutu8"],
    },
    FailClosedCase {
        case: "raw_ptr_addr_method_currently_blocked",
        upstream_case: "basics",
        local_blocker: "strict-provenance addr()",
        expected_fragments: &[
            "addr",
            "unsupported method",
            "unknown return type",
            "unsupported cast",
        ],
    },
    FailClosedCase {
        case: "raw_ptr_with_addr_method_currently_blocked",
        upstream_case: "basics",
        local_blocker: "strict-provenance with_addr()",
        expected_fragments: &[
            "with_addr",
            "unsupported method",
            "unknown return type",
            "unsupported cast",
        ],
    },
    FailClosedCase {
        case: "raw_ptr_compare_const_mut_native_currently_blocked",
        upstream_case: "compare_const_mut_pointers",
        local_blocker: "native const/mut raw-pointer comparison",
        expected_fragments: &["unsupported", "unsupported cast", "*constu32", "*mutu32"],
    },
    FailClosedCase {
        case: "raw_ptr_points_to_write_api_currently_blocked",
        upstream_case: "basics",
        local_blocker: "PointsTo ptr_mut_write API",
        expected_fragments: &[
            "raw_ptr_mut_write_boundary",
            "unknown return type",
            "unsupported",
        ],
    },
    FailClosedCase {
        case: "raw_ptr_allocate_helper_currently_blocked",
        upstream_case: "allocate_in_bounds",
        local_blocker: "raw allocation helper/provenance token split",
        expected_fragments: &[
            "raw_ptr_allocate_boundary",
            "unknown return type",
            "unsupported",
        ],
    },
];

#[test]
fn raw_ptrs_rs_port_file_is_rust_syntax() {
    let source =
        std::fs::read_to_string(raw_ptrs_port_path()).expect("raw_ptrs port should be readable");
    syn::parse_file(&source).expect("raw_ptrs port should parse as ordinary Rust syntax");
}

#[test]
fn raw_ptrs_rs_pinned_upstream_case_shapes_are_present() {
    let path = pinned_upstream_raw_ptrs_path();
    if !path.exists() {
        eprintln!(
            "skipping pinned upstream raw_ptrs.rs shape check; missing {}",
            path.display()
        );
        return;
    }

    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", path.display()));
    for expected in [
        "#[test] basics",
        "fn test_mut_const_casts(x: *mut u8)",
        "fn test_addr_doesnt_imply_eq(x: *mut u8, y: *mut u8)",
        "fn test_view_does_imply_eq",
        "fn test_view_does_imply_eq_const",
        "fn test_null()",
        "fn test_manipulating(x: *mut u8, Tracked(pt): Tracked<PointsTo<u8>>)",
        "fn test_manipulating2(x: *mut u8, Tracked(pt): Tracked<PointsTo<u8>>)",
        "fn test_ptr_mut_write_different",
        "fn test_ptr_mut_read_different",
        "fn test_ptr_ref_different",
        "fn test_ptr_mut_read_uninit",
        "fn test_ptr_ref_uninit",
        "fn cast_test(x: *mut u8)",
        "fn cast_test2(x: *mut [u8])",
        "fn cast_test3(x: *mut [u64; 16])",
        "proof fn cast_proof_test",
        "fn test_strict_provenance(a: *mut u64)",
        "fn test_strict_provenance_const(a: *const u64)",
        "fn test_extensionality_sized<T>",
        "fn test_extensionality_unsized<T: ?Sized>",
        "#[test] pointer_cast_to_ints",
        "fn exec_test<T>(x: *mut T)",
        "fn exec_test_fails<T>(x: *mut T)",
        "fn exec_test_fails2<T>(x: *mut T)",
        "#[test] pointer_cast_slice_and_str",
        "fn test1(a: *mut [u8])",
        "fn test6(a: *const str)",
        "#[test] pointer_exec_eq_is_not_spec_eq",
        "#[test] points_to_move_error",
        "#[test] ptr_ref_lifetime_error",
        "#[test] compare_const_mut_pointers",
        "not_supported_int_to_ptr_cast",
        "not_supported_deref_ptr",
        "allocate_in_bounds",
        "assert_fails(err, 9)",
        "assert_fails(err, 4)",
        "assert_fails(err, 2)",
    ] {
        assert!(
            source.contains(expected),
            "pinned upstream raw_ptrs.rs should still contain {expected}"
        );
    }
}

#[test]
fn raw_ptrs_rs_expected_case_metadata_is_exact() {
    let source =
        std::fs::read_to_string(raw_ptrs_port_path()).expect("raw_ptrs port should be readable");
    let file =
        syn::parse_file(&source).expect("raw_ptrs port should parse as ordinary Rust syntax");

    for expected in [
        "RAW_PTRS_RS_EXPECTED_CASES",
        "raw_ptrs_rs_expected_cases",
        "RAW_PTRS_RS_EXPECTED_ERROR_PATTERNS",
        "raw_ptrs_rs_expected_error_patterns",
    ] {
        assert!(
            source.contains(expected),
            "raw_ptrs port metadata should contain {expected}"
        );
    }

    let metadata = metadata_entries(&file);
    assert_eq!(
        metadata,
        manifest_expected_metadata(),
        "raw_ptrs.rs manifest expected_cases should match port metadata and error patterns exactly"
    );

    let mut metadata_case_names = metadata
        .iter()
        .map(|case| case.case_id.as_str())
        .collect::<Vec<_>>();
    metadata_case_names.sort_unstable();
    let mut expected_case_names = EXPECTED_CASES
        .iter()
        .map(|case| case.case)
        .collect::<Vec<_>>();
    expected_case_names.sort_unstable();
    assert_eq!(
        expected_case_names, metadata_case_names,
        "every metadata case should have a regression expectation"
    );

    let metadata_error_cases = metadata
        .iter()
        .filter_map(|case| (case.expected_verdict == "error").then_some(case.case_id.as_str()))
        .collect::<Vec<_>>();
    let fragment_error_cases = FAIL_CLOSED_CASES
        .iter()
        .map(|case| case.case)
        .collect::<Vec<_>>();
    assert_eq!(
        fragment_error_cases, metadata_error_cases,
        "every metadata error case should have exact fail-closed fragments"
    );
}

#[test]
fn raw_ptrs_rs_verified_subset_verifies_from_file() {
    let path = raw_ptrs_port_path();

    for expected in EXPECTED_CASES
        .iter()
        .filter(|case| case.evidence_status == "verified")
    {
        let (result, obligations) =
            verify_case_with_obligations(&path, expected.case, expected.upstream_case);
        reject_unknown(&result, expected.case, expected.upstream_case);
        assert!(
            obligations >= expected.min_obligations,
            "{} ({}) should collect at least {} obligation(s), got {obligations}",
            expected.case,
            expected.upstream_case,
            expected.min_obligations
        );
        assert!(
            matches!(result, VerifyResult::Verified),
            "{} ({}) should verify, got: {result:?}",
            expected.case,
            expected.upstream_case
        );
    }
}

#[test]
fn raw_ptrs_rs_counterexample_subset_is_rejected_from_file() {
    let path = raw_ptrs_port_path();

    for expected in EXPECTED_CASES
        .iter()
        .filter(|case| case.evidence_status == "counterexample")
    {
        let (result, obligations) =
            verify_case_with_obligations(&path, expected.case, expected.upstream_case);
        reject_unknown(&result, expected.case, expected.upstream_case);
        eprintln!(
            "{} ({}) => {result:?}",
            expected.case, expected.upstream_case
        );
        assert!(
            obligations >= expected.min_obligations,
            "{} ({}) should collect at least {} obligation(s), got {obligations}",
            expected.case,
            expected.upstream_case,
            expected.min_obligations
        );
        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "{} ({}) should produce a counterexample, got: {result:?}",
            expected.case,
            expected.upstream_case
        );
    }
}

#[test]
fn raw_ptrs_rs_fail_closed_boundaries_from_file() {
    let path = raw_ptrs_port_path();
    let path = path.to_str().expect("raw_ptrs port path should be UTF-8");

    for fail_closed in FAIL_CLOSED_CASES {
        expect_fail_closed_error_contains_any(
            path,
            fail_closed.case,
            fail_closed.upstream_case,
            fail_closed.local_blocker,
            fail_closed.expected_fragments,
        );
    }
}
