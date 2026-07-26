// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Executable guards for the expanded upstream size_of.rs TrustVc scout slice.
//!
//! These tests intentionally keep `source/rust_verify_test/tests/size_of.rs`
//! as an unsupported gap. They prove only the Rust-valid subset TrustVc can
//! express today: word-layout witnesses, direct `core::mem::size_of`/`align_of`
//! primitive/reference/raw-pointer/array facts, stable false layout probes, and
//! fail-closed Verus layout intrinsic plus DST slice metadata, tuple,
//! user-struct, Box/Rc/Arc boundaries. Solver `Unknown` is rejected as
//! replacement evidence.

mod common;

use std::{
    collections::{BTreeMap, BTreeSet},
    path::{Path, PathBuf},
};
use trust_vc_core::{
    extract_verification_conditions_with_file_context, parse_file_allow_tracked,
    verify_function_from_file, VerifyResult,
};

type ExpectedCase = (&'static str, &'static str, &'static str, usize);

#[derive(Debug, Eq, PartialEq)]
struct CaseMetadata {
    case_id: String,
    upstream_case_id: String,
    status: String,
    min_obligations: usize,
    expected_error_patterns: Vec<String>,
}

fn size_of_port_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/ported/size_of.rs")
}

fn pinned_upstream_size_of_path() -> PathBuf {
    common::pinned_verus_test_path("size_of.rs")
}

fn verus_manifest_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/verus-tests.json")
}

fn port_source_and_ast() -> (String, syn::File) {
    let source =
        std::fs::read_to_string(size_of_port_path()).expect("size_of port should be readable");
    let ast = syn::parse_file(&source).expect("size_of port should parse as ordinary Rust syntax");
    (source, ast)
}

fn find_port_function<'a>(ast: &'a syn::File, case: &str, upstream_case: &str) -> &'a syn::ItemFn {
    ast.items
        .iter()
        .find_map(|item| match item {
            syn::Item::Fn(function) if function.sig.ident == case => Some(function),
            _ => None,
        })
        .unwrap_or_else(|| panic!("{case} ({upstream_case}) should exist in size_of port"))
}

fn verify_case_with_obligations(case: &str, upstream_case: &str) -> (VerifyResult, usize) {
    let (_source, ast) = port_source_and_ast();
    let function = find_port_function(&ast, case, upstream_case);
    let vc = extract_verification_conditions_with_file_context(&ast, function)
        .unwrap_or_else(|err| panic!("{case} ({upstream_case}) should extract: {err}"));
    let obligations = vc.obligations().len();
    (vc.verify(), obligations)
}

fn expect_fail_closed(path: &str, case: &str, upstream_case: &str, expected_fragments: &[&str]) {
    let message = match verify_function_from_file(path, case) {
        Ok(VerifyResult::Error { message }) => message,
        Ok(VerifyResult::Unknown { reason, .. }) => {
            panic!("{case} ({upstream_case}) returned solver Unknown, which is not stable evidence: {reason}")
        }
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

fn reject_unknown(result: &VerifyResult, case: &str, upstream_case: &str) {
    if let VerifyResult::Unknown { reason, .. } = result {
        panic!("{case} ({upstream_case}) returned solver Unknown, which is not stable evidence: {reason}");
    }
}

fn literal_string(expr: &syn::Expr) -> String {
    match expr {
        syn::Expr::Lit(syn::ExprLit {
            lit: syn::Lit::Str(lit),
            ..
        }) => lit.value(),
        _ => panic!("expected string literal in size_of metadata"),
    }
}

fn literal_usize(expr: &syn::Expr) -> usize {
    match expr {
        syn::Expr::Lit(syn::ExprLit {
            lit: syn::Lit::Int(lit),
            ..
        }) => lit
            .base10_parse::<usize>()
            .unwrap_or_else(|err| panic!("expected usize literal in size_of metadata: {err}")),
        _ => panic!("expected usize literal in size_of metadata"),
    }
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
        .unwrap_or_else(|| panic!("size_of port should define {const_name}"));

    let syn::Expr::Reference(reference) = const_item.expr.as_ref() else {
        panic!("{const_name} should be a referenced array");
    };
    let syn::Expr::Array(array) = reference.expr.as_ref() else {
        panic!("{const_name} should reference an array");
    };
    array.clone()
}

fn error_pattern_entries(file: &syn::File) -> BTreeMap<String, Vec<String>> {
    let array = referenced_array_const(file, "SIZE_OF_RS_EXPECTED_ERROR_PATTERNS");
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
    let array = referenced_array_const(file, "SIZE_OF_RS_EXPECTED_CASES");
    let mut error_patterns = error_pattern_entries(file);
    let mut seen = BTreeSet::new();

    let mut entries = Vec::new();
    for entry in &array.elems {
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
            "duplicate size_of metadata for {case_id}"
        );
        entries.push(CaseMetadata {
            expected_error_patterns: error_patterns.remove(&case_id).unwrap_or_default(),
            case_id,
            upstream_case_id: literal_string(&tuple.elems[1]),
            status: literal_string(&tuple.elems[2]),
            min_obligations: literal_usize(&tuple.elems[3]),
        });
    }

    assert!(
        error_patterns.is_empty(),
        "error-pattern metadata should not contain orphan cases: {error_patterns:?}"
    );
    entries
}

fn expected_metadata() -> Vec<CaseMetadata> {
    let mut error_patterns = BTreeMap::new();
    for (case, _, expected_fragments) in FAIL_CLOSED_CASES {
        assert!(
            error_patterns
                .insert(
                    *case,
                    expected_fragments
                        .iter()
                        .map(|fragment| (*fragment).to_string())
                        .collect::<Vec<_>>(),
                )
                .is_none(),
            "duplicate fail-closed metadata for {case}"
        );
    }

    EXPECTED_CASES
        .iter()
        .map(
            |(case_id, upstream_case_id, status, min_obligations)| CaseMetadata {
                case_id: (*case_id).to_string(),
                upstream_case_id: (*upstream_case_id).to_string(),
                status: (*status).to_string(),
                min_obligations: *min_obligations,
                expected_error_patterns: error_patterns.remove(case_id).unwrap_or_default(),
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
            entry["upstream_path"].as_str() == Some("source/rust_verify_test/tests/size_of.rs")
        })
        .expect("Verus manifest should contain size_of.rs row");

    row["expected_cases"]
        .as_array()
        .expect("size_of.rs row should contain expected_cases")
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

const EXPECTED_CASES: &[ExpectedCase] = &[
    (
        "size_of_word_layout_surrogate_verified",
        "sizeof_test_thin_pointer_reference_same_word_size",
        "verified",
        1,
    ),
    (
        "size_of_core_mem_primitive_sizes_verified",
        "sizeof_test",
        "verified",
        1,
    ),
    (
        "size_of_core_mem_array_sizes_verified",
        "sizeof_test",
        "verified",
        1,
    ),
    (
        "size_of_core_mem_thin_reference_verified",
        "sizeof_test",
        "verified",
        1,
    ),
    (
        "size_of_core_mem_raw_pointer_verified",
        "sizeof_test_pointer_layout_boundary",
        "verified",
        1,
    ),
    (
        "size_of_core_mem_align_of_primitives_verified",
        "sizeof_test",
        "verified",
        1,
    ),
    (
        "size_of_core_mem_array_align_of_verified",
        "sizeof_test",
        "verified",
        1,
    ),
    (
        "size_of_layout_record_witness_verified",
        "sizeof_test",
        "verified",
        1,
    ),
    (
        "size_of_word_layout_sixteen_bit_counterexample",
        "sizeof_test",
        "counterexample",
        1,
    ),
    (
        "size_of_core_mem_wrong_primitive_size_counterexample",
        "sizeof_test",
        "counterexample",
        1,
    ),
    (
        "size_of_core_mem_wrong_array_size_counterexample",
        "sizeof_test",
        "counterexample",
        1,
    ),
    (
        "size_of_core_mem_wrong_reference_size_counterexample",
        "sizeof_test_ref_distinguished_core_size_of_boundary",
        "counterexample",
        1,
    ),
    (
        "size_of_core_mem_wrong_raw_pointer_size_counterexample",
        "sizeof_test_false_raw_pointer_size_probe",
        "counterexample",
        1,
    ),
    (
        "size_of_core_mem_wrong_align_of_counterexample",
        "sizeof_test_false_alignment_probe",
        "counterexample",
        1,
    ),
    (
        "size_of_core_mem_wrong_array_align_counterexample",
        "sizeof_test",
        "counterexample",
        1,
    ),
    (
        "size_of_verus_layout_size_of_intrinsic_currently_blocked",
        "sizeof_test",
        "error",
        0,
    ),
    (
        "size_of_verus_layout_align_of_intrinsic_currently_blocked",
        "sizeof_test",
        "error",
        0,
    ),
    (
        "size_of_core_mem_tuple_layout_currently_blocked",
        "sizeof_test_tuple_wrong_concrete_tuple_layout_boundary",
        "error",
        0,
    ),
    (
        "size_of_core_mem_struct_layout_currently_blocked",
        "sized_trait_broadcast_concrete_user_struct_layout_boundary",
        "error",
        0,
    ),
    (
        "size_of_core_mem_tuple_align_currently_blocked",
        "sizeof_test_tuple_align_concrete_boundary",
        "error",
        0,
    ),
    (
        "size_of_core_mem_struct_align_currently_blocked",
        "sized_trait_broadcast_concrete_user_struct_align_boundary",
        "error",
        0,
    ),
    (
        "size_of_core_mem_box_rc_arc_layout_currently_blocked",
        "sizeof_test_box_rc_arc_distinguished_boundaries",
        "error",
        0,
    ),
    (
        "size_of_core_mem_slice_size_of_val_currently_blocked",
        "pointee_metadata",
        "error",
        0,
    ),
];

const FAIL_CLOSED_CASES: &[(&str, &str, &[&str])] = &[
    (
        "size_of_verus_layout_size_of_intrinsic_currently_blocked",
        "sizeof_test vstd::layout::size_of intrinsic boundary",
        &["unknown return type", "vstd::layout::size_of"],
    ),
    (
        "size_of_verus_layout_align_of_intrinsic_currently_blocked",
        "sizeof_test vstd::layout::align_of intrinsic boundary",
        &["unknown return type", "vstd::layout::align_of"],
    ),
    (
        "size_of_core_mem_tuple_layout_currently_blocked",
        "test_tuple_wrong concrete tuple layout boundary",
        &["core::mem::size_of is only modeled"],
    ),
    (
        "size_of_core_mem_struct_layout_currently_blocked",
        "sized_trait_broadcast concrete user-struct layout boundary",
        &["core::mem::size_of is only modeled"],
    ),
    (
        "size_of_core_mem_tuple_align_currently_blocked",
        "test_tuple_wrong concrete tuple align_of boundary",
        &["core::mem::align_of is only modeled"],
    ),
    (
        "size_of_core_mem_struct_align_currently_blocked",
        "sized_trait_broadcast concrete user-struct align_of boundary",
        &["core::mem::align_of is only modeled"],
    ),
    (
        "size_of_core_mem_box_rc_arc_layout_currently_blocked",
        "test_box_distinguished/test_rc_distinguished/test_arc_distinguished layout boundary",
        &["core::mem::size_of is only modeled"],
    ),
    (
        "size_of_core_mem_slice_size_of_val_currently_blocked",
        "pointee_metadata slice runtime-size boundary",
        &["unknown return type", "core::mem::size_of_val"],
    ),
];

#[test]
fn size_of_rs_port_file_is_rust_syntax() {
    let (source, _ast) = port_source_and_ast();
    assert!(
        source.contains("pub const SIZE_OF_RS_EXPECTED_CASES")
            && source.contains("size_of_rs_expected_cases")
            && source.contains("pub const SIZE_OF_RS_EXPECTED_ERROR_PATTERNS")
            && source.contains("size_of_rs_expected_error_patterns"),
        "size_of scout should carry manifest-ready expected case metadata helpers"
    );
}

#[test]
fn size_of_rs_pinned_upstream_case_shapes_are_present() {
    let path = pinned_upstream_size_of_path();
    if !path.exists() {
        eprintln!(
            "skipping pinned upstream size_of.rs shape check; missing {}",
            path.display()
        );
        return;
    }

    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", path.display()));
    assert_eq!(
        source.matches("test_verify_one_file!").count(),
        3,
        "pinned upstream size_of.rs should keep the three active harnesses"
    );
    assert_eq!(
        source.matches("assert_fails(err,").count(),
        3,
        "pinned upstream size_of.rs should keep one fail count per harness"
    );
    assert_eq!(
        source.matches("// FAILS").count(),
        26,
        "pinned upstream size_of.rs fail-marker count changed"
    );

    for expected in [
        "#[test] sizeof_test",
        "#[test] sized_trait_broadcast",
        "#[test] pointee_metadata",
        "fn test_unsized_wrong<V: ?Sized>()",
        "fn test_unsized_wrong2()",
        "fn test_unsized_wrong5<V: ?Sized>()",
        "fn test_unsized_wrong6()",
        "fn test_tuple_wrong<A, B>()",
        "fn test_ref_distinguished<A, B>()",
        "fn test_box_distinguished<A, B>()",
        "fn test_rc_distinguished<A, B>()",
        "fn test_arc_distinguished<A, B>()",
        "fn test_not_assumed_bounded<V>()",
        "fn test_not_assumed_bounded_align<V>()",
        "fn test_not_assumed_nonzero<V>()",
        "assert_fails(err, 12)",
        "assert_fails(err, 9)",
        "assert_fails(err, 2)",
        "pub broadcast proof fn is_sized_from_trait<T: Sized>()",
        "#[verifier::reject_recursive_types(B)]",
        "proof fn test_reference<T: ?Sized>()",
        "proof fn test_tuple_sized<T: Sized>()",
        "use core::ptr::Pointee;",
        "spec fn metatypefn<T: ?Sized>() -> int",
        "fn test_dst_struct<B: ?Sized>()",
    ] {
        assert!(
            source.contains(expected),
            "pinned upstream size_of.rs should still contain {expected}"
        );
    }
}

#[test]
fn size_of_rs_expected_case_metadata_is_exact_and_schema_valid() {
    let (_source, ast) = port_source_and_ast();
    let actual = metadata_entries(&ast);
    assert_eq!(
        actual,
        expected_metadata(),
        "size_of port metadata should exactly match the regression inventory"
    );

    for case in &actual {
        assert!(
            matches!(
                case.status.as_str(),
                "verified" | "counterexample" | "error"
            ),
            "{} ({}) has non-schema evidence status {}",
            case.case_id,
            case.upstream_case_id,
            case.status
        );
        assert_ne!(
            case.status.to_ascii_lowercase(),
            "unknown",
            "{} ({}) must not inventory Unknown as evidence",
            case.case_id,
            case.upstream_case_id
        );
    }

    for required_status in ["verified", "counterexample", "error"] {
        assert!(
            actual.iter().any(|case| case.status == required_status),
            "metadata should include at least one {required_status} case"
        );
    }

    let function_names = ast
        .items
        .iter()
        .filter_map(|item| match item {
            syn::Item::Fn(function) => Some(function.sig.ident.to_string()),
            _ => None,
        })
        .collect::<std::collections::BTreeSet<_>>();
    for case in &actual {
        assert!(
            function_names.contains(&case.case_id),
            "metadata case {} should name a function in size_of port",
            case.case_id
        );
    }

    let metadata_error_cases = EXPECTED_CASES
        .iter()
        .filter_map(|(case, _upstream_case, status, _min_obligations)| {
            (*status == "error").then_some(*case)
        })
        .collect::<Vec<_>>();
    let fragment_error_cases = FAIL_CLOSED_CASES
        .iter()
        .map(|(case, _upstream_case, _fragments)| *case)
        .collect::<Vec<_>>();
    assert_eq!(
        fragment_error_cases, metadata_error_cases,
        "every metadata error case should have exact fail-closed fragments"
    );
}

#[test]
fn size_of_rs_expected_case_metadata_matches_manifest() {
    let (_source, ast) = port_source_and_ast();
    assert_eq!(
        metadata_entries(&ast),
        manifest_expected_metadata(),
        "size_of.rs manifest expected_cases should match port metadata and error patterns exactly"
    );
}

#[test]
fn size_of_rs_verified_subset_verifies_from_file() {
    for &(case, upstream_case, _status, min_obligations) in
        EXPECTED_CASES.iter().filter(|case| case.2 == "verified")
    {
        let (result, obligations) = verify_case_with_obligations(case, upstream_case);
        reject_unknown(&result, case, upstream_case);
        assert!(
            obligations >= min_obligations,
            "{case} ({upstream_case}) should collect at least {min_obligations} obligation(s), got {obligations}"
        );
        assert!(
            matches!(result, VerifyResult::Verified),
            "{case} ({upstream_case}) should verify, got: {result:?}"
        );
    }
}

#[test]
fn size_of_rs_counterexamples_are_stable_from_file() {
    for &(case, upstream_case, _status, min_obligations) in EXPECTED_CASES
        .iter()
        .filter(|case| case.2 == "counterexample")
    {
        let (result, obligations) = verify_case_with_obligations(case, upstream_case);
        eprintln!("{case} ({upstream_case}) => {result:?}");
        reject_unknown(&result, case, upstream_case);
        assert!(
            obligations >= min_obligations,
            "{case} ({upstream_case}) should collect at least {min_obligations} obligation(s), got {obligations}"
        );
        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "{case} ({upstream_case}) should produce a counterexample, got: {result:?}"
        );
    }
}

#[test]
fn size_of_rs_layout_boundaries_fail_closed_from_file() {
    let path = size_of_port_path();
    let path = path.to_str().expect("size_of port path should be UTF-8");

    for (case, upstream_case, expected_fragments) in FAIL_CLOSED_CASES {
        expect_fail_closed(path, case, upstream_case, expected_fragments);
    }
}

#[test]
fn size_of_rs_verus_specific_size_layout_global_syntax_fails_closed() {
    for (source, upstream_case) in [
        (
            r#"
            global size_of usize == 8;

            fn test() {}
            "#,
            "sizeof_test global size_of declaration",
        ),
        (
            r#"
            #[repr(C)]
            struct S { v: u64 }

            global layout S is size == 8, align == 8;

            fn test() {}
            "#,
            "sizeof_test global layout declaration",
        ),
        (
            r#"
            proof fn test() {
                assert(size_of::<u8>() == 1);
            }
            "#,
            "sizeof_test proof fn size_of diagnostic boundary",
        ),
        (
            r#"
            spec fn test() -> int {
                align_of::<u8>()
            }
            "#,
            "sizeof_test spec fn align_of diagnostic boundary",
        ),
    ] {
        let err = match parse_file_allow_tracked(source) {
            Ok(_) => panic!("{upstream_case} Verus-only syntax should not parse as Rust"),
            Err(err) => err,
        };
        let message = err.to_string();
        assert!(
            !message.is_empty(),
            "{upstream_case} should fail closed with a parser diagnostic"
        );
    }
}
