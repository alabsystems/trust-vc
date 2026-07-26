// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Executable guards for the expanded upstream layout.rs TrustVc scout slice.
//!
//! These tests intentionally keep `source/rust_verify_test/tests/layout.rs`
//! as an unsupported gap. They prove only the Rust-valid subset TrustVc can
//! express today: associated integer constants, equality of `usize::BITS` and
//! `isize::BITS` target semantics, false pointer/layout probes, narrow Rust
//! `core::mem::size_of`/`align_of` primitive and pointer facts, and fail-closed
//! Verus-only/global-layout and user-struct layout boundaries.

mod common;

use std::{
    collections::{BTreeMap, BTreeSet},
    path::{Path, PathBuf},
};
use trust_vc_core::{
    extract_verification_conditions_with_file_context, parse_file_allow_tracked,
    verify_function_from_file, VerifyResult,
};

fn layout_port_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/ported/layout.rs")
}

fn verus_manifest_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/verus-tests.json")
}

fn pinned_upstream_layout_path() -> PathBuf {
    common::pinned_verus_test_path("layout.rs")
}

fn verify_case_with_obligations(
    path: &Path,
    case: &str,
    upstream_case: &str,
) -> (VerifyResult, usize) {
    let source = std::fs::read_to_string(path)
        .unwrap_or_else(|err| panic!("layout port should be readable: {err}"));
    let file =
        syn::parse_file(&source).unwrap_or_else(|err| panic!("layout port should parse: {err}"));
    let func = file
        .items
        .iter()
        .find_map(|item| match item {
            syn::Item::Fn(func) if func.sig.ident == case => Some(func),
            _ => None,
        })
        .unwrap_or_else(|| panic!("{case} ({upstream_case}) should exist in layout port"));

    let vc = extract_verification_conditions_with_file_context(&file, func)
        .unwrap_or_else(|err| panic!("{case} ({upstream_case}) should extract: {err}"));
    let obligations = vc.obligations().len();
    (vc.verify(), obligations)
}

fn expect_error(path: &str, case: &str, upstream_case: &str, expected_fragments: &[&str]) {
    let message = match verify_function_from_file(path, case) {
        Ok(VerifyResult::Error { message }) => message,
        Ok(result) => {
            panic!("{case} ({upstream_case}) should fail closed with Error, got: {result:?}")
        }
        Err(err) => err.to_string(),
    };

    for fragment in expected_fragments {
        assert!(
            message.contains(fragment),
            "{case} ({upstream_case}) error should contain {fragment:?}, got: {message}"
        );
    }
}

const VERIFIED_CASES: &[(&str, &str, usize)] = &[
    (
        "layout_integer_constants_and_target_bits_verified",
        "constants",
        1,
    ),
    (
        "layout_core_mem_size_of_primitives_verified",
        "test_layouts_for_primitives",
        1,
    ),
    (
        "layout_core_mem_size_of_word_and_arrays_verified",
        "test_size_of_1",
        1,
    ),
    (
        "layout_core_mem_align_of_primitives_verified",
        "test_layouts_for_primitives",
        1,
    ),
    (
        "layout_core_mem_pointer_layout_verified",
        "test_ptr_layout",
        1,
    ),
];

const COUNTEREXAMPLE_CASES: &[(&str, &str, usize)] = &[
    (
        "layout_pointer_width_sixteen_counterexample",
        "arch_fail_1",
        1,
    ),
    (
        "layout_core_mem_size_of_wrong_value_counterexample",
        "test_size_of_1",
        1,
    ),
    (
        "layout_core_mem_char_size_wrong_value_counterexample",
        "test_layouts_for_primitives",
        1,
    ),
    (
        "layout_core_mem_pointer_size_wrong_value_counterexample",
        "test_layouts_for_primitives",
        1,
    ),
    (
        "layout_core_mem_align_of_wrong_value_counterexample",
        "test_layouts_for_primitives",
        1,
    ),
];

const FAIL_CLOSED_CASES: &[(&str, &str, &[&str])] = &[
    (
        "layout_core_mem_repr_c_struct_size_currently_blocked",
        "test_layout_3",
        &["core::mem::size_of is only modeled"],
    ),
    (
        "layout_core_mem_repr_c_struct_align_currently_blocked",
        "test_layout_3",
        &["core::mem::align_of is only modeled"],
    ),
    (
        "layout_core_mem_generic_repr_c_struct_size_currently_blocked",
        "test_layout_6",
        &["core::mem::size_of is only modeled"],
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
        .unwrap_or_else(|| panic!("layout port should define {const_name}"));

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
    let array = referenced_array_const(file, "LAYOUT_RS_FAIL_CLOSED_ERROR_PATTERNS");
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
    let array = referenced_array_const(file, "LAYOUT_RS_EXPECTED_CASES");
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
            "duplicate layout metadata for {case_id}"
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
    let verified =
        VERIFIED_CASES.iter().map(
            |(case_id, upstream_case_id, min_obligations)| CaseMetadata {
                case_id: (*case_id).to_string(),
                upstream_case_id: (*upstream_case_id).to_string(),
                expected_verdict: "verified".to_string(),
                min_obligations: *min_obligations,
                expected_error_patterns: Vec::new(),
            },
        );
    let counterexamples =
        COUNTEREXAMPLE_CASES
            .iter()
            .map(
                |(case_id, upstream_case_id, min_obligations)| CaseMetadata {
                    case_id: (*case_id).to_string(),
                    upstream_case_id: (*upstream_case_id).to_string(),
                    expected_verdict: "counterexample".to_string(),
                    min_obligations: *min_obligations,
                    expected_error_patterns: Vec::new(),
                },
            );
    let errors = FAIL_CLOSED_CASES
        .iter()
        .map(
            |(case_id, upstream_case_id, expected_fragments)| CaseMetadata {
                case_id: (*case_id).to_string(),
                upstream_case_id: (*upstream_case_id).to_string(),
                expected_verdict: "error".to_string(),
                min_obligations: 0,
                expected_error_patterns: expected_fragments
                    .iter()
                    .map(|fragment| (*fragment).to_string())
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
            entry["upstream_path"].as_str() == Some("source/rust_verify_test/tests/layout.rs")
        })
        .expect("Verus manifest should contain layout.rs row");

    row["expected_cases"]
        .as_array()
        .expect("layout.rs row should contain expected_cases")
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
fn layout_rs_port_file_is_rust_syntax() {
    let source =
        std::fs::read_to_string(layout_port_path()).expect("layout port should be readable");
    syn::parse_file(&source).expect("layout port should parse as ordinary Rust syntax");
    assert!(
        source.contains("layout_rs_expected_cases")
            && source.contains("layout_rs_fail_closed_error_patterns"),
        "layout scout should carry manifest-ready expected case and error-pattern metadata"
    );
}

#[test]
fn layout_rs_pinned_upstream_case_shapes_are_present() {
    let path = pinned_upstream_layout_path();
    if !path.exists() {
        eprintln!(
            "skipping pinned upstream layout.rs shape check; missing {}",
            path.display()
        );
        return;
    }

    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", path.display()));
    for expected in [
        "#[test] test_with_no_flag",
        "fn constants()",
        "fn arch_fail_1()",
        "fn arch_fail_5()",
        "#[test] test_set_to_32",
        "#[test] test_set_to_64",
        "#[test] test_set_to_both_fail_1",
        "#[test] spec_only_unsigned_max",
        "#[test] spec_only_signed_min",
        "#[test] spec_only_arch_word_bits",
        "test_size_of_1",
        "test_size_of_4",
        "test_layout_1",
        "test_layout_3",
        "test_layout_6",
        "global layout S is size == 16, align == 8",
        "test_layouts_for_primitives",
        "proof fn test_ptr_layout<T>()",
        "proof fn test_ptr_layout_unsized<T: ?Sized>()",
        "test_cfg_global_layout_usize_64",
    ] {
        assert!(
            source.contains(expected),
            "pinned upstream layout.rs should still contain {expected}"
        );
    }
}

#[test]
fn layout_rs_expected_case_metadata_is_exact() {
    let source =
        std::fs::read_to_string(layout_port_path()).expect("layout port should be readable");
    let file = syn::parse_file(&source).expect("layout port should parse as ordinary Rust syntax");
    assert_eq!(metadata_entries(&file), expected_metadata());
}

#[test]
fn layout_rs_expected_case_metadata_matches_manifest() {
    let source =
        std::fs::read_to_string(layout_port_path()).expect("layout port should be readable");
    let file = syn::parse_file(&source).expect("layout port should parse as ordinary Rust syntax");
    assert_eq!(metadata_entries(&file), manifest_expected_metadata());
}

#[test]
fn layout_rs_verified_subset_verifies_from_file() {
    let path = layout_port_path();

    for (case, upstream_case, min_obligations) in VERIFIED_CASES {
        let (result, obligations) = verify_case_with_obligations(&path, case, upstream_case);
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
fn layout_rs_counterexample_subset_is_rejected_from_file() {
    let path = layout_port_path();

    for (case, upstream_case, min_obligations) in COUNTEREXAMPLE_CASES {
        let (result, obligations) = verify_case_with_obligations(&path, case, upstream_case);
        eprintln!("{case} ({upstream_case}) => {result:?}");
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
fn layout_rs_user_struct_layout_queries_fail_closed_from_file() {
    let path = layout_port_path();
    let path = path.to_str().expect("layout port path should be UTF-8");

    for (case, upstream_case, expected_fragments) in FAIL_CLOSED_CASES {
        expect_error(path, case, upstream_case, expected_fragments);
    }
}

#[test]
fn layout_rs_verus_global_layout_syntax_fails_closed() {
    for (source, upstream_case) in [
        (
            r#"
            global size_of usize == 8;

            fn test() {}
            "#,
            "test_size_of_1 global size_of declaration",
        ),
        (
            r#"
            #[repr(C)]
            struct S { v: u64 }

            global layout S is size == 8, align == 8;

            fn test() {}
            "#,
            "test_layout_1 global layout declaration",
        ),
        (
            r#"
            proof fn test() {
                assert(size_of::<u8>() == 1);
            }
            "#,
            "test_layouts_for_primitives proof fn/layout intrinsic syntax",
        ),
    ] {
        let err = match parse_file_allow_tracked(source) {
            Ok(_) => panic!("{upstream_case} Verus-only layout syntax should not parse as Rust"),
            Err(err) => err,
        };
        let message = err.to_string();
        assert!(
            !message.is_empty(),
            "{upstream_case} should fail closed with a parser diagnostic"
        );
    }
}
