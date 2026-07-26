// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Executable guards for the upstream exec_spec_verified.rs scout.
//!
//! These tests intentionally keep the upstream file as an unsupported gap. They
//! prove manually expressed generated-wrapper shapes over source spec
//! functions, reject false wrapper bodies, and pin the current fail-closed
//! boundary for executable helpers used as specification terms.

mod common;

use std::{
    collections::{BTreeMap, BTreeSet},
    path::{Path, PathBuf},
};
use trust_vc_core::{
    extract_verification_conditions_with_file_context, verify_function_from_file, VerifyResult,
};

fn exec_spec_verified_port_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/ported/exec_spec_verified.rs")
}

fn verus_manifest_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/verus-tests.json")
}

fn pinned_upstream_exec_spec_verified_path() -> PathBuf {
    common::pinned_verus_test_path("exec_spec_verified.rs")
}

fn port_obligation_count(case: &str, upstream_case: &str) -> usize {
    let path = exec_spec_verified_port_path();
    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|err| panic!("exec_spec_verified port should read: {err}"));
    let file = syn::parse_file(&source)
        .unwrap_or_else(|err| panic!("exec_spec_verified port should parse: {err}"));
    let func = file
        .items
        .iter()
        .find_map(|item| match item {
            syn::Item::Fn(func) if func.sig.ident == case => Some(func),
            _ => None,
        })
        .unwrap_or_else(|| panic!("{case} ({upstream_case}) should exist in port"));

    let vc = extract_verification_conditions_with_file_context(&file, func)
        .unwrap_or_else(|err| panic!("{case} ({upstream_case}) should extract: {err}"));
    vc.obligations().len()
}

fn verify_port_case(case: &str, upstream_case: &str) -> VerifyResult {
    let path = exec_spec_verified_port_path();
    let path = path
        .to_str()
        .expect("exec_spec_verified port path should be UTF-8");

    verify_function_from_file(path, case)
        .unwrap_or_else(|err| panic!("{case} ({upstream_case}) should extract: {err}"))
}

const EXPECTED_CASES: &[(&str, &str, &str, usize)] = &[
    (
        "exec_exec_spec_verified_id_u32",
        "test_exec_spec_typing_id_u32",
        "verified",
        1,
    ),
    ("exec_exec_spec_verified_literal_true", "", "verified", 1),
    ("exec_exec_spec_verified_literal_i32", "", "verified", 1),
    ("exec_exec_spec_verified_square_bounded", "", "verified", 1),
    ("exec_exec_spec_verified_usize_eq", "", "verified", 1),
    ("exec_exec_spec_verified_option_u8_eq", "", "verified", 1),
    (
        "exec_exec_spec_verified_constant_usize_max_minus",
        "",
        "verified",
        1,
    ),
    (
        "exec_exec_spec_verified_pred",
        "test_exec_spec_interop2_pred",
        "verified",
        1,
    ),
    (
        "exec_exec_spec_verified_literal_i32_wrong_counterexample",
        "",
        "counterexample",
        1,
    ),
    (
        "exec_exec_spec_verified_square_wrong_counterexample",
        "",
        "counterexample",
        1,
    ),
    (
        "exec_exec_spec_verified_constant_wrong_counterexample",
        "",
        "counterexample",
        1,
    ),
    (
        "exec_spec_verified_generated_u32_wrapper_caller_fails_closed",
        "test_exec_spec_typing_generated_wrapper_call",
        "verified",
        1,
    ),
    (
        "exec_spec_verified_generated_pred_wrapper_caller_fails_closed",
        "test_exec_spec_interop2_generated_wrapper_call",
        "verified",
        1,
    ),
    (
        "exec_spec_verified_exec_wrapper_in_contract_fails_closed",
        "test_exec_spec_verified_generated_exec_helper_as_spec_term",
        "error",
        0,
    ),
    (
        "exec_exec_spec_verified_struct_pred_fails_closed",
        "",
        "verified",
        1,
    ),
];

const VERIFIED_CASES: &[(&str, &str)] = &[
    (
        "exec_exec_spec_verified_id_u32",
        "test_exec_spec_typing_id_u32",
    ),
    ("exec_exec_spec_verified_literal_true", ""),
    ("exec_exec_spec_verified_literal_i32", ""),
    ("exec_exec_spec_verified_square_bounded", ""),
    ("exec_exec_spec_verified_usize_eq", ""),
    ("exec_exec_spec_verified_option_u8_eq", ""),
    ("exec_exec_spec_verified_constant_usize_max_minus", ""),
    (
        "exec_exec_spec_verified_pred",
        "test_exec_spec_interop2_pred",
    ),
    (
        "exec_spec_verified_generated_u32_wrapper_caller_fails_closed",
        "test_exec_spec_typing generated wrapper call-site (audited flip 2026-07-04: y != x twin CE'd at x=u32::MAX)",
    ),
    (
        "exec_spec_verified_generated_pred_wrapper_caller_fails_closed",
        "test_exec_spec_interop2 generated wrapper call-site (audited flip 2026-07-04: assert!(!res) twin non-Verified)",
    ),
    (
        "exec_exec_spec_verified_struct_pred_fails_closed",
        "struct-param wrapper conformance (audited flip 2026-07-04: >= body twin non-Verified)",
    ),
];

const COUNTEREXAMPLE_CASES: &[(&str, &str)] = &[
    (
        "exec_exec_spec_verified_literal_i32_wrong_counterexample",
        "",
    ),
    ("exec_exec_spec_verified_square_wrong_counterexample", ""),
    ("exec_exec_spec_verified_constant_wrong_counterexample", ""),
];

const FAIL_CLOSED_CASES: &[(&str, &str, &[&str])] = &[(
    "exec_spec_verified_exec_wrapper_in_contract_fails_closed",
    "test_exec_spec_verified_generated_exec_helper_as_spec_term",
    &["Unsupported call to sibling helper"],
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
        .unwrap_or_else(|| panic!("exec_spec_verified port should define {const_name}"));

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
    let array = referenced_array_const(file, "EXEC_SPEC_VERIFIED_RS_FAIL_CLOSED_ERROR_PATTERNS");
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
    let array = referenced_array_const(file, "EXEC_SPEC_VERIFIED_RS_EXPECTED_CASES");
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
            "duplicate exec_spec_verified metadata for {case_id}"
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
    let mut error_patterns = FAIL_CLOSED_CASES
        .iter()
        .map(|(case_id, _, patterns)| {
            (
                *case_id,
                patterns
                    .iter()
                    .map(|pattern| (*pattern).to_string())
                    .collect::<Vec<_>>(),
            )
        })
        .collect::<BTreeMap<_, _>>();

    EXPECTED_CASES
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
            entry["upstream_path"].as_str()
                == Some("source/rust_verify_test/tests/exec_spec_verified.rs")
        })
        .expect("Verus manifest should contain exec_spec_verified.rs row");

    row["expected_cases"]
        .as_array()
        .expect("exec_spec_verified.rs row should contain expected_cases")
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

#[test]
fn exec_spec_verified_rs_port_file_is_rust_syntax() {
    let source = std::fs::read_to_string(exec_spec_verified_port_path())
        .expect("exec_spec_verified port should be readable");
    syn::parse_file(&source).expect("exec_spec_verified port should parse as ordinary Rust syntax");
}

#[test]
fn exec_spec_verified_rs_pinned_upstream_case_shapes_are_present() {
    let path = pinned_upstream_exec_spec_verified_path();
    if !path.exists() {
        eprintln!(
            "skipping pinned upstream exec_spec_verified.rs shape check; missing {}",
            path.display()
        );
        return;
    }

    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", path.display()));
    for expected in [
        "#[test] test_exec_spec_typing",
        "spec fn id_u32",
        "#[test] test_exec_spec_literals",
        "spec fn test3() -> bool",
        "spec fn test4() -> i32",
        "#[test] test_exec_spec_arith",
        "spec fn square",
        "#[test] test_exec_spec_equality",
        "spec fn test_eq1",
        "spec fn test_eq13",
        "#[test] test_exec_spec_constant",
        "usize::MAX - i != 0",
        "#[test] test_exec_spec_interop2",
        "spec fn pred(a: A) -> bool",
    ] {
        assert!(
            source.contains(expected),
            "pinned upstream exec_spec_verified.rs should still contain {expected}"
        );
    }
}

#[test]
fn exec_spec_verified_rs_expected_case_metadata_is_exact() {
    let source = std::fs::read_to_string(exec_spec_verified_port_path())
        .expect("exec_spec_verified port should be readable");
    let file =
        syn::parse_file(&source).expect("exec_spec_verified port should parse as ordinary Rust");
    assert_eq!(metadata_entries(&file), expected_metadata());
    assert!(
        source.contains("exec_spec_verified_rs_expected_cases")
            && source.contains("exec_spec_verified_rs_fail_closed_error_patterns"),
        "exec_spec_verified port should export expected-case and error-pattern metadata"
    );
    assert_eq!(
        EXPECTED_CASES,
        &[
            (
                "exec_exec_spec_verified_id_u32",
                "test_exec_spec_typing_id_u32",
                "verified",
                1,
            ),
            ("exec_exec_spec_verified_literal_true", "", "verified", 1,),
            ("exec_exec_spec_verified_literal_i32", "", "verified", 1,),
            ("exec_exec_spec_verified_square_bounded", "", "verified", 1,),
            ("exec_exec_spec_verified_usize_eq", "", "verified", 1,),
            ("exec_exec_spec_verified_option_u8_eq", "", "verified", 1,),
            (
                "exec_exec_spec_verified_constant_usize_max_minus",
                "",
                "verified",
                1,
            ),
            (
                "exec_exec_spec_verified_pred",
                "test_exec_spec_interop2_pred",
                "verified",
                1,
            ),
            (
                "exec_exec_spec_verified_literal_i32_wrong_counterexample",
                "",
                "counterexample",
                1,
            ),
            (
                "exec_exec_spec_verified_square_wrong_counterexample",
                "",
                "counterexample",
                1,
            ),
            (
                "exec_exec_spec_verified_constant_wrong_counterexample",
                "",
                "counterexample",
                1,
            ),
            (
                "exec_spec_verified_generated_u32_wrapper_caller_fails_closed",
                "test_exec_spec_typing_generated_wrapper_call",
                "verified",
                1,
            ),
            (
                "exec_spec_verified_generated_pred_wrapper_caller_fails_closed",
                "test_exec_spec_interop2_generated_wrapper_call",
                "verified",
                1,
            ),
            (
                "exec_spec_verified_exec_wrapper_in_contract_fails_closed",
                "test_exec_spec_verified_generated_exec_helper_as_spec_term",
                "error",
                0,
            ),
            (
                "exec_exec_spec_verified_struct_pred_fails_closed",
                "",
                "verified",
                1,
            ),
        ]
    );
}

#[test]
fn exec_spec_verified_rs_expected_case_metadata_matches_manifest() {
    let source = std::fs::read_to_string(exec_spec_verified_port_path())
        .expect("exec_spec_verified port should be readable");
    let file =
        syn::parse_file(&source).expect("exec_spec_verified port should parse as ordinary Rust");
    assert_eq!(metadata_entries(&file), manifest_expected_metadata());
}

#[test]
fn exec_spec_verified_rs_generated_wrapper_subset_verifies_from_file() {
    for (case, upstream_case) in VERIFIED_CASES {
        let obligations = port_obligation_count(case, upstream_case);
        let result = verify_port_case(case, upstream_case);
        assert!(
            obligations >= 1,
            "{case} ({upstream_case}) should collect at least one obligation, got {obligations}"
        );
        assert!(
            matches!(result, VerifyResult::Verified),
            "{case} ({upstream_case}) should verify, got: {result:?}"
        );
    }
}

#[test]
fn exec_spec_verified_rs_generated_wrapper_counterexamples_are_rejected_from_file() {
    for (case, upstream_case) in COUNTEREXAMPLE_CASES {
        let obligations = port_obligation_count(case, upstream_case);
        let result = verify_port_case(case, upstream_case);
        assert!(
            obligations >= 1,
            "{case} ({upstream_case}) should collect at least one obligation, got {obligations}"
        );
        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "{case} ({upstream_case}) should be rejected, got: {result:?}"
        );
    }
}

#[test]
fn exec_spec_verified_rs_exec_helper_spec_term_fails_closed_from_file() {
    let path = exec_spec_verified_port_path();
    let path = path
        .to_str()
        .expect("exec_spec_verified port path should be UTF-8");

    for (case, upstream_case, expected_fragments) in FAIL_CLOSED_CASES {
        let message = match verify_function_from_file(path, case) {
            Ok(VerifyResult::Error { message }) => message,
            Ok(result) => {
                panic!("{case} ({upstream_case}) should fail closed with Error, got: {result:?}")
            }
            Err(err) => err.to_string(),
        };

        for expected_fragment in *expected_fragments {
            assert!(
                message.contains(expected_fragment),
                "{case} ({upstream_case}) error should contain {expected_fragment:?}, got: {message}"
            );
        }
    }
}
