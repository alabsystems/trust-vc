// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Executable guards for the upstream fndef_types.rs partial scout.
//!
//! These tests intentionally keep `source/rust_verify_test/tests/fndef_types.rs`
//! fail-closed in the corpus manifest. The port records supported direct exec
//! helper calls, one-, zero- and three-argument surrogates, generic helper calls,
//! trait-associated surrogates, SpecFn value-argument extensionality and value
//! calls, rejected false counterparts, a current-gap cycle-diagnostic witness,
//! pinned upstream shape checks, and
//! Rust-valid function-value calls/reflection surfaces that TrustVc does not
//! lower directly yet. Solver `Unknown` is rejected rather than counted as
//! evidence.

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

fn fndef_types_port_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/ported/fndef_types.rs")
}

fn pinned_upstream_fndef_types_path() -> PathBuf {
    common::pinned_verus_test_path("fndef_types.rs")
}

fn verus_manifest_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/verus-tests.json")
}

fn port_file() -> syn::File {
    let source =
        std::fs::read_to_string(fndef_types_port_path()).expect("fndef_types port should be read");
    syn::parse_file(&source).expect("fndef_types port should parse as ordinary Rust syntax")
}

fn port_function<'a>(file: &'a syn::File, case: &str, upstream_case: &str) -> &'a syn::ItemFn {
    file.items
        .iter()
        .find_map(|item| match item {
            syn::Item::Fn(function) if function.sig.ident == case => Some(function),
            _ => None,
        })
        .unwrap_or_else(|| panic!("{case} ({upstream_case}) should exist in fndef_types port"))
}

fn verify_case_with_obligations(case: &str, upstream_case: &str) -> (VerifyResult, usize) {
    let file = port_file();
    let function = port_function(&file, case, upstream_case);
    let vc = extract_verification_conditions_with_file_context(&file, function)
        .unwrap_or_else(|err| panic!("{case} ({upstream_case}) should extract VCs: {err}"));
    let obligations = vc.obligations().len();
    let path = fndef_types_port_path();
    let path = path
        .to_str()
        .expect("fndef_types port path should be UTF-8");
    let result = verify_function_from_file(path, case)
        .unwrap_or_else(|err| panic!("{case} ({upstream_case}) should verify from file: {err}"));

    (result, obligations)
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
        Ok(VerifyResult::Error { message }) => message,
        Ok(VerifyResult::Unknown { reason, .. }) => {
            panic!("{case} ({upstream_case}) returned solver Unknown, not stable fail-closed evidence: {reason}")
        }
        Ok(other) => {
            panic!("{case} ({upstream_case}) should fail closed with Error, got: {other:?}")
        }
        Err(err) => err.to_string(),
    }
}

fn string_lit(expr: &syn::Expr) -> String {
    match expr {
        syn::Expr::Lit(syn::ExprLit {
            lit: syn::Lit::Str(value),
            ..
        }) => value.value(),
        _ => panic!("expected string literal in fndef_types metadata"),
    }
}

fn usize_lit(expr: &syn::Expr) -> usize {
    match expr {
        syn::Expr::Lit(syn::ExprLit {
            lit: syn::Lit::Int(value),
            ..
        }) => value
            .base10_parse::<usize>()
            .expect("metadata obligation count should parse as usize"),
        _ => panic!("expected usize literal in fndef_types metadata"),
    }
}

fn referenced_array<'a>(expr: &'a syn::Expr, const_name: &str) -> &'a syn::ExprArray {
    match expr {
        syn::Expr::Reference(reference) => match reference.expr.as_ref() {
            syn::Expr::Array(array) => array,
            _ => panic!("{const_name} should reference an array literal"),
        },
        _ => panic!("{const_name} should be an array reference"),
    }
}

fn port_const_array<'a>(file: &'a syn::File, const_name: &str) -> &'a syn::ExprArray {
    let expr = file
        .items
        .iter()
        .find_map(|item| match item {
            syn::Item::Const(item) if item.ident == const_name => Some(item.expr.as_ref()),
            _ => None,
        })
        .unwrap_or_else(|| panic!("fndef_types port should define {const_name}"));
    referenced_array(expr, const_name)
}

fn string_slice(expr: &syn::Expr) -> Vec<String> {
    let syn::Expr::Reference(reference) = expr else {
        panic!("expected referenced fndef_types string-slice metadata");
    };
    let syn::Expr::Array(array) = reference.expr.as_ref() else {
        panic!("expected fndef_types string-slice array metadata");
    };

    array.elems.iter().map(string_lit).collect()
}

fn error_pattern_entries(file: &syn::File) -> BTreeMap<String, Vec<String>> {
    let mut entries = BTreeMap::new();
    for entry in &port_const_array(file, "FNDEF_TYPES_RS_EXPECTED_ERROR_PATTERNS").elems {
        let syn::Expr::Tuple(tuple) = entry else {
            panic!("expected tuple fndef_types error-pattern metadata entry");
        };
        assert_eq!(
            tuple.elems.len(),
            2,
            "fndef_types error-pattern metadata should contain case and fragments"
        );
        let case_id = string_lit(&tuple.elems[0]);
        let patterns = string_slice(&tuple.elems[1]);
        assert!(
            entries.insert(case_id.clone(), patterns).is_none(),
            "duplicate fndef_types error-pattern metadata for {case_id}"
        );
    }

    entries
}

fn metadata_entries(file: &syn::File) -> Vec<CaseMetadata> {
    let mut error_patterns = error_pattern_entries(file);
    let mut seen = BTreeSet::new();
    let mut entries = Vec::new();

    for entry in &port_const_array(file, "FNDEF_TYPES_RS_EXPECTED_CASES").elems {
        let syn::Expr::Tuple(tuple) = entry else {
            panic!("expected tuple fndef_types case metadata entry");
        };
        assert_eq!(
            tuple.elems.len(),
            4,
            "fndef_types case metadata should contain case, upstream case, verdict, and min obligations"
        );
        let case_id = string_lit(&tuple.elems[0]);
        assert!(
            seen.insert(case_id.clone()),
            "duplicate fndef_types case metadata for {case_id}"
        );
        let expected_error_patterns = error_patterns.remove(&case_id).unwrap_or_default();
        entries.push(CaseMetadata {
            case_id,
            upstream_case_id: string_lit(&tuple.elems[1]),
            expected_verdict: string_lit(&tuple.elems[2]),
            min_obligations: usize_lit(&tuple.elems[3]),
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
            entry["upstream_path"].as_str() == Some("source/rust_verify_test/tests/fndef_types.rs")
        })
        .expect("Verus manifest should contain fndef_types.rs row");

    row["expected_cases"]
        .as_array()
        .expect("fndef_types manifest row should contain expected_cases")
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
            expected_error_patterns: case["expected_error_patterns"]
                .as_array()
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

fn expected_case(case: &str) -> CaseMetadata {
    metadata_entries(&port_file())
        .into_iter()
        .find(|metadata| metadata.case_id == case)
        .unwrap_or_else(|| panic!("{case} should exist in expected metadata"))
}

const VERIFIED_CASES: &[(&str, &str, usize)] = &[
    (
        "direct_exec_function_contract_verified",
        "basic_test::test direct llama calls",
        1,
    ),
    (
        "direct_exec_zero_arg_contract_verified",
        "exec_calling2 direct zero-argument helper call",
        1,
    ),
    (
        "direct_exec_three_arg_contract_verified",
        "generics_test::test concrete three-argument llama surrogate",
        1,
    ),
    (
        "generic_helper_direct_contract_verified",
        "generic_conditions_for_normal_call direct generic helper postcondition",
        1,
    ),
    (
        "spec_fn_value_argument_extensional_verified",
        "basic_test::test_take1 SpecFn extensional surrogate",
        1,
    ),
    (
        "spec_fn_value_call_reflexive_verified",
        "basic_test::takes_fn1 SpecFn value-call reflexive surrogate",
        1,
    ),
    (
        "one_arg_plain_function_item_value_call_verified",
        "exec_calling1 first-class one-argument function item call",
        1,
    ),
    (
        "mutual_exec_function_item_cycle_diagnostic_current_gap_verified",
        "exec_recursion_mutual missing cyclic dependency diagnostic",
        1,
    ),
];

const COUNTEREXAMPLE_CASES: &[(&str, &str, usize)] = &[
    (
        "direct_exec_function_bad_ensures_counterexample",
        "basic_test::test2 false llama result assertion",
        1,
    ),
    (
        "direct_exec_function_bad_requires_counterexample",
        "basic_test::test3 invalid llama precondition surrogate",
        1,
    ),
    (
        "direct_exec_zero_arg_bad_ensures_counterexample",
        "exec_calling2 false zero-argument helper result assertion",
        1,
    ),
    (
        "direct_exec_three_arg_bad_ensures_counterexample",
        "generics_test::test2 false three-argument result assertion",
        1,
    ),
    (
        "direct_exec_three_arg_bad_requires_counterexample",
        "generics_test::test3 invalid three-argument precondition surrogate",
        1,
    ),
    (
        "generic_helper_bad_ensures_counterexample",
        "generic_conditions_for_normal_call false generic helper post-use assertion",
        1,
    ),
    (
        "spec_fn_value_call_wrong_counterexample",
        "basic_test::takes_fn3 SpecFn value-call false assertion surrogate",
        1,
    ),
];

const FAIL_CLOSED_CASES: &[(&str, &str, &[&str])] = &[
    (
        "trait_associated_function_contract_currently_errors",
        "with_trait",
        &[
            "unknown return type for function 'FndefTraitWitness::fndef_trait_llama'",
            "fndef_trait_llama",
            "trait-associated",
        ],
    ),
    (
        "trait_associated_function_bad_ensures_currently_errors",
        "with_trait",
        &[
            "unknown return type for function 'FndefTraitWitness::fndef_trait_llama'",
            "fndef_trait_llama",
            "trait-associated",
        ],
    ),
    (
        "trait_associated_function_bad_requires_currently_errors",
        "with_trait",
        &[
            "unknown return type for function 'FndefTraitWitness::fndef_trait_llama'",
            "fndef_trait_llama",
            "trait-associated",
        ],
    ),
    (
        "exec_function_item_value_call_currently_errors",
        "basic_test",
        &[
            "unknown return type for function 't'",
            "function-item value",
            "function value",
        ],
    ),
    (
        "exec_function_item_value_bad_ensures_currently_errors",
        "basic_test",
        &[
            "unknown return type for function 't'",
            "function-item value",
            "function value",
        ],
    ),
    (
        "exec_function_item_value_bad_requires_currently_errors",
        "basic_test",
        &[
            "unknown return type for function 't'",
            "function-item value",
            "function value",
        ],
    ),
    (
        "zero_arg_function_item_value_call_currently_errors",
        "exec_calling2",
        &[
            "unknown return type for function 't'",
            "function-item value",
            "function value",
        ],
    ),
    (
        "generic_function_item_value_call_currently_errors",
        "generics_test",
        &[
            "unknown return type for function 't'",
            "function-item value",
            "function value",
        ],
    ),
    (
        "generic_function_item_value_bad_ensures_currently_errors",
        "generics_test",
        &[
            "unknown return type for function 't'",
            "function-item value",
            "function value",
        ],
    ),
    (
        "trait_method_function_item_value_call_currently_errors",
        "with_trait",
        &[
            "unknown return type for function 't'",
            "function-item value",
            "function value",
            "fndef_trait_llama",
        ],
    ),
    (
        "fn_trait_bound_value_call_currently_errors",
        "basic_test",
        &[
            "Undefined function: f",
            "unknown return type for function 'f'",
            "Fn(u8) -> bool",
            "function value",
        ],
    ),
    (
        "fn_once_trait_bound_value_call_currently_errors",
        "recursion6_via_fn_once",
        &[
            "Undefined function: f",
            "unknown return type for function 'f'",
            "FnOnce",
            "function value",
        ],
    ),
    (
        "fn_mut_trait_bound_value_call_currently_errors",
        "recursion11_via_fn_mut",
        &[
            "Undefined function: f",
            "unknown return type for function 'f'",
            "FnMut",
            "function value",
        ],
    ),
    (
        "mut_param_function_item_value_currently_errors",
        "mut_params_error",
        &[
            "mutable reference",
            "&mut",
            "unknown return type for function 't'",
            "function value",
        ],
    ),
    (
        "function_item_requires_reflection_currently_errors",
        "basic_test",
        &[
            "unresolved variable",
            "requires",
            "method",
            "function-item value",
            "function value",
        ],
    ),
    (
        "function_item_ensures_reflection_currently_errors",
        "basic_test",
        &[
            "unresolved variable",
            "ensures",
            "method",
            "function-item value",
            "function value",
        ],
    ),
    (
        "datatype_constructor_function_value_currently_errors",
        "unit_struct_as_fn_not_supported",
        &[
            "unknown return type for function 'make'",
            "datatype constructor",
            "constructor",
            "function value",
        ],
    ),
    (
        "function_item_reference_value_call_currently_errors",
        "recursion9_via_fn_once_with_ref",
        &[
            "unknown return type for function 't'",
            "function-item value",
            "function value",
            "reference",
        ],
    ),
];

#[test]
fn fndef_types_rs_port_file_is_rust_syntax() {
    let source =
        std::fs::read_to_string(fndef_types_port_path()).expect("fndef_types port should be read");
    syn::parse_file(&source).expect("fndef_types port should parse as ordinary Rust syntax");
}

#[test]
fn fndef_types_rs_pinned_upstream_case_shapes_are_present() {
    let path = pinned_upstream_fndef_types_path();
    if !path.exists() {
        eprintln!(
            "skipping pinned upstream fndef_types.rs shape check; missing {}",
            path.display()
        );
        return;
    }

    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", path.display()));
    for expected in [
        "#[test] basic_test",
        "fn llama(x: u8) -> (b: bool)",
        "fn takes_fn1<F: Fn(u8) -> bool>(f: F)",
        "fn test2()",
        "fn test4()",
        "fn test5()",
        "#[test] generics_test",
        "fn llama<T>(x: T, y: T, z: T) -> (b: bool)",
        "fn takes_fn4<T, F: Fn(T, T, T) -> bool>(f: F)",
        "#[test] with_trait",
        "let t = <X as Tr>::llama;",
        "#[test] mut_params_error",
        "#[test] recursion6_via_fn_once",
        "#[test] recursion11_via_fn_mut",
        "#[test] recursion9_via_fn_once_with_ref",
        "#[test] exec_calling2",
        "x();",
        "#[test] exec_calling1",
        "x(0);",
        "#[test] exec_recursion_mutual",
        "let y = a;",
        "#[test] generic_conditions_for_normal_call",
        "#[test] zero_arg_fn_issue2296",
        "#[test] unit_struct_as_fn_not_supported",
    ] {
        assert!(
            source.contains(expected),
            "pinned upstream fndef_types.rs should still contain {expected}"
        );
    }
}

#[test]
fn fndef_types_rs_expected_case_metadata_matches_manifest() {
    let file = port_file();
    let source =
        std::fs::read_to_string(fndef_types_port_path()).expect("fndef_types port should be read");
    assert!(
        source.contains("pub const FNDEF_TYPES_RS_EXPECTED_CASES")
            && source.contains("pub fn fndef_types_rs_expected_cases")
            && source.contains("pub const FNDEF_TYPES_RS_EXPECTED_ERROR_PATTERNS")
            && source.contains("pub fn fndef_types_rs_expected_error_patterns"),
        "fndef_types port should expose manifest-ready expected-case and error-pattern metadata helpers"
    );

    assert_eq!(
        metadata_entries(&file),
        manifest_expected_metadata(),
        "fndef_types manifest expected_cases should match port metadata and error patterns exactly"
    );

    for allowed_status in ["verified", "counterexample", "error"] {
        assert!(
            metadata_entries(&file)
                .iter()
                .any(|metadata| metadata.expected_verdict == allowed_status),
            "metadata should include at least one {allowed_status} case"
        );
    }

    for metadata in metadata_entries(&file) {
        assert!(
            matches!(
                metadata.expected_verdict.as_str(),
                "verified" | "counterexample" | "error"
            ),
            "{} ({}) has schema-invalid status {}",
            metadata.case_id,
            metadata.upstream_case_id,
            metadata.expected_verdict
        );
        assert_ne!(
            metadata.expected_verdict, "unknown",
            "{} ({}) must not use Unknown as expected evidence",
            metadata.case_id, metadata.upstream_case_id
        );
        match metadata.expected_verdict.as_str() {
            "verified" | "counterexample" => assert!(
                metadata.min_obligations >= 1,
                "{} ({}) should record at least one obligation",
                metadata.case_id,
                metadata.upstream_case_id
            ),
            "error" => assert_eq!(
                metadata.min_obligations, 0,
                "{} ({}) error metadata should record zero obligations",
                metadata.case_id, metadata.upstream_case_id
            ),
            _ => unreachable!(),
        }
    }
}

#[test]
fn fndef_types_rs_verified_subset_verifies_from_file() {
    for (case, upstream_case, min_obligations) in VERIFIED_CASES {
        let (result, obligations) = verify_case_with_obligations(case, upstream_case);
        reject_unknown(&result, case, upstream_case);
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
fn fndef_types_rs_counterexample_subset_is_rejected_from_file() {
    for (case, upstream_case, min_obligations) in COUNTEREXAMPLE_CASES {
        let (result, obligations) = verify_case_with_obligations(case, upstream_case);
        reject_unknown(&result, case, upstream_case);
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
fn fndef_types_rs_unsupported_function_value_boundaries_fail_closed_from_file() {
    let path = fndef_types_port_path();
    let path = path
        .to_str()
        .expect("fndef_types port path should be UTF-8");

    let metadata = metadata_entries(&port_file());
    let metadata_error_cases = metadata
        .iter()
        .filter_map(|metadata| {
            (metadata.expected_verdict == "error").then_some(metadata.case_id.as_str())
        })
        .collect::<Vec<_>>();
    let fragment_error_cases = FAIL_CLOSED_CASES
        .iter()
        .map(|(case, _, _)| *case)
        .collect::<Vec<_>>();
    assert_eq!(
        fragment_error_cases, metadata_error_cases,
        "every metadata error case should have exact fail-closed fragments"
    );

    for (case, upstream_case, expected_fragments) in FAIL_CLOSED_CASES {
        let metadata = expected_case(case);
        assert_eq!(*upstream_case, metadata.upstream_case_id);
        assert_eq!(metadata.expected_verdict, "error");
        assert_eq!(metadata.min_obligations, 0);
        assert_eq!(
            expected_fragments
                .iter()
                .map(|fragment| (*fragment).to_string())
                .collect::<Vec<_>>(),
            metadata.expected_error_patterns,
            "{case} ({upstream_case}) should use manifest-pinned fail-closed fragments"
        );
        assert!(
            !expected_fragments.is_empty(),
            "{case} ({upstream_case}) should pin at least one fail-closed diagnostic fragment"
        );
        let message = fail_closed_message(path, case, upstream_case);
        assert!(
            expected_fragments
                .iter()
                .any(|expected_fragment| message.contains(expected_fragment)),
            "{case} ({upstream_case}) should fail closed with one of {expected_fragments:?}, got: {message}"
        );
    }
}
