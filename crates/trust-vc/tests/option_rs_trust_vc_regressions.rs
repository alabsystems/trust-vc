// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Executable guards for the active pinned upstream option.rs harnesses.
//!
//! The file-backed checks cover the Rust-valid combinator outcomes. The
//! macro-collected helpers retain focused closure-contract positive and
//! negative regressions while direct source extraction incrementally accepts
//! guarded `trust_vc::closure!` Option combinator cases.

mod common;

use std::{collections::BTreeSet, path::PathBuf};
use trust_vc_core::{verify_function_from_file, VerifyResult};

fn option_port_path() -> PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/ported/option.rs")
}

fn verus_manifest_path() -> PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/verus-tests.json")
}

fn option_regression_path() -> PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/option_rs_trust_vc_regressions.rs")
}

const FILE_VERIFIED_CASES: &[(&str, &str)] = &[
    ("test_unwrap_expect", "test_unwrap_expect"),
    ("test_ok_or_else", "test_ok_or_else"),
    ("test_unwrap_or_default", "test_unwrap_or_default"),
    ("test_and_then", "test_and_then"),
    ("test_cloned", "test_cloned"),
    ("test_unwrap_or_else", "test_unwrap_or_else"),
];

#[derive(Debug, Eq, PartialEq)]
struct CaseMetadata {
    case_id: String,
    upstream_case_id: String,
    expected_verdict: String,
    min_obligations: usize,
}

fn referenced_array_const(file: &syn::File, const_name: &str) -> syn::ExprArray {
    let const_item = file
        .items
        .iter()
        .find_map(|item| match item {
            syn::Item::Const(item) if item.ident == const_name => Some(item),
            _ => None,
        })
        .unwrap_or_else(|| panic!("option port should define {const_name}"));

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

fn metadata_entries(file: &syn::File) -> Vec<CaseMetadata> {
    let array = referenced_array_const(file, "OPTION_RS_EXPECTED_CASES");
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
            "duplicate option metadata for {case_id}"
        );
        entries.push(CaseMetadata {
            case_id,
            upstream_case_id: literal_string(&tuple.elems[1]),
            expected_verdict: literal_string(&tuple.elems[2]),
            min_obligations: literal_usize(&tuple.elems[3]),
        });
    }

    entries
}

fn expected_metadata() -> Vec<CaseMetadata> {
    FILE_VERIFIED_CASES
        .iter()
        .map(|(case_id, upstream_case_id)| CaseMetadata {
            case_id: (*case_id).to_string(),
            upstream_case_id: (*upstream_case_id).to_string(),
            expected_verdict: "verified".to_string(),
            min_obligations: 1,
        })
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
            entry["upstream_path"].as_str() == Some("source/rust_verify_test/tests/option.rs")
        })
        .expect("Verus manifest should contain option.rs row");

    row["expected_cases"]
        .as_array()
        .expect("option.rs row should contain expected_cases")
        .iter()
        .map(|entry| {
            assert!(
                entry.get("expected_error_patterns").is_none(),
                "option.rs manifest evidence should not carry error-pattern metadata"
            );
            CaseMetadata {
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
            }
        })
        .collect()
}

const DIRECT_SOURCE_CLOSURE_CONTRACT_CASES: &[&str] = &[
    "option_ok_or_else_contract_closure_requires_ensures",
    "option_ok_or_else_contract_closure_upstream_shape",
    "option_ok_or_else_contract_closure_skips_uncalled_postcondition",
    "option_ok_or_else_contract_closure_skips_uncalled_precondition",
    "option_and_then_contract_closure_precondition",
    "option_and_then_contract_closure_upstream_shape",
    "option_and_then_contract_closure_skips_uncalled_contracts",
    "option_unwrap_or_else_contract_closure_requires_ensures",
    "option_unwrap_or_else_contract_closure_upstream_shape",
    "option_unwrap_or_else_contract_closure_skips_uncalled_contracts",
];

fn trust_vc_evidence_case_attr_name(attr: &syn::Attribute) -> Option<String> {
    let segments = attr
        .path()
        .segments
        .iter()
        .map(|segment| segment.ident.to_string())
        .collect::<Vec<_>>();
    let name = match segments.as_slice() {
        [name] => name,
        [prefix, name] if prefix == "trust_vc" => name,
        _ => return None,
    };
    if matches!(
        name.as_str(),
        "requires"
            | "ensures"
            | "recommends"
            | "returns"
            | "proof"
            | "external"
            | "external_body"
            | "contract"
            | "trait_spec"
            | "trait_impl"
            | "spec_mode"
            | "memoize"
            | "opens_invariants"
            | "via_fn"
            | "protocol"
            | "action"
            | "safety"
            | "liveness"
    ) {
        Some(name.clone())
    } else {
        None
    }
}

fn option_ok_or_else_contract_closure_requires_ensures() {
    let opt: Option<u32> = None;
    let res: Result<u32, u32> = opt.ok_or_else(trust_vc::closure!(
        || -> u32
        requires(true)
        ensures(|r: u32| r == 99u32)
        99u32
    ));
    assert_eq!(res, Err::<u32, u32>(99u32));
}

fn option_ok_or_else_contract_closure_upstream_shape() {
    let some: Option<u32> = Some(42u32);
    let some_res: Result<u32, u32> = some.ok_or_else(trust_vc::closure!(
        || -> u32
        ensures(|r: u32| r == 99u32)
        99u32
    ));
    assert_eq!(some_res, Ok::<u32, u32>(42u32));

    let none: Option<u32> = None;
    let none_res: Result<u32, u32> = none.ok_or_else(trust_vc::closure!(
        || -> u32
        ensures(|r: u32| r == 99u32)
        99u32
    ));
    assert_eq!(none_res, Err::<u32, u32>(99u32));
}

fn option_ok_or_else_contract_closure_skips_uncalled_postcondition() {
    let some: Option<u32> = Some(42u32);
    let some_res: Result<u32, u32> = some.ok_or_else(trust_vc::closure!(
        || -> u32
        ensures(|r: u32| r == 100u32)
        99u32
    ));
    assert_eq!(some_res, Ok::<u32, u32>(42u32));

    let none: Option<u32> = None;
    let none_res: Result<u32, u32> = none.ok_or_else(trust_vc::closure!(
        || -> u32
        ensures(|r: u32| r == 99u32)
        99u32
    ));
    assert_eq!(none_res, Err::<u32, u32>(99u32));
}

#[allow(dead_code)]
fn option_ok_or_else_contract_closure_skips_uncalled_precondition() {
    let some: Option<u32> = Some(42u32);
    let some_res: Result<u32, u32> = some.ok_or_else(trust_vc::closure!(
        || -> u32
        requires(false)
        99u32
    ));
    assert_eq!(some_res, Ok::<u32, u32>(42u32));
}

fn option_ok_or_else_contract_closure_wrong_err_counterexample() {
    let opt: Option<u32> = None;
    let res: Result<u32, u32> = opt.ok_or_else(trust_vc::closure!(
        || -> u32
        ensures(|r: u32| r == 100u32)
        99u32
    ));
    assert_eq!(res, Err::<u32, u32>(99u32));
}

#[allow(dead_code)]
fn option_ok_or_else_contract_closure_bad_precondition_counterexample() {
    let opt: Option<u32> = None;
    let res: Result<u32, u32> = opt.ok_or_else(trust_vc::closure!(
        || -> u32
        requires(false)
        99u32
    ));
    assert_eq!(res, Err::<u32, u32>(99u32));
}

fn option_and_then_contract_closure_precondition() {
    let opt: Option<u32> = Some(2u32);
    let res: Option<u32> = opt.and_then(trust_vc::closure!(
        |x: u32| -> Option<u32>
        requires(x < 1000u32)
        ensures(|r: Option<u32>| r == Option::<u32>::Some(x + 1u32))
        Option::<u32>::Some(x + 1u32)
    ));
    assert_eq!(res, Option::<u32>::Some(3u32));

    let none: Option<u32> = None;
    let none_res: Option<u32> = none.and_then(trust_vc::closure!(
        |x: u32| -> Option<u32>
        requires(x < 1000u32)
        ensures(|r: Option<u32>| r == Option::<u32>::Some(x + 1u32))
        Option::<u32>::Some(x + 1u32)
    ));
    assert_eq!(none_res, Option::<u32>::None);
}

fn option_and_then_contract_closure_upstream_shape() {
    let opt: Option<u32> = Some(2u32);
    let res: Option<u32> = opt.and_then(trust_vc::closure!(
        |x: u32| -> Option<u32>
        requires(x < 1000u32)
        ensures(|r: Option<u32>| r.is_some() && r.unwrap() == x + 1u32)
        Option::<u32>::Some(x + 1u32)
    ));
    assert_eq!(res, Option::<u32>::Some(3u32));

    let none: Option<u32> = None;
    let none_res: Option<u32> = none.and_then(trust_vc::closure!(
        |x: u32| -> Option<u32>
        requires(x < 1000u32)
        ensures(|r: Option<u32>| r.is_some() && r.unwrap() == x + 1u32)
        Option::<u32>::Some(x + 1u32)
    ));
    assert_eq!(none_res, Option::<u32>::None);
}

#[allow(dead_code)]
fn option_and_then_contract_closure_skips_uncalled_contracts() {
    let none: Option<u32> = None;
    let none_res: Option<u32> = none.and_then(trust_vc::closure!(
        |x: u32| -> Option<u32>
        requires(false)
        ensures(|r: Option<u32>| r == Option::<u32>::Some(x + 99u32))
        Option::<u32>::Some(x + 1u32)
    ));
    assert_eq!(none_res, Option::<u32>::None);
}

#[allow(dead_code)]
fn option_and_then_contract_closure_bad_precondition_counterexample() {
    let opt: Option<u32> = Some(1000u32);
    let res: Option<u32> = opt.and_then(trust_vc::closure!(
        |x: u32| -> Option<u32>
        requires(x < 1000u32)
        ensures(|r: Option<u32>| r == Option::<u32>::Some(x + 1u32))
        Option::<u32>::Some(x + 1u32)
    ));
    assert_eq!(res, Option::<u32>::Some(1001u32));
}

fn option_and_then_contract_closure_upstream_shape_wrong_result_counterexample() {
    let opt: Option<u32> = Some(2u32);
    let res: Option<u32> = opt.and_then(trust_vc::closure!(
        |x: u32| -> Option<u32>
        requires(x < 1000u32)
        ensures(|r: Option<u32>| r.is_some() && r.unwrap() == x + 2u32)
        Option::<u32>::Some(x + 1u32)
    ));
    assert_eq!(res, Option::<u32>::Some(3u32));
}

fn option_and_then_contract_closure_wrong_result_counterexample() {
    let opt: Option<u32> = Some(2u32);
    let res: Option<u32> = opt.and_then(trust_vc::closure!(
        |x: u32| -> Option<u32>
        requires(x < 1000u32)
        ensures(|r: Option<u32>| r == Option::<u32>::Some(x + 2u32))
        Option::<u32>::Some(x + 1u32)
    ));
    assert_eq!(res, Option::<u32>::Some(3u32));
}

fn option_unwrap_or_else_contract_closure_requires_ensures() {
    let opt: Option<u32> = None;
    let val: u32 = opt.unwrap_or_else(trust_vc::closure!(
        || -> u32
        requires(true)
        ensures(|r: u32| r == 99u32)
        99u32
    ));
    assert_eq!(val, 99u32);
}

fn option_unwrap_or_else_contract_closure_upstream_shape() {
    let some: Option<u32> = Some(42u32);
    let some_val: u32 = some.unwrap_or_else(trust_vc::closure!(
        || -> u32
        ensures(|r: u32| r == 99u32)
        99u32
    ));
    assert_eq!(some_val, 42u32);

    let none: Option<u32> = None;
    let none_val: u32 = none.unwrap_or_else(trust_vc::closure!(
        || -> u32
        ensures(|r: u32| r == 99u32)
        99u32
    ));
    assert_eq!(none_val, 99u32);
}

#[allow(dead_code)]
fn option_unwrap_or_else_contract_closure_skips_uncalled_contracts() {
    let some: Option<u32> = Some(42u32);
    let some_val: u32 = some.unwrap_or_else(trust_vc::closure!(
        || -> u32
        requires(false)
        ensures(|r: u32| r == 100u32)
        99u32
    ));
    assert_eq!(some_val, 42u32);
}

#[allow(dead_code)]
fn option_unwrap_or_else_contract_closure_bad_precondition_counterexample() {
    let opt: Option<u32> = None;
    let val: u32 = opt.unwrap_or_else(trust_vc::closure!(
        || -> u32
        requires(false)
        ensures(|r: u32| r == 99u32)
        99u32
    ));
    assert_eq!(val, 99u32);
}

fn option_unwrap_or_else_contract_closure_wrong_value_counterexample() {
    let opt: Option<u32> = None;
    let val: u32 = opt.unwrap_or_else(trust_vc::closure!(
        || -> u32
        ensures(|r: u32| r == 100u32)
        99u32
    ));
    assert_eq!(val, 99u32);
}

#[test]
fn option_rs_expected_case_metadata_is_exact() {
    let source =
        std::fs::read_to_string(option_port_path()).expect("option.rs port should be readable");
    let file = syn::parse_file(&source).expect("option.rs port should parse");
    assert_eq!(metadata_entries(&file), expected_metadata());
}

#[test]
fn option_rs_expected_case_metadata_matches_manifest() {
    let source =
        std::fs::read_to_string(option_port_path()).expect("option.rs port should be readable");
    let file = syn::parse_file(&source).expect("option.rs port should parse");
    assert_eq!(metadata_entries(&file), manifest_expected_metadata());
}

#[test]
fn option_rs_port_exposes_expected_partial_evidence_cases() {
    let source =
        std::fs::read_to_string(option_port_path()).expect("option.rs port should be readable");
    let file = syn::parse_file(&source).expect("option.rs port should parse");
    let mut observed = file
        .items
        .iter()
        .filter_map(|item| match item {
            syn::Item::Fn(function)
                if function
                    .attrs
                    .iter()
                    .any(|attr| trust_vc_evidence_case_attr_name(attr).is_some()) =>
            {
                Some(function.sig.ident.to_string())
            }
            _ => None,
        })
        .collect::<Vec<_>>();
    let mut expected = FILE_VERIFIED_CASES
        .iter()
        .map(|(case, _)| (*case).to_string())
        .collect::<Vec<_>>();
    observed.sort();
    expected.sort();

    assert_eq!(
        observed, expected,
        "option.rs port should expose only upstream file-backed cases; closure-contract probes are regression-only"
    );
}

#[test]
fn option_rs_active_upstream_cases_verify_from_file() {
    let path = option_port_path();
    let path = path.to_str().expect("option port path should be UTF-8");

    for (case, upstream_case) in FILE_VERIFIED_CASES {
        let result = verify_function_from_file(path, case)
            .unwrap_or_else(|err| panic!("{case} ({upstream_case}) should extract: {err}"));
        assert!(
            matches!(result, VerifyResult::Verified),
            "{case} ({upstream_case}) should verify, got: {result:?}"
        );
    }
}

#[test]
fn option_rs_closure_contract_cases_verify_from_regression_file() {
    let path = option_regression_path();
    let path = path.to_str().expect("option port path should be UTF-8");

    for case in DIRECT_SOURCE_CLOSURE_CONTRACT_CASES {
        let result = verify_function_from_file(path, case)
            .unwrap_or_else(|err| panic!("{case} should extract: {err}"));
        assert!(
            matches!(result, VerifyResult::Verified),
            "{case} should verify from regression direct source, got: {result:?}"
        );
    }
}

#[test]
fn option_rs_direct_source_rejects_called_bad_postconditions() {
    let path = option_regression_path();
    let path = path
        .to_str()
        .expect("option regression path should be UTF-8");

    for case in [
        "option_ok_or_else_contract_closure_wrong_err_counterexample",
        "option_and_then_contract_closure_wrong_result_counterexample",
        "option_and_then_contract_closure_upstream_shape_wrong_result_counterexample",
        "option_unwrap_or_else_contract_closure_wrong_value_counterexample",
    ] {
        let result = verify_function_from_file(path, case)
            .unwrap_or_else(|err| panic!("bad closure postcondition case should extract: {err}"));
        assert!(
            matches!(
                result,
                VerifyResult::Counterexample { .. } | VerifyResult::Unknown { .. }
            ),
            "{case} called closure postcondition should be checked from direct source, got: {result:?}"
        );
    }
}

#[test]
fn option_rs_direct_source_rejects_called_bad_preconditions() {
    let path = option_regression_path();
    let path = path
        .to_str()
        .expect("option regression path should be UTF-8");

    for case in [
        "option_ok_or_else_contract_closure_bad_precondition_counterexample",
        "option_and_then_contract_closure_bad_precondition_counterexample",
        "option_unwrap_or_else_contract_closure_bad_precondition_counterexample",
    ] {
        let result = verify_function_from_file(path, case)
            .unwrap_or_else(|err| panic!("bad closure precondition case should extract: {err}"));
        assert!(
            matches!(
                result,
                VerifyResult::Counterexample { .. } | VerifyResult::Unknown { .. }
            ),
            "{case} called closure precondition should be checked from direct source, got: {result:?}"
        );
    }
}

#[test]
fn option_rs_closure_contract_subset_verifies_via_macro_collection() {
    for (case, run_case) in [
        (
            "option_ok_or_else_contract_closure_requires_ensures",
            option_ok_or_else_contract_closure_requires_ensures as fn(),
        ),
        (
            "option_ok_or_else_contract_closure_upstream_shape",
            option_ok_or_else_contract_closure_upstream_shape as fn(),
        ),
        (
            "option_ok_or_else_contract_closure_skips_uncalled_postcondition",
            option_ok_or_else_contract_closure_skips_uncalled_postcondition as fn(),
        ),
        (
            "option_and_then_contract_closure_precondition",
            option_and_then_contract_closure_precondition as fn(),
        ),
        (
            "option_and_then_contract_closure_upstream_shape",
            option_and_then_contract_closure_upstream_shape as fn(),
        ),
        (
            "option_unwrap_or_else_contract_closure_requires_ensures",
            option_unwrap_or_else_contract_closure_requires_ensures as fn(),
        ),
        (
            "option_unwrap_or_else_contract_closure_upstream_shape",
            option_unwrap_or_else_contract_closure_upstream_shape as fn(),
        ),
    ] {
        let result = common::verify_and_get_result(run_case);
        assert!(
            matches!(result, VerifyResult::Verified),
            "{case} should verify through macro collection, got: {result:?}"
        );
    }
}

#[test]
fn option_rs_upstream_shape_option_unwrap_contract_verifies() {
    let result = common::verify_and_get_result(option_and_then_contract_closure_upstream_shape);
    assert!(
        matches!(result, VerifyResult::Verified),
        "upstream-shaped and_then closure contract should verify with the is_some() guard, got: {result:?}"
    );
}

#[test]
fn option_rs_closure_contract_negative_cases_are_rejected() {
    for (case, run_case) in [
        (
            "option_ok_or_else_contract_closure_wrong_err_counterexample",
            option_ok_or_else_contract_closure_wrong_err_counterexample as fn(),
        ),
        (
            "option_and_then_contract_closure_wrong_result_counterexample",
            option_and_then_contract_closure_wrong_result_counterexample as fn(),
        ),
        (
            "option_and_then_contract_closure_upstream_shape_wrong_result_counterexample",
            option_and_then_contract_closure_upstream_shape_wrong_result_counterexample as fn(),
        ),
        (
            "option_unwrap_or_else_contract_closure_wrong_value_counterexample",
            option_unwrap_or_else_contract_closure_wrong_value_counterexample as fn(),
        ),
    ] {
        let result = common::verify_and_get_result(run_case);
        assert!(
            matches!(
                result,
                VerifyResult::Counterexample { .. } | VerifyResult::Unknown { .. }
            ),
            "{case} should be rejected through macro collection, got: {result:?}"
        );
    }
}
