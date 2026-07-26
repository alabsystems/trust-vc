// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! TrustVc-only regressions that were previously mixed into the partial
//! upstream functions.rs port.

#![allow(clippy::let_unit_value, clippy::unit_arg)]

mod common;

use std::{
    collections::{BTreeMap, BTreeSet},
    path::PathBuf,
};
use trust_vc_core::{
    ir::TrustVcType, vc::ObligationKind, verification_bridge::VerificationPipeline,
    verify_function_from_file, verify_macro, VerifyResult,
};
use trust_vc_types::int;

#[trust_vc::contract(
    requires(x >= 0),
    ensures(result > x),
    returns(result),
)]
fn sibling_contract_add_one(x: int) -> int {
    x + 1
}

#[trust_vc::contract(
    requires(x >= 0),
    ensures(result > x),
    returns(result),
)]
fn test_sibling_helper_contract_call(x: int) -> int {
    let y = sibling_contract_add_one(x);
    trust_vc::assert!(y > x);
    y
}

fn trust_vc_only_returns_unit() {}

#[trust_vc::spec]
fn trust_vc_only_returns_unit_spec() {}

fn trust_vc_only_takes_unit(_u: ()) {}

#[trust_vc::contract(
    ensures(result == trust_vc_only_returns_unit_spec()),
    returns(result),
)]
fn test_ensures_returns_default_regression_392_4() -> () {
    trust_vc_only_returns_unit()
}

#[trust_vc::contract(
    ensures(result == ()),
    returns(result),
)]
fn test_ensures_returns_default_regression_392_5() -> () {
    trust_vc_only_takes_unit(trust_vc_only_returns_unit())
}

fn declare_int_value(name: &str, value: int) {
    verify_macro::collect_variable(name.to_string(), "int".to_string());
    verify_macro::collect_obligation(
        ObligationKind::Assume,
        format!("{name}_value"),
        format!("{name} == {value}"),
        None,
    );
}

fn declare_unit(name: &str) {
    verify_macro::collect_variable(name.to_string(), "()".to_string());
}

fn verify_with_unit_spec_helper<F>(proof_fn: F) -> VerifyResult
where
    F: FnOnce(),
{
    common::with_clean_verification(|| {
        proof_fn();
        let mut pipeline = VerificationPipeline::collect_from_macros();
        pipeline.context_mut().declare_helper_function_typed(
            "trust_vc_only_returns_unit_spec",
            TrustVcType::Unit,
            Vec::new(),
        );
        pipeline
            .context_mut()
            .declare_var_typed("trust_vc_only_returns_unit_spec", TrustVcType::Unit);
        pipeline.verify()
    })
}

fn functions_port_path() -> PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/ported/functions.rs")
}

fn verus_manifest_path() -> PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/verus-tests.json")
}

const EXPECTED_CASES: &[(&str, &str, &str, &str, usize)] = &[
    (
        "test_use_fun_ext",
        "test_use_fun_ext",
        "evals/verus/ported/functions.rs",
        "verified",
        2,
    ),
    (
        "test_use_fun_ext2",
        "test_use_fun_ext2",
        "evals/verus/ported/functions.rs",
        "verified",
        2,
    ),
    (
        "test_ensures_returns_default_regression_392_1",
        "test_ensures_returns_default_regression_392_1",
        "evals/verus/ported/functions.rs",
        "verified",
        2,
    ),
    (
        "test_ensures_returns_default_regression_497",
        "test_ensures_returns_default_regression_497",
        "evals/verus/ported/functions.rs",
        "verified",
        1,
    ),
    (
        "test_ensures_returns_default_regression_392_2",
        "test_ensures_returns_default_regression_392_2",
        "evals/verus/ported/functions.rs",
        "verified",
        2,
    ),
    (
        "test_ensures_returns_default_regression_392_3",
        "test_ensures_returns_default_regression_392_3",
        "evals/verus/ported/functions.rs",
        "verified",
        2,
    ),
    (
        "test_returns_named_unit",
        "test_returns_named_unit",
        "evals/verus/ported/functions.rs",
        "verified",
        1,
    ),
    (
        "test_async_external_fn_accepted",
        "test_async_external_fn_accepted",
        "evals/verus/ported/functions.rs",
        "verified",
        1,
    ),
    (
        "test_non_async_opaque_types_disallowed",
        "test_non_async_opaque_types_disallowed",
        "evals/verus/ported/functions_invalid_opaque_type",
        "error",
        0,
    ),
    (
        "test_ensures_name_collision",
        "test_ensures_name_collision",
        "evals/verus/ported/functions.rs",
        "verified",
        1,
    ),
];

#[derive(Debug, Eq, PartialEq)]
struct CaseMetadata {
    case_id: String,
    upstream_case_id: String,
    trust_vc_path: String,
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
        .unwrap_or_else(|| panic!("functions port should define {const_name}"));

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
    let array = referenced_array_const(file, "FUNCTIONS_RS_EXPECTED_ERROR_PATTERNS");
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
    let array = referenced_array_const(file, "FUNCTIONS_RS_EXPECTED_CASES");
    let mut error_patterns = error_pattern_entries(file);
    let mut seen = BTreeSet::new();
    let mut entries = Vec::new();

    for entry in &array.elems {
        let syn::Expr::Tuple(tuple) = entry else {
            panic!("expected tuple expected-case metadata entry");
        };
        assert_eq!(
            tuple.elems.len(),
            5,
            "expected-case entries should have case, upstream case, TrustVc path, verdict, and min obligations"
        );
        let case_id = literal_string(&tuple.elems[0]);
        assert!(
            seen.insert(case_id.clone()),
            "duplicate functions metadata for {case_id}"
        );
        let expected_error_patterns = error_patterns.remove(&case_id).unwrap_or_default();
        entries.push(CaseMetadata {
            case_id,
            upstream_case_id: literal_string(&tuple.elems[1]),
            trust_vc_path: literal_string(&tuple.elems[2]),
            expected_verdict: literal_string(&tuple.elems[3]),
            min_obligations: literal_usize(&tuple.elems[4]),
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
    EXPECTED_CASES
        .iter()
        .map(
            |(case_id, upstream_case_id, trust_vc_path, expected_verdict, min_obligations)| {
                CaseMetadata {
                    case_id: (*case_id).to_string(),
                    upstream_case_id: (*upstream_case_id).to_string(),
                    trust_vc_path: (*trust_vc_path).to_string(),
                    expected_verdict: (*expected_verdict).to_string(),
                    min_obligations: *min_obligations,
                    expected_error_patterns: if *case_id == "test_non_async_opaque_types_disallowed"
                    {
                        vec!["`impl Trait` in type aliases is unstable".to_string()]
                    } else {
                        Vec::new()
                    },
                }
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
            entry["upstream_path"].as_str() == Some("source/rust_verify_test/tests/functions.rs")
        })
        .expect("Verus manifest should contain functions.rs row");

    row["expected_cases"]
        .as_array()
        .expect("functions.rs row should contain expected_cases")
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
            trust_vc_path: entry["trust_vc_path"]
                .as_str()
                .expect("trust_vc_path should be a string")
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

#[test]
fn functions_rs_expected_case_metadata_is_exact() {
    let source = std::fs::read_to_string(functions_port_path())
        .expect("functions.rs port should be readable");
    let file = syn::parse_file(&source).expect("functions.rs port should parse");
    assert_eq!(metadata_entries(&file), expected_metadata());
}

#[test]
fn functions_rs_expected_case_metadata_matches_manifest() {
    let source = std::fs::read_to_string(functions_port_path())
        .expect("functions.rs port should be readable");
    let file = syn::parse_file(&source).expect("functions.rs port should parse");
    assert_eq!(metadata_entries(&file), manifest_expected_metadata());
}

#[test]
fn functions_rs_helpers_are_not_standalone_evidence_cases() {
    let source = std::fs::read_to_string(functions_port_path())
        .expect("functions.rs port should be readable");
    let file = syn::parse_file(&source).expect("functions.rs port should parse");

    for helper in ["returns_nothing", "returns_unit", "takes_unit"] {
        let function = file
            .items
            .iter()
            .find_map(|item| match item {
                syn::Item::Fn(function) if function.sig.ident == helper => Some(function),
                _ => None,
            })
            .unwrap_or_else(|| panic!("{helper} helper should exist in functions.rs port"));
        let trust_vc_attrs = function
            .attrs
            .iter()
            .filter_map(trust_vc_evidence_case_attr_name)
            .collect::<Vec<_>>();
        assert!(
            trust_vc_attrs.is_empty(),
            "{helper} must stay a plain helper so evidence does not observe it as a standalone case; found {trust_vc_attrs:?}"
        );
    }
}

#[test]
fn functions_rs_active_upstream_port_cases_verify_from_file() {
    let path = functions_port_path();
    let path = path.to_str().expect("port path should be UTF-8");

    for (case, _, _, _, _) in EXPECTED_CASES
        .iter()
        .filter(|(_, _, trust_vc_path, verdict, _)| {
            *trust_vc_path == "evals/verus/ported/functions.rs" && *verdict == "verified"
        })
    {
        let result = verify_function_from_file(path, case)
            .unwrap_or_else(|err| panic!("{case} should extract from functions.rs: {err}"));
        assert!(
            matches!(result, VerifyResult::Verified),
            "{case} should verify from functions.rs, got: {result:?}"
        );
    }
}

#[test]
fn trust_vc_only_sibling_helper_regressions_verify() {
    let direct_result = common::verify_and_get_result(|| {
        declare_int_value("x", 3 as int);
        declare_int_value("result", 4 as int);
        let direct = sibling_contract_add_one(3 as int);
        assert_eq!(direct, 4 as int);
    });
    assert!(
        matches!(direct_result, VerifyResult::Verified),
        "direct sibling helper contract should verify, got: {direct_result:?}"
    );

    let helper_result = common::verify_and_get_result(|| {
        declare_int_value("x", 5 as int);
        declare_int_value("y", 6 as int);
        declare_int_value("result", 6 as int);
        let via_helper = test_sibling_helper_contract_call(5 as int);
        assert_eq!(via_helper, 6 as int);
    });
    assert!(
        matches!(helper_result, VerifyResult::Verified),
        "sibling helper caller contract should verify, got: {helper_result:?}"
    );
}

#[test]
fn trust_vc_only_unit_return_regressions_verify() {
    let first_result = verify_with_unit_spec_helper(|| {
        declare_unit("result");
        let first = test_ensures_returns_default_regression_392_4();
        assert_eq!(first, ());
    });
    assert!(
        matches!(first_result, VerifyResult::Verified),
        "unit-return regression 392_4 should verify, got: {first_result:?}"
    );

    let second_result = verify_with_unit_spec_helper(|| {
        declare_unit("result");
        let second = test_ensures_returns_default_regression_392_5();
        assert_eq!(second, ());
    });
    assert!(
        matches!(second_result, VerifyResult::Verified),
        "unit-return regression 392_5 should verify, got: {second_result:?}"
    );
}
