// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Executable guards for the upstream safe_api.rs TrustVc scout slice.
//!
//! These tests intentionally keep `source/rust_verify_test/tests/safe_api.rs`
//! as an unsupported gap. They parse the port's expected-case metadata, reject
//! solver `Unknown` as evidence, check declared verified/counterexample/error
//! outcomes and obligation floors, and pin the upstream API-safety shapes whose
//! exact Verus diagnostics TrustVc does not currently expose.

mod common;

use std::{
    collections::{BTreeMap, BTreeSet},
    path::{Path, PathBuf},
};
use trust_vc_core::{
    extract_verification_conditions_with_file_context, verify_function_from_file, VerifyResult,
};

#[derive(Debug, Clone, PartialEq, Eq)]
struct ExpectedCase {
    case: String,
    upstream_case: String,
    status: String,
    min_obligations: usize,
    expected_error_patterns: Vec<String>,
}

fn safe_api_port_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/ported/safe_api.rs")
}

fn verus_manifest_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/verus-tests.json")
}

fn pinned_upstream_safe_api_path() -> PathBuf {
    common::pinned_verus_test_path("safe_api.rs")
}

fn parse_safe_api_port_file() -> (String, syn::File) {
    let path = safe_api_port_path();
    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|err| panic!("{} should be readable: {err}", path.display()));
    let file = syn::parse_file(&source)
        .unwrap_or_else(|err| panic!("{} should parse as Rust syntax: {err}", path.display()));
    (source, file)
}

fn parse_safe_api_expected_cases() -> Vec<ExpectedCase> {
    let (_, file) = parse_safe_api_port_file();
    parse_expected_case_metadata(&file)
}

fn referenced_array_const(file: &syn::File, const_name: &str) -> syn::ExprArray {
    let item_const = file
        .items
        .iter()
        .find_map(|item| match item {
            syn::Item::Const(item_const) if item_const.ident == const_name => Some(item_const),
            _ => None,
        })
        .unwrap_or_else(|| panic!("safe_api port should define {const_name}"));

    match item_const.expr.as_ref() {
        syn::Expr::Reference(reference) => match reference.expr.as_ref() {
            syn::Expr::Array(array) => array.clone(),
            _ => panic!("{const_name} should reference an array"),
        },
        syn::Expr::Array(array) => array.clone(),
        _ => panic!("{const_name} should be an array literal"),
    }
}

fn parse_expected_case_metadata(file: &syn::File) -> Vec<ExpectedCase> {
    let mut error_patterns = parse_error_pattern_metadata(file);

    let entries = referenced_array_const(file, "SAFE_API_RS_EXPECTED_CASES")
        .elems
        .iter()
        .map(|entry| {
            let mut parsed = parse_expected_case_tuple(entry);
            parsed.expected_error_patterns =
                error_patterns.remove(&parsed.case).unwrap_or_default();
            parsed
        })
        .collect();

    assert!(
        error_patterns.is_empty(),
        "error-pattern metadata should not contain orphan cases: {error_patterns:?}"
    );
    entries
}

fn parse_error_pattern_metadata(file: &syn::File) -> BTreeMap<String, Vec<String>> {
    let array = referenced_array_const(file, "SAFE_API_RS_FAIL_CLOSED_ERROR_PATTERNS");
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
        let case_id = parse_string_lit(&tuple.elems[0]);
        let patterns = parse_string_slice(&tuple.elems[1]);
        assert!(
            entries.insert(case_id.clone(), patterns).is_none(),
            "duplicate error-pattern metadata for {case_id}"
        );
    }

    entries
}

fn parse_expected_case_tuple(expr: &syn::Expr) -> ExpectedCase {
    let tuple = match expr {
        syn::Expr::Tuple(tuple) => tuple,
        _ => panic!("expected metadata tuple"),
    };
    assert_eq!(
        tuple.elems.len(),
        4,
        "expected metadata tuple shape (case, upstream_case, status, min_obligations)"
    );

    ExpectedCase {
        case: parse_string_lit(&tuple.elems[0]),
        upstream_case: parse_string_lit(&tuple.elems[1]),
        status: parse_string_lit(&tuple.elems[2]),
        min_obligations: parse_usize_lit(&tuple.elems[3]),
        expected_error_patterns: Vec::new(),
    }
}

fn parse_string_lit(expr: &syn::Expr) -> String {
    match expr {
        syn::Expr::Lit(expr_lit) => match &expr_lit.lit {
            syn::Lit::Str(lit) => lit.value(),
            _ => panic!("expected string literal"),
        },
        _ => panic!("expected string literal expression"),
    }
}

fn parse_usize_lit(expr: &syn::Expr) -> usize {
    match expr {
        syn::Expr::Lit(expr_lit) => match &expr_lit.lit {
            syn::Lit::Int(lit) => lit
                .base10_parse()
                .unwrap_or_else(|err| panic!("expected usize literal: {err}")),
            _ => panic!("expected integer literal"),
        },
        _ => panic!("expected integer literal expression"),
    }
}

fn parse_string_slice(expr: &syn::Expr) -> Vec<String> {
    let syn::Expr::Reference(reference) = expr else {
        panic!("expected referenced string-slice metadata");
    };
    let syn::Expr::Array(array) = reference.expr.as_ref() else {
        panic!("expected string-slice array metadata");
    };

    array.elems.iter().map(parse_string_lit).collect()
}

fn manifest_expected_metadata() -> Vec<ExpectedCase> {
    let source =
        std::fs::read_to_string(verus_manifest_path()).expect("Verus manifest should be readable");
    let manifest: serde_json::Value =
        serde_json::from_str(&source).expect("Verus manifest should parse as JSON");
    let row = manifest["entries"]
        .as_array()
        .expect("Verus manifest should contain entries")
        .iter()
        .find(|entry| {
            entry["upstream_path"].as_str() == Some("source/rust_verify_test/tests/safe_api.rs")
        })
        .expect("Verus manifest should contain safe_api.rs row");

    row["expected_cases"]
        .as_array()
        .expect("safe_api.rs row should contain expected_cases")
        .iter()
        .map(|entry| ExpectedCase {
            case: entry["case_id"]
                .as_str()
                .expect("case_id should be a string")
                .to_string(),
            upstream_case: entry
                .get("upstream_case_id")
                .and_then(serde_json::Value::as_str)
                .unwrap_or("")
                .to_string(),
            status: entry["expected_verdict"]
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

fn find_function_owned(file: &syn::File, case: &str) -> Option<syn::ItemFn> {
    find_function_in_items_owned(&file.items, case)
}

fn find_function_in_items_owned(items: &[syn::Item], case: &str) -> Option<syn::ItemFn> {
    for item in items {
        if let syn::Item::Fn(function) = item {
            if function.sig.ident == case {
                return Some(function.clone());
            }
        }
    }

    for item in items {
        match item {
            syn::Item::Impl(impl_block) => {
                for impl_item in &impl_block.items {
                    if let syn::ImplItem::Fn(method) = impl_item {
                        if method.sig.ident == case {
                            return Some(syn::ItemFn {
                                attrs: method.attrs.clone(),
                                vis: method.vis.clone(),
                                sig: method.sig.clone(),
                                block: Box::new(method.block.clone()),
                            });
                        }
                    }
                }
            }
            syn::Item::Mod(module) => {
                if let Some((_, inner_items)) = &module.content {
                    if let Some(function) = find_function_in_items_owned(inner_items, case) {
                        return Some(function);
                    }
                }
            }
            syn::Item::Trait(trait_block) => {
                for trait_item in &trait_block.items {
                    if let syn::TraitItem::Fn(method) = trait_item {
                        if method.sig.ident == case {
                            if let Some(block) = &method.default {
                                return Some(syn::ItemFn {
                                    attrs: method.attrs.clone(),
                                    vis: syn::Visibility::Inherited,
                                    sig: method.sig.clone(),
                                    block: Box::new(block.clone()),
                                });
                            }
                        }
                    }
                }
            }
            _ => {}
        }
    }

    None
}

fn safe_api_error_fragments(case: &str) -> Option<&'static [&'static str]> {
    Some(match case {
        "safe_api_trait_impl_side_requires_currently_blocked" => {
            &["trait method implementation cannot declare requires"]
        }
        "safe_api_closure_smuggling_boundary_fails_closed" => {
            &["unknown return type for function 'f'"]
        }
        "safe_api_fn_pointer_return_boundary_fails_closed" => &[
            "Failed to lower obligation 'return_value'",
            "unresolved variable `safe_api_fn_pointer_private_target`",
        ],
        _ => return None,
    })
}

fn verify_non_error_case(file: &syn::File, expected: &ExpectedCase) -> (VerifyResult, usize) {
    let function = find_function_owned(file, &expected.case).unwrap_or_else(|| {
        panic!(
            "{} ({}) should exist in the safe_api port",
            expected.case, expected.upstream_case
        )
    });
    let vc =
        extract_verification_conditions_with_file_context(file, &function).unwrap_or_else(|err| {
            panic!(
                "{} ({}) should extract VCs: {err}",
                expected.case, expected.upstream_case
            )
        });
    let obligations = vc.obligations().len();
    let result = vc.verify();
    if let VerifyResult::Unknown { reason, .. } = &result {
        panic!(
            "{} ({}) returned solver Unknown, which is not stable evidence: {reason}",
            expected.case, expected.upstream_case
        );
    }
    (result, obligations)
}

fn expect_fail_closed(path: &str, expected: &ExpectedCase, expected_fragments: &[&str]) {
    let message = match verify_function_from_file(path, &expected.case) {
        Ok(VerifyResult::Error { message }) => message,
        Ok(VerifyResult::Unknown { reason, .. }) => {
            panic!(
                "{} ({}) returned solver Unknown, which is not stable evidence: {reason}",
                expected.case, expected.upstream_case
            )
        }
        Ok(result) => {
            panic!(
                "{} ({}) should fail closed with Error, got: {result:?}",
                expected.case, expected.upstream_case
            )
        }
        Err(err) => err.to_string(),
    };

    for expected_fragment in expected_fragments {
        assert!(
            message.contains(expected_fragment),
            "{} ({}) error should contain {expected_fragment:?}, got: {message}",
            expected.case,
            expected.upstream_case
        );
    }
}

#[test]
fn safe_api_rs_port_file_is_rust_syntax() {
    parse_safe_api_port_file();
}

#[test]
fn safe_api_rs_pinned_upstream_case_shapes_are_present() {
    let path = pinned_upstream_safe_api_path();
    if !path.exists() {
        eprintln!(
            "skipping pinned upstream safe_api.rs shape check; missing {}",
            path.display()
        );
        return;
    }

    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", path.display()));
    for expected in [
        "#[test] normal_fn_requires_fail",
        "#[test] normal_fn_private_is_ok",
        "#[test] normal_fn_unsafe_is_ok",
        "#[test] normal_fn_ensures_is_ok",
        "#[test] normal_fn_mask_is_ok",
        "#[test] normal_fn_unwind_is_ok",
        "#[test] trait_fn_requires_is_ok",
        "#[test] trait_fn_ensures_fail",
        "#[test] trait_fn_unwind_fail",
        "#[test] trait_fn_mask_fail",
        "#[test] trait_fn_impl_requires_fail",
        "#[test] trait_fn_impl_requires_fail_even_if_trait_is_unsafe",
        "#[test] trait_fn_impl_with_default_body_and_nontrivial_requires",
        "#[test] opaque_closure_type_returned",
        "#[test] opaque_fndef_type_returned",
        "#[test] fnsig_type_returned",
        "#[test] dyn_returned",
        "#[test] any_returned",
        "#[test] fancy_0args_fail",
        "#[test] fancy_0args_ok",
        "Safe API violation: 'requires' clause is nontrivial",
        "Safe API violation: 'ensures' clause is nontrivial",
        "Safe API violation: 'unwind' clause is nontrivial",
        "Safe API violation: 'invariant' clause is nontrivial",
        "The verifier does not support opaque types together with the check-api-safety flag:",
        "The verifier does not yet support the following Rust feature: function pointer types",
    ] {
        assert!(
            source.contains(expected),
            "pinned upstream safe_api.rs should still contain {expected}"
        );
    }

    for expected in parse_safe_api_expected_cases() {
        if expected.upstream_case.is_empty() {
            continue;
        }
        let upstream_anchor = expected
            .upstream_case
            .split(" / ")
            .next()
            .expect("upstream metadata should have an anchor")
            .trim();
        assert!(
            source.contains(upstream_anchor),
            "{} should pin upstream shape {upstream_anchor}",
            expected.case
        );
    }
}

#[test]
fn safe_api_rs_expected_case_metadata_is_schema_valid() {
    let (source, file) = parse_safe_api_port_file();
    assert!(
        source.contains("SAFE_API_RS_EXPECTED_CASES")
            && source.contains("pub fn safe_api_rs_expected_cases")
            && source.contains("SAFE_API_RS_FAIL_CLOSED_ERROR_PATTERNS")
            && source.contains("pub fn safe_api_rs_fail_closed_error_patterns"),
        "safe_api port should expose expected-case and error-pattern metadata accessors"
    );

    let cases = parse_expected_case_metadata(&file);
    assert!(
        !cases.is_empty(),
        "safe_api port metadata should list expected cases"
    );

    let mut seen = BTreeSet::new();
    for expected in &cases {
        assert!(
            seen.insert(expected.case.clone()),
            "safe_api port metadata should not duplicate case {}",
            expected.case
        );
        assert!(
            matches!(
                expected.status.as_str(),
                "verified" | "counterexample" | "error"
            ),
            "{} should use only verified/counterexample/error status, got {}",
            expected.case,
            expected.status
        );
        assert_ne!(
            expected.status.to_ascii_lowercase(),
            "unknown",
            "{} must not list Unknown as expected evidence",
            expected.case
        );
        if expected.status == "error" {
            assert_eq!(
                expected.min_obligations, 0,
                "{} error metadata should declare zero obligations",
                expected.case
            );
            assert!(
                safe_api_error_fragments(&expected.case).is_some(),
                "{} error metadata should have pinned diagnostic fragments",
                expected.case
            );
            assert!(
                !expected.expected_error_patterns.is_empty(),
                "{} error metadata should declare expected_error_patterns",
                expected.case
            );
        } else {
            assert!(
                expected.min_obligations > 0,
                "{} non-error metadata should declare an obligation floor",
                expected.case
            );
            assert!(
                expected.expected_error_patterns.is_empty(),
                "{} non-error metadata should not declare expected_error_patterns",
                expected.case
            );
        }
        assert!(
            find_function_owned(&file, &expected.case).is_some(),
            "{} should exist in the safe_api port",
            expected.case
        );
    }
}

#[test]
fn safe_api_rs_expected_case_metadata_matches_manifest() {
    let cases = parse_safe_api_expected_cases();
    assert_eq!(cases, manifest_expected_metadata());
}

#[test]
fn safe_api_rs_expected_cases_match_declared_statuses_and_obligations() {
    let path = safe_api_port_path();
    let path_str = path
        .to_str()
        .expect("safe_api.rs port path should be UTF-8");
    let (_, file) = parse_safe_api_port_file();
    let cases = parse_safe_api_expected_cases();

    for expected in &cases {
        match expected.status.as_str() {
            "verified" | "counterexample" => {
                let (result, obligations) = verify_non_error_case(&file, expected);
                assert!(
                    obligations >= expected.min_obligations,
                    "{} ({}) should collect at least {} obligation(s), got {}",
                    expected.case,
                    expected.upstream_case,
                    expected.min_obligations,
                    obligations
                );
                match expected.status.as_str() {
                    "verified" => assert!(
                        matches!(result, VerifyResult::Verified),
                        "{} ({}) should verify, got: {result:?}",
                        expected.case,
                        expected.upstream_case
                    ),
                    "counterexample" => assert!(
                        matches!(result, VerifyResult::Counterexample { .. }),
                        "{} ({}) should produce a counterexample, got: {result:?}",
                        expected.case,
                        expected.upstream_case
                    ),
                    _ => unreachable!(),
                }
            }
            "error" => {
                let expected_fragments =
                    safe_api_error_fragments(&expected.case).unwrap_or_else(|| {
                        panic!(
                            "{} ({}) should have expected diagnostic fragments",
                            expected.case, expected.upstream_case
                        )
                    });
                expect_fail_closed(path_str, expected, expected_fragments);
            }
            other => panic!(
                "{} ({}) has unsupported expected status {other}",
                expected.case, expected.upstream_case
            ),
        }
    }
}
