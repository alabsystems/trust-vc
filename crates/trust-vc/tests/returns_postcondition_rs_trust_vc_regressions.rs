// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Executable guards for the current upstream returns_postcondition.rs TrustVc scout slice.
//!
//! This test keeps the corpus row as unsupported-gap evidence only. It pins
//! Rust-valid verified/counterexample cases, fail-closed diagnostics, upstream
//! shape anchors, and local expected-case metadata. Solver Unknown is rejected.

mod common;

use std::collections::BTreeSet;
use std::path::{Path, PathBuf};
use trust_vc_core::{
    extract_verification_conditions_with_file_context, verify_function_from_file, VerifyResult,
};

#[derive(Debug, Clone, PartialEq, Eq)]
struct ExpectedCase {
    case: String,
    upstream_case: String,
    status: String,
    min_obligations: usize,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct ExpectedCaseWithPatterns {
    case: String,
    upstream_case: String,
    status: String,
    min_obligations: usize,
    expected_error_patterns: Vec<String>,
}

fn port_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/ported/returns_postcondition.rs")
}

fn verus_manifest_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/verus-tests.json")
}

fn pinned_upstream_path() -> PathBuf {
    common::pinned_verus_test_path("returns_postcondition.rs")
}

fn parse_port_file() -> (String, syn::File) {
    let path = port_path();
    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|err| panic!("{} should be readable: {err}", path.display()));
    let file = syn::parse_file(&source)
        .unwrap_or_else(|err| panic!("{} should parse as Rust syntax: {err}", path.display()));
    (source, file)
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
    }
}

fn parse_expected_cases(file: &syn::File) -> Vec<ExpectedCase> {
    let item_const = file
        .items
        .iter()
        .find_map(|item| match item {
            syn::Item::Const(item_const)
                if item_const.ident == "RETURNS_POSTCONDITION_RS_EXPECTED_CASES" =>
            {
                Some(item_const)
            }
            _ => None,
        })
        .expect("returns_postcondition port should define expected-case metadata");

    let array = match item_const.expr.as_ref() {
        syn::Expr::Reference(reference) => match reference.expr.as_ref() {
            syn::Expr::Array(array) => array,
            _ => panic!("expected metadata const to reference an array"),
        },
        _ => panic!("expected metadata const to reference an array"),
    };

    array.elems.iter().map(parse_expected_case_tuple).collect()
}

fn with_error_patterns(cases: Vec<ExpectedCase>) -> Vec<ExpectedCaseWithPatterns> {
    cases
        .into_iter()
        .map(|case| ExpectedCaseWithPatterns {
            expected_error_patterns: expected_error_fragments(&case.case)
                .unwrap_or_default()
                .iter()
                .map(|fragment| (*fragment).to_string())
                .collect(),
            case: case.case,
            upstream_case: case.upstream_case,
            status: case.status,
            min_obligations: case.min_obligations,
        })
        .collect()
}

fn manifest_expected_cases() -> Vec<ExpectedCaseWithPatterns> {
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
                == Some("source/rust_verify_test/tests/returns_postcondition.rs")
        })
        .expect("Verus manifest should contain returns_postcondition.rs row");

    row["expected_cases"]
        .as_array()
        .expect("returns_postcondition manifest row should contain expected_cases")
        .iter()
        .map(|case| ExpectedCaseWithPatterns {
            case: case["case_id"]
                .as_str()
                .expect("manifest case should contain case_id")
                .to_string(),
            upstream_case: case["upstream_case_id"]
                .as_str()
                .expect("manifest case should contain upstream_case_id")
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

fn verify_case(path: &str, case: &str, upstream_case: &str) -> VerifyResult {
    match verify_function_from_file(path, case)
        .unwrap_or_else(|err| panic!("{case} ({upstream_case}) should extract: {err}"))
    {
        VerifyResult::Unknown { reason, .. } => {
            panic!("{case} ({upstream_case}) returned solver Unknown, which is not stable evidence: {reason}")
        }
        result => result,
    }
}

fn expected_error_fragments(case: &str) -> Option<&'static [&'static str]> {
    Some(match case {
        "returns_basic_direct_attr_unresolved_sum_return" => &["unresolved variable `b`"],
        "returns_direct_attr_unknown_ret_param_rejected" => &["unresolved variable `x`"],
        "returns_basic_direct_attr_literal_type_mismatch" => {
            &["type of `returns` clause does not match function return type"]
        }
        "returns_reference_direct_attr_char_referent_rejected" => {
            &["unsupported direct #[returns] shared-reference identifier `x`"]
        }
        "returns_mut_ref_bool_current_value_currently_rejected" => &[
            "unsupported unary operator",
            "dereference expressions are not supported in verification syntax",
        ],
        "spec_direct_returns_clause_rejected"
        | "spec_grouped_returns_clause_rejected"
        | "spec_direct_returns_expression_rejected" => {
            &["spec functions cannot have `returns` clause"]
        }
        "conflicting_returns_clause" | "conflicting_grouped_returns_clause" => &[
            "a `returns` clause cannot be declared on both a trait method impl and its declaration",
        ],
        _ => return None,
    })
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

    for fragment in expected_fragments {
        assert!(
            message.contains(fragment),
            "{case} ({upstream_case}) error should contain {fragment:?}, got: {message}"
        );
    }
}

#[test]
fn returns_postcondition_rs_port_file_is_rust_syntax() {
    parse_port_file();
}

#[test]
fn returns_postcondition_rs_pinned_upstream_case_shapes_are_present() {
    let path = pinned_upstream_path();
    if !path.exists() {
        eprintln!(
            "skipping pinned upstream returns_postcondition.rs shape check; missing {}",
            path.display()
        );
        return;
    }

    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", path.display()));
    for expected in [
        "#[test] returns_basic",
        "#[test] wrong_type",
        "#[test] spec_fn_returns",
        "#[test] spec_fn_returns_references_ret_param",
        "#[test] returning_unit_value",
        "#[test] default_trait_fn_with_returns",
        "#[test] default_trait_fn_with_returns_override",
        "#[test] default_trait_fn_with_returns_conflict",
        "#[test] trait_returns_on_trait_method_decl",
        "#[test] trait_returns_on_trait_method_impl",
        "#[test] returns_and_recommends_issue1834",
        "#[test] allow_in_spec_mut_ref",
        "returns 20u8",
        "returns x == 3",
        "returns ()",
        "returns self.ret(i)",
        "returns (x * y) as u128",
    ] {
        assert!(
            source.contains(expected),
            "pinned upstream returns_postcondition.rs should still contain {expected}"
        );
    }
}

#[test]
fn returns_postcondition_rs_expected_case_metadata_is_schema_valid() {
    let (source, file) = parse_port_file();
    assert!(
        source.contains("RETURNS_POSTCONDITION_RS_EXPECTED_CASES")
            && source.contains("returns_postcondition_rs_expected_cases"),
        "port should expose expected-case metadata and accessor"
    );

    let cases = parse_expected_cases(&file);
    assert!(
        !cases.is_empty(),
        "returns_postcondition metadata should list expected cases"
    );

    let mut seen = BTreeSet::new();
    for expected in &cases {
        assert!(
            seen.insert(expected.case.clone()),
            "metadata should not duplicate case {}",
            expected.case
        );
        assert!(
            !expected.upstream_case.is_empty(),
            "{} should pin a nonempty upstream shape name",
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
                expected_error_fragments(&expected.case).is_some(),
                "{} error metadata should have pinned diagnostic fragments",
                expected.case
            );
        } else {
            assert!(
                expected.min_obligations > 0,
                "{} non-error metadata should declare an obligation floor",
                expected.case
            );
        }
        assert!(
            find_function_owned(&file, &expected.case).is_some(),
            "{} should exist in the port",
            expected.case
        );
    }
}

#[test]
fn returns_postcondition_rs_expected_case_metadata_matches_manifest() {
    let (_, file) = parse_port_file();

    assert_eq!(
        manifest_expected_cases(),
        with_error_patterns(parse_expected_cases(&file)),
        "returns_postcondition manifest expected_cases should match port metadata and fail-closed patterns exactly"
    );
}

#[test]
fn returns_postcondition_rs_expected_cases_match_declared_statuses_and_obligations() {
    let path = port_path();
    let path_str = path
        .to_str()
        .expect("returns_postcondition.rs port path should be UTF-8");
    let (_, file) = parse_port_file();
    let cases = parse_expected_cases(&file);

    for expected in &cases {
        match expected.status.as_str() {
            "verified" | "counterexample" => {
                let function = find_function_owned(&file, &expected.case).unwrap_or_else(|| {
                    panic!(
                        "{} ({}) should exist in the port",
                        expected.case, expected.upstream_case
                    )
                });
                let vc = extract_verification_conditions_with_file_context(&file, &function)
                    .unwrap_or_else(|err| {
                        panic!(
                            "{} ({}) should extract VCs: {err}",
                            expected.case, expected.upstream_case
                        )
                    });
                assert!(
                    vc.obligations().len() >= expected.min_obligations,
                    "{} ({}) should collect at least {} obligation(s), got {}",
                    expected.case,
                    expected.upstream_case,
                    expected.min_obligations,
                    vc.obligations().len()
                );

                let result = verify_case(path_str, &expected.case, &expected.upstream_case);
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
                    expected_error_fragments(&expected.case).unwrap_or_else(|| {
                        panic!(
                            "{} ({}) should have expected diagnostic fragments",
                            expected.case, expected.upstream_case
                        )
                    });
                expect_fail_closed(
                    path_str,
                    &expected.case,
                    &expected.upstream_case,
                    expected_fragments,
                );
            }
            other => panic!(
                "{} ({}) has unsupported expected status {other}",
                expected.case, expected.upstream_case
            ),
        }
    }
}
