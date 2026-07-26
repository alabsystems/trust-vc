// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Executable guards for the currently ported upstream return.rs and
//! returns_postcondition.rs subsets.
//!
//! These tests intentionally keep both manifest entries fail-closed. They prove
//! only the listed upstream-derived return-control-flow and unit-return slices.

mod common;

use std::collections::{BTreeMap, BTreeSet};
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
    expected_error_patterns: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct UnpromotedUpstreamCase {
    upstream_case: String,
    reason: String,
}

fn port_path(file: &str) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join(format!("../../evals/verus/ported/{file}"))
}

fn return_port_path() -> PathBuf {
    port_path("return.rs")
}

fn pinned_upstream_return_path() -> PathBuf {
    common::pinned_verus_test_path("return.rs")
}

fn verus_manifest_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/verus-tests.json")
}

fn parse_return_port_file() -> (String, syn::File) {
    let path = return_port_path();
    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|err| panic!("{} should be readable: {err}", path.display()));
    let file = syn::parse_file(&source)
        .unwrap_or_else(|err| panic!("{} should parse as Rust syntax: {err}", path.display()));
    (source, file)
}

fn parse_return_expected_cases() -> Vec<ExpectedCase> {
    let (_, file) = parse_return_port_file();
    parse_expected_case_metadata(&file, "RETURN_RS_EXPECTED_CASES")
}

fn parse_return_metadata_entries() -> Vec<ExpectedCase> {
    let (_, file) = parse_return_port_file();
    let mut error_patterns =
        parse_error_pattern_metadata(&file, "RETURN_RS_EXPECTED_ERROR_PATTERNS");
    let mut entries = parse_expected_case_metadata(&file, "RETURN_RS_EXPECTED_CASES");

    for entry in &mut entries {
        entry.expected_error_patterns = error_patterns.remove(&entry.case).unwrap_or_default();
    }

    assert!(
        error_patterns.is_empty(),
        "error-pattern metadata should not contain orphan cases: {error_patterns:?}"
    );
    entries
}

fn parse_return_unpromoted_upstream_cases() -> Vec<UnpromotedUpstreamCase> {
    let (_, file) = parse_return_port_file();
    parse_unpromoted_upstream_case_metadata(&file, "RETURN_RS_UNPROMOTED_UPSTREAM_CASES")
}

fn parse_expected_case_metadata(file: &syn::File, const_name: &str) -> Vec<ExpectedCase> {
    let item_const = file
        .items
        .iter()
        .find_map(|item| match item {
            syn::Item::Const(item_const) if item_const.ident == const_name => Some(item_const),
            _ => None,
        })
        .unwrap_or_else(|| panic!("return port should define {const_name}"));

    let array = match item_const.expr.as_ref() {
        syn::Expr::Reference(reference) => match reference.expr.as_ref() {
            syn::Expr::Array(array) => array,
            _ => panic!("{const_name} should reference an array"),
        },
        syn::Expr::Array(array) => array,
        _ => panic!("{const_name} should be an array literal"),
    };

    array.elems.iter().map(parse_expected_case_tuple).collect()
}

fn parse_error_pattern_metadata(
    file: &syn::File,
    const_name: &str,
) -> BTreeMap<String, Vec<String>> {
    let item_const = file
        .items
        .iter()
        .find_map(|item| match item {
            syn::Item::Const(item_const) if item_const.ident == const_name => Some(item_const),
            _ => None,
        })
        .unwrap_or_else(|| panic!("return port should define {const_name}"));

    let array = match item_const.expr.as_ref() {
        syn::Expr::Reference(reference) => match reference.expr.as_ref() {
            syn::Expr::Array(array) => array,
            _ => panic!("{const_name} should reference an array"),
        },
        syn::Expr::Array(array) => array,
        _ => panic!("{const_name} should be an array literal"),
    };

    let mut entries = BTreeMap::new();
    for entry in &array.elems {
        let tuple = match entry {
            syn::Expr::Tuple(tuple) => tuple,
            _ => panic!("expected error-pattern metadata tuple"),
        };
        assert_eq!(
            tuple.elems.len(),
            2,
            "expected error-pattern metadata tuple shape (case, patterns)"
        );

        let case = parse_string_lit(&tuple.elems[0]);
        let patterns = parse_string_slice(&tuple.elems[1]);
        assert!(
            entries.insert(case.clone(), patterns).is_none(),
            "return error-pattern metadata should not duplicate case {case}"
        );
    }

    entries
}

fn parse_unpromoted_upstream_case_metadata(
    file: &syn::File,
    const_name: &str,
) -> Vec<UnpromotedUpstreamCase> {
    let item_const = file
        .items
        .iter()
        .find_map(|item| match item {
            syn::Item::Const(item_const) if item_const.ident == const_name => Some(item_const),
            _ => None,
        })
        .unwrap_or_else(|| panic!("return port should define {const_name}"));

    let array = match item_const.expr.as_ref() {
        syn::Expr::Reference(reference) => match reference.expr.as_ref() {
            syn::Expr::Array(array) => array,
            _ => panic!("{const_name} should reference an array"),
        },
        syn::Expr::Array(array) => array,
        _ => panic!("{const_name} should be an array literal"),
    };

    array
        .elems
        .iter()
        .map(parse_unpromoted_upstream_case_tuple)
        .collect()
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

fn parse_unpromoted_upstream_case_tuple(expr: &syn::Expr) -> UnpromotedUpstreamCase {
    let tuple = match expr {
        syn::Expr::Tuple(tuple) => tuple,
        _ => panic!("expected unpromoted upstream metadata tuple"),
    };
    assert_eq!(
        tuple.elems.len(),
        2,
        "expected unpromoted upstream metadata tuple shape (upstream_case, reason)"
    );

    UnpromotedUpstreamCase {
        upstream_case: parse_string_lit(&tuple.elems[0]),
        reason: parse_string_lit(&tuple.elems[1]),
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

fn parse_string_slice(expr: &syn::Expr) -> Vec<String> {
    let array = match expr {
        syn::Expr::Reference(reference) => match reference.expr.as_ref() {
            syn::Expr::Array(array) => array,
            _ => panic!("expected referenced string-slice array"),
        },
        syn::Expr::Array(array) => array,
        _ => panic!("expected string-slice array"),
    };

    array.elems.iter().map(parse_string_lit).collect()
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
            entry["upstream_path"].as_str() == Some("source/rust_verify_test/tests/return.rs")
        })
        .expect("Verus manifest should contain return.rs row");

    row["expected_cases"]
        .as_array()
        .expect("return.rs manifest row should contain expected_cases")
        .iter()
        .map(|case| ExpectedCase {
            case: case["case_id"]
                .as_str()
                .expect("manifest case should contain case_id")
                .to_string(),
            upstream_case: case
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

fn return_rs_error_fragments(case: &str) -> Option<&'static [&'static str]> {
    Some(match case {
        "return_from_if_let_expression_contract" => &[
            "ambiguous multi-path return extraction",
            "if-let explicit return path",
        ],
        "return_from_let_else_contract" => &[
            "Failed to lower obligation 'return_value'",
            "unresolved variable `value`",
        ],
        "return_from_call_argument_contract" => &[
            "ambiguous multi-path return extraction",
            "unsupported nested explicit return path",
        ],
        "return_from_match_binding_contract_currently_errors"
        | "return_from_match_guard_contract_currently_errors" => &[
            "ambiguous multi-path return extraction",
            "match explicit return path",
        ],
        "nested_return_value_currently_errors" => &[
            "ambiguous multi-path return extraction",
            "nested explicit return in return value",
        ],
        "non_tail_local_initializer_return_currently_errors" => &[
            "ambiguous multi-path return extraction",
            "local initializer explicit return path",
        ],
        "return_with_nested_impl_method_contract" => &[
            "Unsupported nested struct item in function body",
            "nested items are rejected",
        ],
        "spec_fun_returning_unit_returns_clause_currently_rejected" => {
            &["spec functions cannot have `returns` clause"]
        }
        // The no-self UFCS call now renders with the CONCRETE self type
        // (`bool::…`) rather than the trait-qualified name (49d16b3); the empty
        // impl inherits the trait DEFAULT body, which the concrete no-self
        // registration does not yet cover, so this stays soundly fail-closed —
        // only the symbol named in the message changed.
        "default_trait_return_unit_concrete_call_issue1108" => &[
            "unknown return type",
            "bool::default_trait_return_unit_issue1108",
        ],
        _ => return None,
    })
}

const RETURNS_POSTCONDITION_VERIFIED_CASES: &[(&str, &str)] = &[
    ("returns_basic_value", "returns_basic"),
    ("proof_returns_basic_value", "returns_basic"),
    ("returns_basic_call_uses_return_value", "returns_basic"),
    ("returns_basic_explicit_sum_return_value", "returns_basic"),
    ("returning_unit_value_ok", "returning_unit_value"),
    ("returns_basic_direct_attr_value", "returns_basic"),
    ("proof_returns_basic_direct_attr_value", "returns_basic"),
    (
        "returns_basic_direct_attr_explicit_return_value",
        "returns_basic",
    ),
    (
        "returns_basic_direct_attr_legacy_ident_binding",
        "returns_basic",
    ),
    ("returns_basic_direct_attr_sum_value", "returns_basic"),
    (
        "returns_basic_direct_attr_bool_expression_value",
        "returns_basic",
    ),
    (
        "returning_unit_value_direct_attr_ok",
        "returning_unit_value",
    ),
    (
        "returns_reference_postcondition",
        "returns references ret param",
    ),
    (
        "returns_reference_direct_attr_postcondition",
        "returns references ret param",
    ),
    (
        "returns_recommends_body_call_positive",
        "returns_and_recommends_issue1834",
    ),
    (
        "returns_recommends_multi_arg_body_call_positive",
        "returns_and_recommends_issue1834",
    ),
    (
        "default_trait_returns_inherited_positive",
        "default_trait_fn_with_returns",
    ),
    ("default_returns_input", "default_trait_fn_with_returns"),
    (
        "inherited_returns_true_positive",
        "trait_returns_on_trait_method_decl",
    ),
    ("impl_returns_true", "trait_returns_on_trait_method_impl"),
    // recommends is ADVISORY (72829a9): a body call VIOLATING a source-spec
    // recommends no longer forces a Counterexample; the asserted result
    // (identity(10)==10, product(10,3)==30) genuinely holds ⇒ Verified.
    (
        "returns_recommends_body_call_violates",
        "returns_and_recommends_issue1834",
    ),
    (
        "returns_recommends_multi_arg_body_call_violates",
        "returns_and_recommends_issue1834",
    ),
];

const RETURNS_POSTCONDITION_COUNTEREXAMPLE_CASES: &[(&str, &str)] = &[
    ("returns_basic_wrong_value", "returns_basic"),
    ("returns_basic_wrong_explicit_return", "returns_basic"),
    ("returns_basic_wrong_sum_return", "returns_basic"),
    ("returns_basic_stronger_ensures_fails", "returns_basic"),
    ("proof_returns_basic_wrong_sum_return", "returns_basic"),
    (
        "proof_returns_basic_stronger_ensures_fails",
        "returns_basic",
    ),
    ("returns_basic_explicit_sum_return_wrong", "returns_basic"),
    ("returning_unit_value_fails", "returning_unit_value"),
    ("returns_basic_direct_attr_wrong_value", "returns_basic"),
    (
        "returns_basic_direct_attr_wrong_explicit_return",
        "returns_basic",
    ),
    (
        "returns_basic_direct_attr_wrong_sum_return",
        "returns_basic",
    ),
    (
        "returns_basic_direct_attr_bool_expression_wrong",
        "returns_basic",
    ),
    (
        "returns_reference_postcondition_wrong",
        "returns references ret param",
    ),
    (
        "returns_reference_direct_attr_postcondition_wrong",
        "returns references ret param",
    ),
    ("default_returns_false", "default_trait_fn_with_returns2"),
    (
        "default_returns_wrong_input",
        "default_trait_fn_with_returns2",
    ),
    (
        "inherited_returns_true",
        "trait_returns_on_trait_method_decl",
    ),
    ("impl_returns_false", "trait_returns_on_trait_method_impl"),
];

const RETURNS_POSTCONDITION_FAIL_CLOSED_ERROR_CASES: &[(&str, &str, &[&str])] = &[
    (
        "returns_basic_direct_attr_unresolved_sum_return",
        "returns_basic",
        &["unresolved variable `b`"],
    ),
    (
        "returns_basic_direct_attr_literal_type_mismatch",
        "returns diagnostics",
        &["type of `returns` clause does not match function return type"],
    ),
    (
        "returns_reference_direct_attr_char_referent_rejected",
        "returns references ret param",
        &["unsupported direct #[returns] shared-reference identifier `x`"],
    ),
    (
        "returns_mut_ref_bool_current_value_currently_rejected",
        "allow_in_spec_mut_ref",
        &[
            "unsupported unary operator",
            "dereference expressions are not supported in verification syntax",
        ],
    ),
    (
        "spec_direct_returns_clause_rejected",
        "returns diagnostics",
        &["spec functions cannot have `returns` clause"],
    ),
    (
        "spec_grouped_returns_clause_rejected",
        "returns diagnostics",
        &["spec functions cannot have `returns` clause"],
    ),
    (
        "spec_direct_returns_expression_rejected",
        "spec_fn_returns",
        &["spec functions cannot have `returns` clause"],
    ),
    (
        "conflicting_returns_clause",
        "default_trait_fn_with_returns_conflict/trait_returns_conflict",
        &["a `returns` clause cannot be declared on both a trait method impl and its declaration"],
    ),
    (
        "conflicting_grouped_returns_clause",
        "trait_returns_conflict grouped contract",
        &["a `returns` clause cannot be declared on both a trait method impl and its declaration"],
    ),
];

#[test]
fn return_rs_port_file_is_rust_syntax() {
    parse_return_port_file();
}

#[test]
fn return_rs_pinned_upstream_case_shapes_are_present() {
    let path = pinned_upstream_return_path();
    if !path.exists() {
        eprintln!(
            "skipping pinned upstream return.rs shape check; missing {}",
            path.display()
        );
        return;
    }

    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", path.display()));
    for expected in [
        "#[test] test1",
        "#[test] test1_fails1",
        "#[test] test1_fails2",
        "#[test] test2",
        "#[test] test2_fails",
        "#[test] test3",
        "#[test] test3_fails",
        "#[test] regression_215",
        "#[test] returning_named_unit_issue1108",
        "#[test] return_unit_trait_issue1278",
        "#[test] trait_clone_unit_issue1108",
        "#[test] trait_impl_return_unit_issue1108",
        "#[test] generic_spec_funs_returning_unit_issue1108",
        "fn test_ret(b: bool) -> (i: u64)",
        "while b || !b",
        "invariant b",
        "return ();",
        "proof fn f() -> (n: ())",
        "proof fn g() -> (n: ())",
        "spec fn g<A: T>()",
        "return; // FAILS",
    ] {
        assert!(
            source.contains(expected),
            "pinned upstream return.rs should still contain {expected}"
        );
    }
}

#[test]
fn return_rs_expected_case_metadata_is_schema_valid() {
    let (source, file) = parse_return_port_file();
    assert!(
        source.contains("RETURN_RS_EXPECTED_CASES")
            && source.contains("pub fn return_rs_expected_cases")
            && source.contains("RETURN_RS_EXPECTED_ERROR_PATTERNS")
            && source.contains("pub fn return_rs_expected_error_patterns")
            && source.contains("RETURN_RS_UNPROMOTED_UPSTREAM_CASES")
            && source.contains("pub fn return_rs_unpromoted_upstream_cases"),
        "return port should expose expected-case, error-pattern, and unpromoted-upstream metadata/accessors"
    );

    let cases = parse_return_metadata_entries();
    assert!(
        !cases.is_empty(),
        "return port metadata should list expected cases"
    );

    let mut seen = BTreeSet::new();
    for expected in &cases {
        assert!(
            seen.insert(expected.case.clone()),
            "return port metadata should not duplicate case {}",
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
                return_rs_error_fragments(&expected.case).is_some(),
                "{} error metadata should have pinned diagnostic fragments",
                expected.case
            );
            assert!(
                !expected.expected_error_patterns.is_empty(),
                "{} error metadata should declare expected manifest error patterns",
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
                "{} non-error metadata should not declare error patterns",
                expected.case
            );
        }
        assert!(
            find_function_owned(&file, &expected.case).is_some(),
            "{} should exist in the return port",
            expected.case
        );
    }

    let unpromoted_cases =
        parse_unpromoted_upstream_case_metadata(&file, "RETURN_RS_UNPROMOTED_UPSTREAM_CASES");
    assert!(
        !unpromoted_cases.is_empty(),
        "return port should explicitly list upstream return.rs cases not claimed as evidence"
    );

    let expected_case_ids = cases
        .iter()
        .map(|expected| expected.case.as_str())
        .collect::<BTreeSet<_>>();
    let mut seen_unpromoted = BTreeSet::new();
    for unpromoted in &unpromoted_cases {
        assert!(
            seen_unpromoted.insert(unpromoted.upstream_case.clone()),
            "unpromoted upstream metadata should not duplicate {}",
            unpromoted.upstream_case
        );
        assert!(
            !unpromoted.reason.is_empty(),
            "{} should document why it is still unsupported",
            unpromoted.upstream_case
        );
        assert!(
            !unpromoted.reason.to_ascii_lowercase().contains("unknown"),
            "{} should not cite solver Unknown as evidence",
            unpromoted.upstream_case
        );
        assert!(
            !expected_case_ids.contains(unpromoted.upstream_case.as_str()),
            "{} should not be both accepted evidence and an unpromoted upstream case",
            unpromoted.upstream_case
        );
    }
}

#[test]
fn return_rs_expected_case_metadata_matches_manifest_exactly() {
    assert_eq!(
        parse_return_metadata_entries(),
        manifest_expected_metadata()
    );
}

#[test]
fn return_rs_unpromoted_upstream_cases_remain_shape_pinned() {
    let path = pinned_upstream_return_path();
    if !path.exists() {
        eprintln!(
            "skipping pinned upstream return.rs unpromoted-case check; missing {}",
            path.display()
        );
        return;
    }

    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", path.display()));
    for unpromoted in parse_return_unpromoted_upstream_cases() {
        let test_marker = format!("#[test] {}", unpromoted.upstream_case);
        assert!(
            source.contains(&test_marker),
            "pinned upstream return.rs should still contain unpromoted case marker {test_marker}"
        );
    }
}

#[test]
fn return_rs_expected_cases_match_declared_statuses_and_obligations() {
    let path = return_port_path();
    let path_str = path.to_str().expect("return.rs port path should be UTF-8");
    let (_, file) = parse_return_port_file();
    let cases = parse_return_expected_cases();

    for expected in &cases {
        match expected.status.as_str() {
            "verified" | "counterexample" => {
                let function = find_function_owned(&file, &expected.case).unwrap_or_else(|| {
                    panic!(
                        "{} ({}) should exist in the return port",
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
                    return_rs_error_fragments(&expected.case).unwrap_or_else(|| {
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

#[test]
fn returns_postcondition_direct_attr_subset_verifies_from_file() {
    let path = port_path("returns_postcondition.rs");
    let path = path
        .to_str()
        .expect("returns_postcondition.rs port path should be UTF-8");

    for (case, upstream_case) in RETURNS_POSTCONDITION_VERIFIED_CASES {
        let result = verify_case(path, case, upstream_case);
        assert!(
            matches!(result, VerifyResult::Verified),
            "{case} ({upstream_case}) should verify, got: {result:?}"
        );
    }
}

#[test]
fn returns_postcondition_direct_attr_counterexamples_are_rejected_from_file() {
    let path = port_path("returns_postcondition.rs");
    let path = path
        .to_str()
        .expect("returns_postcondition.rs port path should be UTF-8");

    for (case, upstream_case) in RETURNS_POSTCONDITION_COUNTEREXAMPLE_CASES {
        let result = verify_case(path, case, upstream_case);
        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "{case} ({upstream_case}) should be rejected, got: {result:?}"
        );
    }
}

#[test]
fn returns_postcondition_direct_attr_blockers_fail_closed_from_file() {
    let path = port_path("returns_postcondition.rs");
    let path = path
        .to_str()
        .expect("returns_postcondition.rs port path should be UTF-8");

    for (case, upstream_case, expected_fragments) in RETURNS_POSTCONDITION_FAIL_CLOSED_ERROR_CASES {
        expect_fail_closed(path, case, upstream_case, expected_fragments);
    }
}
