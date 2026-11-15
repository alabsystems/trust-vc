// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Executable guards for the current upstream regression.rs partial port.
//!
//! These tests intentionally do not claim full Verus regression.rs parity. They
//! verify only the listed upstream-derived witnesses and parse guards while the
//! manifest keeps the file fail-closed until the broader heterogeneous corpus is
//! covered. Solver `Unknown` is not accepted as evidence.

mod common;

use std::{
    collections::{BTreeMap, BTreeSet},
    path::{Path, PathBuf},
};
use trust_vc_core::{
    extract_verification_conditions_with_file_context, verify_function_from_file, VerifyResult,
};

fn regression_port_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/ported/regression.rs")
}

fn pinned_upstream_regression_path() -> PathBuf {
    common::pinned_verus_test_path("regression.rs")
}

fn verus_manifest_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/verus-tests.json")
}

fn port_file() -> syn::File {
    let source = std::fs::read_to_string(regression_port_path())
        .expect("regression port should be readable");
    syn::parse_file(&source).expect("regression port should parse as ordinary Rust syntax")
}

fn port_function(items: &[syn::Item], case: &str, upstream_case: &str) -> Option<syn::ItemFn> {
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
                    if let Some(function) = port_function(inner_items, case, upstream_case) {
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

    let _ = upstream_case;
    None
}

fn verify_case(case: &str, upstream_case: &str) -> (VerifyResult, usize) {
    let file = port_file();
    let function = port_function(&file.items, case, upstream_case)
        .unwrap_or_else(|| panic!("{case} ({upstream_case}) should exist in regression port"));
    let vc = extract_verification_conditions_with_file_context(&file, &function)
        .unwrap_or_else(|err| panic!("{case} ({upstream_case}) should extract: {err}"));
    let obligations = vc.obligations().len();
    let result = vc.verify();

    if let VerifyResult::Unknown { reason, .. } = &result {
        panic!(
            "{case} ({upstream_case}) returned solver Unknown, which is not stable evidence: {reason}"
        );
    }

    (result, obligations)
}

fn fail_closed_message(case: &str, upstream_case: &str) -> String {
    let path = regression_port_path();
    let path = path.to_str().expect("regression port path should be UTF-8");

    match verify_function_from_file(path, case) {
        Err(err) => err.to_string(),
        Ok(VerifyResult::Error { message }) => message,
        Ok(VerifyResult::Unknown { reason, .. }) => {
            panic!("{case} ({upstream_case}) returned solver Unknown, which is not stable evidence: {reason}")
        }
        Ok(other) => {
            panic!("{case} ({upstream_case}) should fail closed with Error, got: {other:?}")
        }
    }
}

fn literal_string(expr: &syn::Expr) -> String {
    match expr {
        syn::Expr::Lit(syn::ExprLit {
            lit: syn::Lit::Str(lit),
            ..
        }) => lit.value(),
        _ => panic!("expected string literal in metadata"),
    }
}

fn literal_usize(expr: &syn::Expr) -> usize {
    match expr {
        syn::Expr::Lit(syn::ExprLit {
            lit: syn::Lit::Int(lit),
            ..
        }) => lit
            .base10_parse::<usize>()
            .unwrap_or_else(|err| panic!("expected usize literal in metadata: {err}")),
        _ => panic!("expected usize literal in metadata"),
    }
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
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
        .unwrap_or_else(|| panic!("regression port should define {const_name}"));

    let syn::Expr::Reference(reference) = const_item.expr.as_ref() else {
        panic!("{const_name} should be a referenced array");
    };
    let syn::Expr::Array(array) = reference.expr.as_ref() else {
        panic!("{const_name} should reference an array");
    };
    array.clone()
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
    let array = referenced_array_const(file, "REGRESSION_RS_EXPECTED_ERROR_PATTERNS");
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

fn parse_expected_case_metadata(file: &syn::File) -> Vec<CaseMetadata> {
    let array = referenced_array_const(file, "REGRESSION_RS_EXPECTED_CASES");
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
            "duplicate regression metadata for {case_id}"
        );
        entries.push(CaseMetadata {
            expected_error_patterns: error_patterns.remove(&case_id).unwrap_or_default(),
            case_id,
            upstream_case_id: literal_string(&tuple.elems[1]),
            expected_verdict: literal_string(&tuple.elems[2]),
            min_obligations: literal_usize(&tuple.elems[3]),
        });
    }

    assert!(
        error_patterns.is_empty(),
        "error-pattern metadata should not contain orphan cases: {error_patterns:?}"
    );
    entries
}

fn expected_metadata_from_tests() -> Vec<CaseMetadata> {
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

    let mut metadata = Vec::new();
    for (case, upstream_case, min_obligations) in VERIFIED_CASES {
        metadata.push(CaseMetadata {
            case_id: (*case).to_string(),
            upstream_case_id: (*upstream_case).to_string(),
            expected_verdict: "verified".to_string(),
            min_obligations: *min_obligations,
            expected_error_patterns: Vec::new(),
        });
    }
    for (case, upstream_case, min_obligations) in COUNTEREXAMPLE_CASES {
        metadata.push(CaseMetadata {
            case_id: (*case).to_string(),
            upstream_case_id: (*upstream_case).to_string(),
            expected_verdict: "counterexample".to_string(),
            min_obligations: *min_obligations,
            expected_error_patterns: Vec::new(),
        });
    }
    for (case, upstream_case, _) in FAIL_CLOSED_CASES {
        metadata.push(CaseMetadata {
            case_id: (*case).to_string(),
            upstream_case_id: (*upstream_case).to_string(),
            expected_verdict: "error".to_string(),
            min_obligations: 0,
            expected_error_patterns: error_patterns.remove(case).unwrap_or_default(),
        });
    }
    metadata.sort();
    metadata
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
            entry["upstream_path"].as_str() == Some("source/rust_verify_test/tests/regression.rs")
        })
        .expect("Verus manifest should contain regression.rs row");

    row["expected_cases"]
        .as_array()
        .expect("regression.rs row should contain expected_cases")
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

fn has_case_contract_attr(function: &syn::ItemFn) -> bool {
    function.attrs.iter().any(|attr| {
        attr.path()
            .segments
            .last()
            .is_some_and(|segment| segment.ident == "ensures" || segment.ident == "contract")
    })
}

fn collect_case_function_names(items: &[syn::Item], names: &mut Vec<String>) {
    for item in items {
        match item {
            syn::Item::Fn(function) if has_case_contract_attr(function) => {
                names.push(function.sig.ident.to_string());
            }
            syn::Item::Mod(module) => {
                if let Some((_, inner_items)) = &module.content {
                    collect_case_function_names(inner_items, names);
                }
            }
            syn::Item::Impl(impl_block) => {
                for impl_item in &impl_block.items {
                    if let syn::ImplItem::Fn(method) = impl_item {
                        let function = syn::ItemFn {
                            attrs: method.attrs.clone(),
                            vis: method.vis.clone(),
                            sig: method.sig.clone(),
                            block: Box::new(method.block.clone()),
                        };
                        if has_case_contract_attr(&function) {
                            names.push(function.sig.ident.to_string());
                        }
                    }
                }
            }
            syn::Item::Trait(trait_block) => {
                for trait_item in &trait_block.items {
                    if let syn::TraitItem::Fn(method) = trait_item {
                        if let Some(block) = &method.default {
                            let function = syn::ItemFn {
                                attrs: method.attrs.clone(),
                                vis: syn::Visibility::Inherited,
                                sig: method.sig.clone(),
                                block: Box::new(block.clone()),
                            };
                            if has_case_contract_attr(&function) {
                                names.push(function.sig.ident.to_string());
                            }
                        }
                    }
                }
            }
            _ => {}
        }
    }
}

const VERIFIED_CASES: &[(&str, &str, usize)] = &[
    ("regression_test_189a_set_insert_membership", "test_189a", 1),
    (
        "regression_test_189b_empty_set_witness_membership",
        "test_189b",
        1,
    ),
    (
        "regression_truncate_cast_u64_to_u8",
        "test_verifier_truncate_allowed_on_cast",
        1,
    ),
    (
        "regression_identifier_shadowing_model",
        "test_hygienic_identifiers_regression_279",
        1,
    ),
    (
        "regression_field_access_model",
        "fields_from_macros_not_treated_as_distinct_identifiers",
        1,
    ),
    (
        "regression_named_map_return_caller",
        "parse_named_return_type_with_comma_in_type_args",
        1,
    ),
    (
        "regression_named_map_return_type_with_comma",
        "parse_named_return_type_with_comma_in_type_args",
        1,
    ),
    (
        "regression_return_keyword_result_postcondition",
        "forall_in_ensures_with_return_keyword_regression_216",
        1,
    ),
    (
        "regression_lifetime_constructor_option_none",
        "test_lifetime_constructor_regression_768",
        1,
    ),
    (
        "regression_lifetime_assoc_type_constructor_issue769",
        "lifetime_generate_assoc_type_regression_769",
        1,
    ),
    (
        "regression_parsing_unit_ret_type_issue937",
        "parsing_unit_ret_type_issue937",
        1,
    ),
    (
        "regression_named_unit_return_issue937",
        "parsing_unit_ret_type_issue937",
        1,
    ),
    (
        "regression_struct_update_generic_field_subst",
        "struct_with_updater_and_typ_subst_in_field_issue956",
        1,
    ),
    (
        "regression_arithmetic_trigger_choose",
        "arithmetic_trigger_choose_issue923",
        1,
    ),
    (
        "regression_fieldless_enum_regression_1339",
        "fieldless_enum_regression_1339",
        1,
    ),
    (
        "regression_derive_clone_copy_enum",
        "derive_regression_1575",
        1,
    ),
    (
        "regression_field_update_map_insert_issue1591",
        "field_update_regression_1591",
        1,
    ),
    (
        "regression_tuple_copy_bound_issue2211",
        "tuple_copy_bound_issue2211",
        1,
    ),
];

const COUNTEREXAMPLE_CASES: &[(&str, &str, usize)] = &[
    (
        "regression_identifier_shadowing_wrong_value_counterexample",
        "test_hygienic_identifiers_regression_279",
        1,
    ),
    (
        "regression_return_keyword_assert_false_counterexample",
        "forall_in_ensures_with_return_keyword_regression_216",
        1,
    ),
];

const FAIL_CLOSED_CASES: &[(&str, &str, &[&str])] = &[
    (
        "regression_let_with_parens_issue260",
        "let_with_parens_issue_260",
        &["unresolved variable `x`", "Failed to lower obligation"],
    ),
    (
        "regression_verus_not_ext_equal_syntax_currently_errors",
        "test_189a",
        &["Failed to parse assert!() expression", "!==", "unexpected"],
    ),
    (
        "regression_verus_exists_syntax_currently_errors",
        "test_189b",
        &["Failed to parse assert!() expression", "exists"],
    ),
    (
        "regression_macro_argument_hygiene_currently_errors",
        "test_hygienic_identifiers_regression_279",
        &[
            "Unsupported nested macro_rules! item",
            "only an empty `()` matcher is supported",
        ],
    ),
    (
        "regression_reveal_exec_fn_currently_errors",
        "reveal_exec_fn_issue_411",
        &[
            "reveal!(regression_exec_reveal_target) references unknown function",
            "Available functions",
        ],
    ),
    (
        "regression_qualified_module_reveal_currently_errors",
        "reveal_func_unused_from_other_module_issue_411",
        &["supports only unqualified function names"],
    ),
    (
        "regression_reveal_with_fuel_currently_errors",
        "reveal_with_fuel_non_opaque_non_recursive_issue236_373_fail",
        &[
            "Unsupported reveal_with_fuel!()",
            "unsupported macros are rejected",
        ],
    ),
    (
        "regression_nested_module_item_currently_errors",
        "test_modules_nested_in_items_external_code",
        &["Unsupported nested mod item in function body"],
    ),
];

#[test]
fn regression_rs_port_file_is_rust_syntax() {
    let source = std::fs::read_to_string(regression_port_path())
        .expect("regression port should be readable");
    syn::parse_file(&source).expect("regression port should parse as ordinary Rust syntax");
}

#[test]
fn regression_rs_pinned_upstream_case_shapes_are_present() {
    let path = pinned_upstream_regression_path();
    if !path.exists() {
        eprintln!(
            "skipping pinned upstream regression.rs shape check; missing {}",
            path.display()
        );
        return;
    }

    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", path.display()));
    for expected in [
        "#[test] test_189a",
        "#[test] test_189b",
        "assert(s1 !== s2);",
        "assert (exists|s3: Set<i32>|",
        "macro_rules! assert_with_binding",
        "macro_rules! recursor",
        "macro_rules! iterer",
        "reveal(X::foo);",
        "reveal(foo);",
        "reveal_with_fuel(is_true, 1);",
        "reveal_with_fuel(is_true, 2);",
        "#[verifier(opaque)]",
        "#[verifier::opaque]",
        "#[verifier::external]",
        "#[test] let_with_parens_issue_260",
        "#[test] test_lifetime_constructor_regression_768",
        "#[test] lifetime_generate_assoc_type_regression_769",
        "#[test] nested_macros_regression_866",
        "#[test] parsing_unit_ret_type_issue937",
        "#[test] struct_with_updater_and_typ_subst_in_field_issue956",
        "#[test] external_module_issue618",
        "#[test] arithmetic_trigger_choose_issue923",
        "#[test] test_modules_nested_in_items_external_code",
        "#[test] field_update_regression_1591",
        "#[test] well_formed_pattern_check_issue1741",
        "#[test] tuple_copy_bound_issue2211",
        "#[test] no_verus_attribute_warning_issue2211",
        "verus! {",
        "mod X {",
        "disallowed: pattern constructor for an opaque datatype",
    ] {
        assert!(
            source.contains(expected),
            "pinned upstream regression.rs should still contain {expected}"
        );
    }
}

#[test]
fn regression_rs_expected_case_metadata_is_exact_and_excludes_unknown() {
    let file = port_file();
    let mut actual = parse_expected_case_metadata(&file);
    actual.sort();

    let expected = expected_metadata_from_tests();

    assert_eq!(actual, expected);
    assert!(
        actual.iter().all(|case| matches!(
            case.expected_verdict.as_str(),
            "verified" | "counterexample" | "error"
        )),
        "regression metadata must contain only schema-valid stable verdicts"
    );
}

#[test]
fn regression_rs_expected_case_metadata_matches_manifest() {
    let file = port_file();
    assert_eq!(
        parse_expected_case_metadata(&file),
        manifest_expected_metadata(),
        "regression.rs manifest expected_cases should match port metadata and error patterns exactly"
    );
}

#[test]
fn regression_rs_port_inventory_stays_intentional() {
    let file = port_file();
    let mut observed = Vec::new();
    collect_case_function_names(&file.items, &mut observed);
    observed.sort();

    let mut expected = expected_metadata_from_tests()
        .into_iter()
        .map(|case| case.case_id)
        .collect::<Vec<_>>();
    expected.sort();

    assert_eq!(
        observed, expected,
        "regression.rs port should expose only intentional expected-case functions"
    );
}

#[test]
fn regression_rs_verified_subset_verifies_from_file() {
    for (case, upstream_case, min_obligations) in VERIFIED_CASES {
        let (result, obligation_count) = verify_case(case, upstream_case);
        assert!(
            obligation_count >= *min_obligations,
            "{case} ({upstream_case}) should collect at least {min_obligations} obligation(s), got {obligation_count}"
        );
        assert!(
            matches!(result, VerifyResult::Verified),
            "{case} ({upstream_case}) should verify, got: {result:?}"
        );
    }
}

#[test]
fn regression_rs_counterexample_subset_is_rejected_from_file() {
    for (case, upstream_case, min_obligations) in COUNTEREXAMPLE_CASES {
        let (result, obligation_count) = verify_case(case, upstream_case);
        assert!(
            obligation_count >= *min_obligations,
            "{case} ({upstream_case}) should collect at least {min_obligations} obligation(s), got {obligation_count}"
        );
        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "{case} ({upstream_case}) should produce a counterexample, got: {result:?}"
        );
    }
}

/// Every case is checked before the test fails, so one red case cannot hide a
/// later one that verifies.
#[test]
fn regression_rs_unsupported_boundaries_fail_closed_from_file() {
    let mut failures = Vec::new();
    for (case, upstream_case, expected_fragments) in FAIL_CLOSED_CASES {
        let outcome = std::panic::catch_unwind(|| fail_closed_message(case, upstream_case));
        match outcome {
            Ok(message) if expected_fragments.iter().any(|f| message.contains(f)) => {}
            Ok(message) => failures.push(format!(
                "{case} ({upstream_case}) error should contain one of {expected_fragments:?}, got: {message}"
            )),
            Err(payload) => failures.push(
                payload
                    .downcast_ref::<String>()
                    .cloned()
                    .unwrap_or_else(|| format!("{case} ({upstream_case}) panicked")),
            ),
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}
