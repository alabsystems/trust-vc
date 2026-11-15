// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Executable guards for the upstream default_trait.rs TrustVc scout slice.
//!
//! These tests intentionally do not claim full Verus default_trait.rs parity.
//! They parse the scout metadata from the port itself, reject solver `Unknown`
//! as replacement evidence, pin the type-directed `Default::default()`
//! constructor family (2026-09-13: the `<Ty>::default()`, `let b: Ty =
//! Default::default()` and `<Ty as core::default::Default>::default()`
//! spellings over primitives, `&str`, `String`, `Option`, `PhantomData`,
//! tuples, `Vec`/`VecDeque`/`HashMap`/`HashSet`, `Box`/`Rc`/`Arc`,
//! `#[derive(Default)]` and hand-written `impl Default` types, and a generic
//! `T::default()`), require a refuted liar twin for every modelled
//! constructor, and require the two remaining fail-closed boundaries (the
//! upstream `T::default.ensures((), r)` reflection contract and
//! `String::is_ascii()`) to carry precise error fragments while the corpus
//! entry remains `unsupported-gap`.

mod common;

use std::{
    collections::{BTreeMap, BTreeSet},
    path::{Path, PathBuf},
};
use trust_vc_core::{
    extract_verification_conditions_with_file_context, verify_function_from_file, VerifyResult,
};

type ExpectedCase = (
    &'static str,
    &'static str,
    &'static str,
    usize,
    &'static [&'static str],
);

#[derive(Debug, Eq, PartialEq)]
struct CaseMetadata {
    case_id: String,
    upstream_case_id: String,
    expected_verdict: String,
    min_obligations: usize,
    expected_error_patterns: Vec<String>,
}

fn default_trait_port_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/ported/default_trait.rs")
}

fn verus_manifest_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/verus-tests.json")
}

fn pinned_upstream_default_trait_path() -> PathBuf {
    common::pinned_verus_test_path("default_trait.rs")
}

fn port_source_and_ast() -> (String, syn::File) {
    let source = std::fs::read_to_string(default_trait_port_path())
        .expect("default_trait port should be readable");
    let ast =
        syn::parse_file(&source).expect("default_trait port should parse as ordinary Rust syntax");
    (source, ast)
}

fn verify_port_case(case: &str, upstream_case: &str) -> (VerifyResult, usize) {
    let (_source, file) = port_source_and_ast();
    let function = find_port_function(&file.items, case)
        .unwrap_or_else(|| panic!("{case} ({upstream_case}) should exist in default_trait port"));

    let vc = extract_verification_conditions_with_file_context(&file, &function)
        .unwrap_or_else(|err| panic!("{case} ({upstream_case}) should extract: {err}"));
    let obligation_count = vc.obligations().len();
    (vc.verify(), obligation_count)
}

fn find_port_function(items: &[syn::Item], case: &str) -> Option<syn::ItemFn> {
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
                    if let Some(function) = find_port_function(inner_items, case) {
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

fn collect_port_function_names(items: &[syn::Item], names: &mut Vec<String>) {
    for item in items {
        match item {
            syn::Item::Fn(function) => {
                let name = function.sig.ident.to_string();
                if !matches!(
                    name.as_str(),
                    "default_trait_rs_expected_cases"
                        | "default_trait_rs_fail_closed_error_patterns"
                ) {
                    names.push(name);
                }
            }
            syn::Item::Impl(impl_block) => {
                // A `impl Default for S { fn default() .. }` method is the
                // Rust-required half of a ported custom-type shape (upstream
                // `test_default_custom_type_spec` / `..._in_smart_ptrs`), not a
                // witness of its own: the witnesses are the functions that CALL
                // it. Inherent-impl methods stay inventoried.
                if impl_block.trait_.is_some() {
                    continue;
                }
                for impl_item in &impl_block.items {
                    if let syn::ImplItem::Fn(method) = impl_item {
                        names.push(method.sig.ident.to_string());
                    }
                }
            }
            syn::Item::Mod(module) => {
                if let Some((_, inner_items)) = &module.content {
                    collect_port_function_names(inner_items, names);
                }
            }
            syn::Item::Trait(trait_block) => {
                for trait_item in &trait_block.items {
                    if let syn::TraitItem::Fn(method) = trait_item {
                        if method.default.is_some() {
                            names.push(method.sig.ident.to_string());
                        }
                    }
                }
            }
            _ => {}
        }
    }
}

fn expect_fail_closed(case: &CaseMetadata) {
    let path = default_trait_port_path();
    let path = path
        .to_str()
        .expect("default_trait port path should be UTF-8");

    let message = match verify_function_from_file(path, &case.case_id) {
        Ok(VerifyResult::Error { message }) => message,
        Ok(VerifyResult::Unknown { reason, .. }) => {
            panic!(
                "{} ({}) returned solver Unknown, which is not stable evidence: {reason}",
                case.case_id, case.upstream_case_id
            )
        }
        Ok(result) => {
            panic!(
                "{} ({}) should fail closed with Error, got: {result:?}",
                case.case_id, case.upstream_case_id
            )
        }
        Err(err) => err.to_string(),
    };

    for expected_fragment in &case.expected_error_patterns {
        assert!(
            message.contains(expected_fragment),
            "{} ({}) error should contain {expected_fragment:?}, got: {message}",
            case.case_id,
            case.upstream_case_id
        );
    }
}

fn reject_unknown(result: &VerifyResult, case: &CaseMetadata) {
    if let VerifyResult::Unknown { reason, .. } = result {
        panic!(
            "{} ({}) returned solver Unknown, which is not stable evidence: {reason}",
            case.case_id, case.upstream_case_id
        );
    }
}

fn literal_string(expr: &syn::Expr) -> String {
    match expr {
        syn::Expr::Lit(syn::ExprLit {
            lit: syn::Lit::Str(lit),
            ..
        }) => lit.value(),
        _ => panic!("expected string literal in default_trait metadata"),
    }
}

fn literal_usize(expr: &syn::Expr) -> usize {
    match expr {
        syn::Expr::Lit(syn::ExprLit {
            lit: syn::Lit::Int(lit),
            ..
        }) => lit.base10_parse::<usize>().unwrap_or_else(|err| {
            panic!("expected usize literal in default_trait metadata: {err}")
        }),
        _ => panic!("expected usize literal in default_trait metadata"),
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

fn referenced_array_const<'a>(file: &'a syn::File, const_name: &str) -> &'a syn::ExprArray {
    let const_item = file
        .items
        .iter()
        .find_map(|item| match item {
            syn::Item::Const(item) if item.ident == const_name => Some(item),
            _ => None,
        })
        .unwrap_or_else(|| panic!("default_trait port should define {const_name}"));

    let syn::Expr::Reference(reference) = const_item.expr.as_ref() else {
        panic!("{const_name} should be a referenced array");
    };
    let syn::Expr::Array(array) = reference.expr.as_ref() else {
        panic!("{const_name} should reference an array");
    };

    array
}

fn error_pattern_entries(file: &syn::File) -> BTreeMap<String, Vec<String>> {
    let array = referenced_array_const(file, "DEFAULT_TRAIT_RS_FAIL_CLOSED_ERROR_PATTERNS");
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
    let array = referenced_array_const(file, "DEFAULT_TRAIT_RS_EXPECTED_CASES");
    let mut error_patterns = error_pattern_entries(file);
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
        let patterns = error_patterns.remove(&case_id).unwrap_or_default();
        entries.push(CaseMetadata {
            case_id,
            upstream_case_id: literal_string(&tuple.elems[1]),
            expected_verdict: literal_string(&tuple.elems[2]),
            min_obligations: literal_usize(&tuple.elems[3]),
            expected_error_patterns: patterns,
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
            |(
                case_id,
                upstream_case_id,
                expected_verdict,
                min_obligations,
                expected_error_patterns,
            )| CaseMetadata {
                case_id: (*case_id).to_string(),
                upstream_case_id: (*upstream_case_id).to_string(),
                expected_verdict: (*expected_verdict).to_string(),
                min_obligations: *min_obligations,
                expected_error_patterns: expected_error_patterns
                    .iter()
                    .map(|pattern| (*pattern).to_string())
                    .collect(),
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
                == Some("source/rust_verify_test/tests/default_trait.rs")
        })
        .expect("Verus manifest should contain default_trait.rs row");

    row["expected_cases"]
        .as_array()
        .expect("default_trait.rs row should contain expected_cases")
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
            expected_error_patterns: entry["expected_error_patterns"]
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

fn schema_identifier(value: &str) -> bool {
    let mut chars = value.chars();
    let Some(first) = chars.next() else {
        return false;
    };

    (first.is_ascii_alphabetic() || first == '_')
        && chars.all(|ch| ch.is_ascii_alphanumeric() || ch == '_')
}

const EXPECTED_CASES: &[ExpectedCase] = &[
    (
        "trust_vc_default_u32_zero_value_verified",
        "test_default_u32_ok",
        "verified",
        2,
        &[],
    ),
    (
        "trust_vc_default_u32_arithmetic_zero_verified",
        "test_default_arithmetic",
        "verified",
        3,
        &[],
    ),
    (
        "trust_vc_default_f32_zero_literal_verified",
        "test_default_f32_ok",
        "verified",
        2,
        &[],
    ),
    (
        "trust_vc_default_f64_zero_literal_verified",
        "test_default_f64_ok",
        "verified",
        2,
        &[],
    ),
    (
        "trust_vc_default_u32_wrong_value_counterexample",
        "test_default_u32_wrong",
        "counterexample",
        2,
        &[],
    ),
    (
        "trust_vc_default_bool_false_value_verified",
        "test_default_bool_ok",
        "verified",
        2,
        &[],
    ),
    (
        "trust_vc_default_option_u32_none_verified",
        "test_default_option_u32_ok",
        "verified",
        2,
        &[],
    ),
    (
        "trust_vc_default_tuple2_surrogate_verified",
        "test_default_tuple2_ok",
        "verified",
        3,
        &[],
    ),
    (
        "trust_vc_default_tuple3_surrogate_verified",
        "test_default_tuple3_ok",
        "verified",
        4,
        &[],
    ),
    (
        "trust_vc_default_record_verified",
        "test_default_custom_type_spec",
        "verified",
        4,
        &[],
    ),
    (
        "trust_vc_default_vec_new_empty_view_verified",
        "test_default_vec_u32_ok",
        "verified",
        2,
        &[],
    ),
    (
        "trust_vc_default_hash_map_direct_view_reflexive_verified",
        "test_default_hash_map_u32_ok",
        "verified",
        2,
        &[],
    ),
    (
        "trust_vc_default_hash_set_direct_view_reflexive_verified",
        "test_default_hash_set_u32_ok",
        "verified",
        2,
        &[],
    ),
    (
        "trust_vc_default_bool_wrong_value_counterexample",
        "test_default_bool_wrong",
        "counterexample",
        2,
        &[],
    ),
    (
        "rust_default_trait_inference_verified",
        "test_default_u32_ok",
        "verified",
        5,
        &[],
    ),
    (
        "rust_default_u32_associated_constructor_verified",
        "test_default_u32_ok",
        "verified",
        5,
        &[],
    ),
    (
        "rust_default_bool_associated_constructor_verified",
        "test_default_bool_ok",
        "verified",
        5,
        &[],
    ),
    (
        "rust_default_option_u32_associated_constructor_verified",
        "test_default_option_u32_ok",
        "verified",
        5,
        &[],
    ),
    (
        "rust_default_str_associated_constructor_verified",
        "test_default_str_ok",
        "verified",
        2,
        &[],
    ),
    (
        "rust_default_tuple2_associated_constructor_verified",
        "test_default_tuple2_ok",
        "verified",
        3,
        &[],
    ),
    (
        "rust_default_tuple3_associated_constructor_verified",
        "test_default_tuple3_ok",
        "verified",
        4,
        &[],
    ),
    (
        "rust_default_u32_ufcs_constructor_verified",
        "test_default_u32_ok",
        "verified",
        5,
        &[],
    ),
    (
        "rust_default_vec_u32_constructor_verified",
        "test_default_vec_u32_ok",
        "verified",
        5,
        &[],
    ),
    (
        "rust_default_string_constructor_verified",
        "test_default_string_ok",
        "verified",
        5,
        &[],
    ),
    (
        "rust_default_hash_map_constructor_verified",
        "test_default_hash_map_u32_ok",
        "verified",
        5,
        &[],
    ),
    (
        "rust_default_hash_set_constructor_verified",
        "test_default_hash_set_u32_ok",
        "verified",
        5,
        &[],
    ),
    (
        "rust_default_vec_deque_constructor_verified",
        "test_default_vec_deque_u32_ok",
        "verified",
        5,
        &[],
    ),
    (
        "rust_default_box_u32_constructor_verified",
        "test_default_box_u32_ok",
        "verified",
        5,
        &[],
    ),
    (
        "rust_default_box_vec_u32_constructor_verified",
        "test_default_box_vec_u32_ok",
        "verified",
        5,
        &[],
    ),
    (
        "rust_default_rc_u32_constructor_verified",
        "test_default_rc_u32_ok",
        "verified",
        5,
        &[],
    ),
    (
        "rust_default_arc_u32_constructor_verified",
        "test_default_arc_u32_ok",
        "verified",
        5,
        &[],
    ),
    (
        "rust_default_box_custom_type_constructor_verified",
        "test_default_custom_type_ensures_in_smart_ptrs",
        "verified",
        6,
        &[],
    ),
    (
        "rust_default_rc_custom_type_constructor_verified",
        "test_default_custom_type_ensures_in_smart_ptrs",
        "verified",
        6,
        &[],
    ),
    (
        "rust_default_arc_custom_type_constructor_verified",
        "test_default_custom_type_ensures_in_smart_ptrs",
        "verified",
        6,
        &[],
    ),
    (
        "rust_default_phantom_constructor_verified",
        "test_default_phantom_ok",
        "verified",
        5,
        &[],
    ),
    (
        "rust_default_generic_instantiation_verified",
        "test_default_generic_instantiation",
        "error",
        5,
        &["bodiless call repeated"],
    ),
    (
        "rust_default_trait_inference_wrong_counterexample",
        "test_default_u32_wrong",
        "counterexample",
        5,
        &[],
    ),
    (
        "rust_default_str_associated_constructor_wrong_counterexample",
        "test_default_str_ok",
        "counterexample",
        2,
        &[],
    ),
    (
        "rust_default_string_constructor_wrong_counterexample",
        "test_default_string_ok",
        "counterexample",
        5,
        &[],
    ),
    (
        "rust_default_vec_deque_constructor_wrong_counterexample",
        "test_default_vec_deque_u32_ok",
        "counterexample",
        5,
        &[],
    ),
    (
        "rust_default_box_u32_constructor_wrong_counterexample",
        "test_default_box_u32_ok",
        "counterexample",
        5,
        &[],
    ),
    (
        "rust_default_box_vec_u32_constructor_wrong_counterexample",
        "test_default_box_vec_u32_ok",
        "counterexample",
        5,
        &[],
    ),
    (
        "rust_default_rc_u32_constructor_wrong_counterexample",
        "test_default_rc_u32_ok",
        "counterexample",
        5,
        &[],
    ),
    (
        "rust_default_arc_u32_constructor_wrong_counterexample",
        "test_default_arc_u32_ok",
        "counterexample",
        5,
        &[],
    ),
    (
        "rust_default_box_custom_type_constructor_wrong_counterexample",
        "test_default_custom_type_ensures_in_smart_ptrs",
        "counterexample",
        5,
        &[],
    ),
    (
        "rust_default_phantom_constructor_wrong_counterexample",
        "test_default_phantom_ok",
        "counterexample",
        5,
        &[],
    ),
    (
        "rust_default_generic_instantiation_wrong_counterexample",
        "test_default_generic_instantiation",
        "counterexample",
        5,
        &[],
    ),
    (
        "upstream_test_default_u32_ok_verified",
        "test_default_u32_ok",
        "verified",
        7,
        &[],
    ),
    (
        "upstream_test_default_u32_wrong_counterexample",
        "test_default_u32_wrong",
        "counterexample",
        2,
        &[],
    ),
    (
        "upstream_test_default_bool_ok_verified",
        "test_default_bool_ok",
        "verified",
        7,
        &[],
    ),
    (
        "upstream_test_default_bool_wrong_counterexample",
        "test_default_bool_wrong",
        "counterexample",
        2,
        &[],
    ),
    (
        "upstream_test_default_f32_ok_verified",
        "test_default_f32_ok",
        "verified",
        7,
        &[],
    ),
    (
        "upstream_test_default_f64_ok_verified",
        "test_default_f64_ok",
        "verified",
        7,
        &[],
    ),
    (
        "upstream_test_default_f64_wrong_counterexample",
        "test_default_f64_ok",
        "counterexample",
        5,
        &[],
    ),
    (
        "upstream_test_default_str_ok_verified",
        "test_default_str_ok",
        "verified",
        7,
        &[],
    ),
    (
        "upstream_test_default_option_u32_ok_verified",
        "test_default_option_u32_ok",
        "verified",
        7,
        &[],
    ),
    (
        "upstream_test_default_option_u32_wrong_counterexample",
        "test_default_option_u32_ok",
        "counterexample",
        5,
        &[],
    ),
    (
        "upstream_test_default_phantom_ok_verified",
        "test_default_phantom_ok",
        "verified",
        7,
        &[],
    ),
    (
        "upstream_test_default_tuple2_ok_verified",
        "test_default_tuple2_ok",
        "verified",
        7,
        &[],
    ),
    (
        "upstream_test_default_tuple2_wrong_counterexample",
        "test_default_tuple2_ok",
        "counterexample",
        5,
        &[],
    ),
    (
        "upstream_test_default_tuple3_ok_verified",
        "test_default_tuple3_ok",
        "verified",
        7,
        &[],
    ),
    (
        "upstream_test_default_tuple3_wrong_counterexample",
        "test_default_tuple3_ok",
        "counterexample",
        2,
        &[],
    ),
    (
        "rust_default_custom_type_spec_mk_verified",
        "test_default_custom_type_spec",
        "verified",
        6,
        &[],
    ),
    (
        "rust_default_custom_type_spec_test_verified",
        "test_default_custom_type_spec",
        "verified",
        9,
        &[],
    ),
    (
        "rust_default_custom_type_spec_wrong_counterexample",
        "test_default_custom_type_spec",
        "counterexample",
        5,
        &[],
    ),
    (
        "rust_default_custom_type_ensures_in_smart_ptrs_verified",
        "test_default_custom_type_ensures_in_smart_ptrs",
        "verified",
        10,
        &[],
    ),
    (
        "rust_default_custom_type_ensures_in_smart_ptrs_wrong_counterexample",
        "test_default_custom_type_ensures_in_smart_ptrs",
        "counterexample",
        5,
        &[],
    ),
    (
        "rust_default_generic_mk_reflection_currently_blocked",
        "test_default_generic_instantiation",
        "error",
        0,
        &[
            "Failed to lower obligation 'postcondition'",
            "unsupported expression `T::default` in specification context",
        ],
    ),
    (
        "rust_default_string_is_ascii_currently_blocked",
        "test_default_string_ok",
        "error",
        0,
        &[
            "Failed to lower obligation 'assertion_1'",
            "unsupported method `is_ascii()",
        ],
    ),
];

#[test]
fn default_trait_rs_port_file_is_rust_syntax() {
    let (source, _ast) = port_source_and_ast();
    assert!(
        source.contains("pub const DEFAULT_TRAIT_RS_EXPECTED_CASES")
            && source.contains("default_trait_rs_expected_cases")
            && source.contains("pub const DEFAULT_TRAIT_RS_FAIL_CLOSED_ERROR_PATTERNS")
            && source.contains("default_trait_rs_fail_closed_error_patterns"),
        "default_trait scout should carry executable expected-case and error-pattern metadata"
    );
}

#[test]
fn default_trait_rs_pinned_upstream_case_shapes_are_present() {
    let path = pinned_upstream_default_trait_path();
    if !path.exists() {
        eprintln!(
            "skipping pinned upstream default_trait.rs shape check; missing {}",
            path.display()
        );
        return;
    }

    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", path.display()));
    assert_eq!(
        source.matches("test_verify_one_file!").count(),
        15,
        "pinned upstream default_trait.rs active harness count changed"
    );
    assert_eq!(
        source.matches("test_default_ok!").count(),
        9,
        "pinned upstream default_trait.rs primitive macro-pass count changed"
    );
    assert_eq!(
        source.matches("test_default_fail!").count(),
        2,
        "pinned upstream default_trait.rs primitive macro-fail count changed"
    );
    assert_eq!(
        source.matches("=> Err(e)").count(),
        1,
        "pinned upstream default_trait.rs should keep one failing upstream harness"
    );

    for expected in [
        "let a = <{ty}>::default();",
        "let b: {ty} = Default::default();",
        "let c = <{ty} as core::default::Default>::default();",
        "test_default_ok!(test_default_u32_ok, u32, 0u32)",
        "test_default_fail!(test_default_u32_wrong, u32, 1u32)",
        "test_default_ok!(test_default_bool_ok, bool, false)",
        "test_default_fail!(test_default_bool_wrong, bool, true)",
        "test_default_ok!(test_default_f32_ok, f32, 0.0f32)",
        "test_default_ok!(test_default_f64_ok, f64, 0.0f64)",
        "test_default_ok!(test_default_str_ok, &'static str, \"\")",
        "test_default_ok!(test_default_option_u32_ok, Option<u32>, Option::<u32>::None)",
        "test_default_ok!(test_default_tuple2_ok, (u32, bool), (0u32, false))",
        "test_default_ok!(test_default_tuple3_ok, (u32, bool, char), (0u32, false, '\\0'))",
        "#[test] test_default_string_ok",
        "#[test] test_default_vec_u32_ok",
        "#[test] test_default_hash_map_u32_ok",
        "#[test] test_default_hash_set_u32_ok",
        "#[test] test_default_box_u32_ok",
        "#[test] test_default_box_vec_u32_ok",
        "#[test] test_default_rc_u32_ok",
        "#[test] test_default_arc_u32_ok",
        "#[test] test_default_vec_deque_u32_ok",
        "#[test] test_default_arithmetic",
        "#[test] test_default_generic_instantiation",
        "#[test] test_default_custom_type_spec",
        "#[test] test_default_custom_type_ensures_in_smart_ptrs",
        "T::default.ensures((), r)",
        "Box<MyType> = Box::default()",
        "Rc<MyType> = Rc::default()",
        "Arc<MyType> = Arc::default()",
    ] {
        assert!(
            source.contains(expected),
            "pinned upstream default_trait.rs should still contain {expected}"
        );
    }

    let (_port_source, ast) = port_source_and_ast();
    for upstream_case_id in metadata_entries(&ast)
        .into_iter()
        .map(|case| case.upstream_case_id)
        .collect::<BTreeSet<_>>()
    {
        assert!(
            source.contains(&upstream_case_id),
            "pinned upstream default_trait.rs should contain metadata upstream case {upstream_case_id}"
        );
    }
}

#[test]
fn default_trait_rs_expected_case_metadata_is_exact_and_schema_valid() {
    let (_source, ast) = port_source_and_ast();
    let actual = metadata_entries(&ast);
    assert_eq!(
        actual,
        expected_metadata(),
        "default_trait port metadata should exactly match the regression inventory"
    );

    let mut seen_case_ids = BTreeSet::new();
    for case in &actual {
        assert!(
            seen_case_ids.insert(case.case_id.clone()),
            "duplicate metadata case_id {}",
            case.case_id
        );
        assert!(
            schema_identifier(&case.case_id),
            "{} should be a schema-valid case_id",
            case.case_id
        );
        assert!(
            schema_identifier(&case.upstream_case_id),
            "{} ({}) should be a schema-valid upstream_case_id",
            case.case_id,
            case.upstream_case_id
        );
        assert!(
            matches!(
                case.expected_verdict.as_str(),
                "verified" | "counterexample" | "error"
            ),
            "{} ({}) has non-schema evidence verdict {}",
            case.case_id,
            case.upstream_case_id,
            case.expected_verdict
        );
        assert_ne!(
            case.expected_verdict.to_ascii_lowercase(),
            "unknown",
            "{} ({}) must not inventory Unknown as evidence",
            case.case_id,
            case.upstream_case_id
        );

        if case.expected_verdict == "error" {
            assert!(
                !case.expected_error_patterns.is_empty(),
                "{} ({}) should carry precise fail-closed error fragments",
                case.case_id,
                case.upstream_case_id
            );
        } else {
            assert!(
                case.expected_error_patterns.is_empty(),
                "{} ({}) should not carry error fragments for {} evidence",
                case.case_id,
                case.upstream_case_id,
                case.expected_verdict
            );
        }
    }

    for required_status in ["verified", "counterexample", "error"] {
        assert!(
            actual
                .iter()
                .any(|case| case.expected_verdict == required_status),
            "metadata should include at least one {required_status} case"
        );
    }

    let mut function_names = Vec::new();
    collect_port_function_names(&ast.items, &mut function_names);
    let function_names = function_names.into_iter().collect::<BTreeSet<_>>();
    for case in &actual {
        assert!(
            function_names.contains(&case.case_id),
            "metadata case {} should name a function or default method in default_trait port",
            case.case_id
        );
    }
}

#[test]
fn default_trait_rs_expected_case_metadata_matches_manifest() {
    let (_source, ast) = port_source_and_ast();
    assert_eq!(metadata_entries(&ast), manifest_expected_metadata());
}

#[test]
fn default_trait_rs_verified_subset_verifies_from_metadata() {
    let (_source, ast) = port_source_and_ast();
    for case in metadata_entries(&ast)
        .into_iter()
        .filter(|case| case.expected_verdict == "verified")
    {
        let (result, obligation_count) = verify_port_case(&case.case_id, &case.upstream_case_id);
        reject_unknown(&result, &case);
        assert!(
            obligation_count >= case.min_obligations,
            "{} ({}) should collect at least {} obligation(s), got {obligation_count}",
            case.case_id,
            case.upstream_case_id,
            case.min_obligations
        );
        assert!(
            matches!(result, VerifyResult::Verified),
            "{} ({}) should verify, got: {result:?}",
            case.case_id,
            case.upstream_case_id
        );
    }
}

#[test]
fn default_trait_rs_counterexamples_are_stable_from_metadata() {
    let (_source, ast) = port_source_and_ast();
    for case in metadata_entries(&ast)
        .into_iter()
        .filter(|case| case.expected_verdict == "counterexample")
    {
        let (result, obligation_count) = verify_port_case(&case.case_id, &case.upstream_case_id);
        reject_unknown(&result, &case);
        assert!(
            obligation_count >= case.min_obligations,
            "{} ({}) should collect at least {} obligation(s), got {obligation_count}",
            case.case_id,
            case.upstream_case_id,
            case.min_obligations
        );
        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "{} ({}) should produce a counterexample, got: {result:?}",
            case.case_id,
            case.upstream_case_id
        );
    }
}

#[test]
fn default_trait_rs_default_constructor_boundaries_fail_closed_from_metadata() {
    let (_source, ast) = port_source_and_ast();
    for case in metadata_entries(&ast)
        .into_iter()
        .filter(|case| case.expected_verdict == "error")
    {
        expect_fail_closed(&case);
    }
}

#[test]
fn default_trait_rs_port_inventory_stays_intentional() {
    let (_source, ast) = port_source_and_ast();

    let mut observed = Vec::new();
    collect_port_function_names(&ast.items, &mut observed);
    let mut expected = metadata_entries(&ast)
        .into_iter()
        .map(|case| case.case_id)
        .collect::<Vec<_>>();
    observed.sort();
    expected.sort();

    assert_eq!(
        observed, expected,
        "default_trait.rs port should expose only intentional scout witnesses"
    );
}
