// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Executable guards for the first upstream impl.rs TrustVc scout slice.
//!
//! These tests intentionally do not claim full Verus impl.rs parity. They pin
//! the currently executable inherent associated-function and explicit
//! self-receiver evidence, plus generic impl-body witnesses, upstream shape
//! checks, stable counterexamples, and fail-closed unsupported boundaries while
//! the manifest keeps
//! `source/rust_verify_test/tests/impl.rs` as `unsupported-gap`.

mod common;

use std::{
    collections::{BTreeMap, BTreeSet},
    path::{Path, PathBuf},
};
use trust_vc_core::{
    extract_verification_conditions_with_file_context, verify_function_from_file, VerifyResult,
};

fn impl_port_path() -> PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/ported/impl.rs")
}

fn pinned_upstream_impl_path() -> PathBuf {
    common::pinned_verus_test_path("impl.rs")
}

fn verus_manifest_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/verus-tests.json")
}

#[derive(Debug, Eq, PartialEq)]
struct CaseMetadata {
    case_id: String,
    upstream_case_id: String,
    expected_verdict: String,
    min_obligations: usize,
    expected_error_patterns: Vec<String>,
}

fn impl_case_function(items: &[syn::Item], case: &str) -> Option<syn::ItemFn> {
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
                    if let Some(function) = impl_case_function(inner_items, case) {
                        return Some(function);
                    }
                }
            }
            _ => {}
        }
    }

    None
}

fn verify_port_case(case: &str, upstream_case: &str) -> (VerifyResult, usize) {
    let path = impl_port_path();
    let source =
        std::fs::read_to_string(&path).unwrap_or_else(|err| panic!("impl port should read: {err}"));
    let file =
        syn::parse_file(&source).unwrap_or_else(|err| panic!("impl port should parse: {err}"));
    let function = impl_case_function(&file.items, case)
        .unwrap_or_else(|| panic!("{case} ({upstream_case}) should exist in impl port"));

    let vc = extract_verification_conditions_with_file_context(&file, &function)
        .unwrap_or_else(|err| panic!("{case} ({upstream_case}) should extract: {err}"));
    let obligation_count = vc.obligations().len();
    (vc.verify(), obligation_count)
}

fn fail_closed_message_for_case(
    path: &str,
    case: &str,
    upstream_case: &str,
    expected_fragments: &[&str],
) {
    let message = match verify_function_from_file(path, case) {
        Err(err) => err.to_string(),
        Ok(VerifyResult::Error { message }) => message,
        Ok(VerifyResult::Unknown { reason, .. }) => {
            panic!("{case} ({upstream_case}) returned solver Unknown, which is not stable evidence: {reason}")
        }
        Ok(other) => {
            panic!("{case} ({upstream_case}) should fail closed with Error, got: {other:?}")
        }
    };

    assert!(
        expected_fragments
            .iter()
            .any(|expected_fragment| message.contains(expected_fragment)),
        "{case} ({upstream_case}) error should contain one of {expected_fragments:?}, got: {message}"
    );
}

fn referenced_array_const(file: &syn::File, const_name: &str) -> syn::ExprArray {
    let const_item = file
        .items
        .iter()
        .find_map(|item| match item {
            syn::Item::Const(item) if item.ident == const_name => Some(item),
            _ => None,
        })
        .unwrap_or_else(|| panic!("impl port should define {const_name}"));

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
    let array = referenced_array_const(file, "IMPL_RS_EXPECTED_ERROR_PATTERNS");
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
            "duplicate impl error-pattern metadata for {case_id}"
        );
    }

    entries
}

fn metadata_entries(file: &syn::File) -> Vec<CaseMetadata> {
    let array = referenced_array_const(file, "IMPL_RS_EXPECTED_CASES");
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
            "duplicate impl metadata for {case_id}"
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
            entry["upstream_path"].as_str() == Some("source/rust_verify_test/tests/impl.rs")
        })
        .expect("Verus manifest should contain impl.rs row");

    row["expected_cases"]
        .as_array()
        .expect("impl.rs row should contain expected_cases")
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

fn assert_verified(case: &str, upstream_case: &str, min_obligations: usize) {
    let (result, obligation_count) = verify_port_case(case, upstream_case);
    assert!(
        obligation_count >= min_obligations,
        "{case} ({upstream_case}) should collect at least {min_obligations} obligation(s), got {obligation_count}"
    );
    assert!(
        matches!(result, VerifyResult::Verified),
        "{case} ({upstream_case}) should verify, got: {result:?}"
    );
}

fn assert_counterexample(case: &str, upstream_case: &str, min_obligations: usize) {
    let (result, obligation_count) = verify_port_case(case, upstream_case);
    assert!(
        obligation_count >= min_obligations,
        "{case} ({upstream_case}) should collect at least {min_obligations} obligation(s), got {obligation_count}"
    );
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "{case} ({upstream_case}) should be rejected, got: {result:?}"
    );
}

const VERIFIED_CASES: &[(&str, &str, usize)] = &[
    ("new_bike_verified", "test_impl_no_self", 1),
    ("explicit_self_hard_tail_verified", "test_generic_struct", 1),
    ("explicit_borrow_self_hard_tail_verified", "test_impl_1", 1),
    ("associated_identity_verified", "test_impl_no_self", 1),
    ("generic_wrapper_take_verified", "test_impl_generic_pass", 1),
    (
        "concrete_wrapper_take_with_param_verified",
        "test_impl_generic_param",
        1,
    ),
    ("template_new_u64_verified", "test_generic_struct", 1),
    (
        "template_get_passengers_explicit_self_verified",
        "test_generic_struct",
        1,
    ),
    (
        "template_get_v_explicit_self_verified",
        "test_generic_struct",
        1,
    ),
    (
        "associated_function_call_currently_blocked",
        "test_impl_mod_1",
        1,
    ),
    ("method_call_verified", "test_impl_1", 1),
    ("implicit_self_hard_tail_verified", "test_generic_struct", 1),
    ("self_return_type_verified", "test_impl_with_self", 1),
    ("self_associated_call_verified", "test_resolve_self_ty", 1),
    ("generic_method_call_verified", "test_impl_generic_pass", 1),
];

const COUNTEREXAMPLE_CASES: &[(&str, &str, usize)] = &[
    (
        "associated_assert_false_counterexample",
        "test_impl_generic_fail",
        1,
    ),
    (
        "concrete_wrapper_field_wrong_counterexample",
        "test_impl_generic_fail",
        1,
    ),
    (
        "template_field_projection_wrong_counterexample",
        "test_generic_struct",
        1,
    ),
];

// After Phase A2-generic every impl.rs scout case resolves (verified /
// counterexample); no fail-closed boundary remains in this slice.
const FAIL_CLOSED_CASES: &[(&str, &str, &[&str])] = &[];

#[test]
fn impl_rs_port_file_is_rust_syntax() {
    let source = std::fs::read_to_string(impl_port_path()).expect("impl port should be readable");
    syn::parse_file(&source).expect("impl port should parse as ordinary Rust syntax");
}

#[test]
fn impl_rs_pinned_upstream_case_shapes_are_present() {
    let path = pinned_upstream_impl_path();
    if !path.exists() {
        eprintln!(
            "skipping pinned upstream impl.rs shape check; missing {}",
            path.display()
        );
        return;
    }

    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", path.display()));
    for expected in [
        "#[test] test_impl_1",
        "#[test] test_impl_no_self",
        "#[test] test_impl_no_self_fail_pub_private",
        "#[test] test_impl_mod_1",
        "#[test] test_impl_mod_priv_field",
        "#[test] test_impl_generic_pass",
        "#[test] test_impl_generic_fail",
        "#[test] test_impl_generic_param",
        "#[test] test_impl_with_self",
        "#[test] test_illegal_trait_impl",
        "#[test] test_illegal_trait_impl_2",
        "#[test] test_generic_struct",
        "#[test] test_resolve_self_ty",
        "#[test] unsafe_impl_fail_send",
        "#[test] unsafe_impl_fail_sync",
        "impl Bike",
        "fn new() -> Bike",
        "pub closed spec fn take(self) -> A",
        "fn take<B>(self, b: B) -> Two<A, B>",
        "fn template_new(v: V)",
        "fn template_get_passengers(&self)",
        "fn template_get_v(self)",
        "fn bar2(self) -> (s: Self)",
        "Self::bar(self)",
        "unsafe impl Send for Foo",
        "unsafe impl Sync for Foo",
    ] {
        assert!(
            source.contains(expected),
            "pinned upstream impl.rs should still contain {expected}"
        );
    }
}

#[test]
fn impl_rs_expected_case_metadata_is_exact() {
    let source = std::fs::read_to_string(impl_port_path()).expect("impl port should be readable");
    let file = syn::parse_file(&source).expect("impl port should parse as ordinary Rust syntax");
    assert!(
        source.contains("IMPL_RS_EXPECTED_CASES")
            && source.contains("impl_rs_expected_cases")
            && source.contains("IMPL_RS_EXPECTED_ERROR_PATTERNS")
            && source.contains("impl_rs_expected_error_patterns"),
        "impl port should expose expected-case and error-pattern metadata helpers"
    );
    assert_eq!(
        metadata_entries(&file),
        manifest_expected_metadata(),
        "impl.rs manifest expected_cases should match port metadata and error patterns exactly"
    );
}

#[test]
fn impl_rs_verified_subset_verifies_from_file() {
    for (case, upstream_case, min_obligations) in VERIFIED_CASES {
        assert_verified(case, upstream_case, *min_obligations);
    }
}

#[test]
fn impl_rs_counterexample_subset_is_rejected_from_file() {
    for (case, upstream_case, min_obligations) in COUNTEREXAMPLE_CASES {
        assert_counterexample(case, upstream_case, *min_obligations);
    }
}

#[test]
fn impl_rs_unsupported_boundaries_fail_closed_from_file() {
    let path = impl_port_path();
    let path = path.to_str().expect("impl port path should be UTF-8");

    for (case, upstream_case, expected_fragments) in FAIL_CLOSED_CASES {
        fail_closed_message_for_case(path, case, upstream_case, expected_fragments);
    }
}
