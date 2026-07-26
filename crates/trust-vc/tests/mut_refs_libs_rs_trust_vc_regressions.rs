// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Executable guards for the first upstream mut_refs_libs.rs TrustVc scout.
//!
//! These tests intentionally keep the upstream file as an unsupported gap. They
//! parse the port's expected-case metadata, reject solver `Unknown` as evidence,
//! check declared verified/counterexample/error outcomes and obligation floors,
//! pin Rust runtime witnesses, and require precise fail-closed fragments for
//! the mutable-reference library surfaces TrustVc does not yet model.

#![allow(clippy::useless_vec)]

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

fn mut_refs_libs_port_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/ported/mut_refs_libs.rs")
}

fn verus_manifest_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/verus-tests.json")
}

fn mut_refs_libs_upstream_path() -> PathBuf {
    common::pinned_verus_test_path("mut_refs_libs.rs")
}

fn parse_mut_refs_libs_port_file() -> (String, syn::File) {
    let path = mut_refs_libs_port_path();
    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|err| panic!("{} should be readable: {err}", path.display()));
    let file = syn::parse_file(&source)
        .unwrap_or_else(|err| panic!("{} should parse as Rust syntax: {err}", path.display()));
    (source, file)
}

fn parse_mut_refs_libs_expected_cases() -> Vec<ExpectedCase> {
    let (_, file) = parse_mut_refs_libs_port_file();
    parse_expected_case_metadata(&file, "MUT_REFS_LIBS_RS_EXPECTED_CASES")
}

fn with_error_patterns(cases: Vec<ExpectedCase>) -> Vec<ExpectedCaseWithPatterns> {
    cases
        .into_iter()
        .map(|case| ExpectedCaseWithPatterns {
            expected_error_patterns: mut_refs_libs_error_fragments(&case.case)
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
                == Some("source/rust_verify_test/tests/mut_refs_libs.rs")
        })
        .expect("Verus manifest should contain mut_refs_libs.rs row");

    row["expected_cases"]
        .as_array()
        .expect("mut_refs_libs manifest row should contain expected_cases")
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

fn parse_expected_case_metadata(file: &syn::File, const_name: &str) -> Vec<ExpectedCase> {
    let item_const = file
        .items
        .iter()
        .find_map(|item| match item {
            syn::Item::Const(item_const) if item_const.ident == const_name => Some(item_const),
            _ => None,
        })
        .unwrap_or_else(|| panic!("mut_refs_libs port should define {const_name}"));

    let array = match item_const.expr.as_ref() {
        syn::Expr::Reference(reference) => match reference.expr.as_ref() {
            syn::Expr::Array(array) => array,
            _ => panic!("{const_name} should reference an array literal"),
        },
        syn::Expr::Array(array) => array,
        _ => panic!("{const_name} should be an array literal"),
    };

    array.elems.iter().map(parse_expected_case_tuple).collect()
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

fn find_function<'a>(file: &'a syn::File, case: &str) -> Option<&'a syn::ItemFn> {
    file.items.iter().find_map(|item| match item {
        syn::Item::Fn(func) if func.sig.ident == case => Some(func),
        _ => None,
    })
}

fn verify_port_case(file: &syn::File, expected: &ExpectedCase) -> (VerifyResult, usize) {
    let path = mut_refs_libs_port_path();
    let path_str = path
        .to_str()
        .expect("mut_refs_libs port path should be UTF-8");

    let result = verify_function_from_file(path_str, &expected.case).unwrap_or_else(|err| {
        panic!(
            "{} ({}) should extract: {err}",
            expected.case, expected.upstream_case
        )
    });
    if let VerifyResult::Unknown { reason, .. } = &result {
        panic!(
            "{} ({}) returned solver Unknown, which is not stable evidence: {reason}",
            expected.case, expected.upstream_case
        );
    }

    let func = find_function(file, &expected.case).unwrap_or_else(|| {
        panic!(
            "{} ({}) should exist in {}",
            expected.case,
            expected.upstream_case,
            path.display()
        )
    });
    let vc = extract_verification_conditions_with_file_context(file, func).unwrap_or_else(|err| {
        panic!(
            "{} ({}) should extract: {err}",
            expected.case, expected.upstream_case
        )
    });

    (result, vc.obligations().len())
}

fn fail_closed_message(expected: &ExpectedCase) -> String {
    let path = mut_refs_libs_port_path();
    let path = path
        .to_str()
        .expect("mut_refs_libs port path should be UTF-8");

    match verify_function_from_file(path, &expected.case) {
        Err(err) => err.to_string(),
        Ok(VerifyResult::Error { message }) => message,
        Ok(VerifyResult::Unknown { reason, .. }) => {
            panic!(
                "{} ({}) returned solver Unknown, which is not stable evidence: {reason}",
                expected.case, expected.upstream_case
            )
        }
        Ok(other) => {
            panic!(
                "{} ({}) should fail closed with Error, got: {other:?}",
                expected.case, expected.upstream_case
            )
        }
    }
}

fn assert_expected_fragments(expected: &ExpectedCase, message: &str, fragments: &[&str]) {
    for fragment in fragments {
        assert!(
            message.contains(fragment),
            "{} ({}) error should contain {fragment:?}, got: {message}",
            expected.case,
            expected.upstream_case
        );
    }
}

fn assert_contains_in_order(source: &str, expected: &[&str]) {
    let mut offset = 0usize;
    for item in expected {
        let relative = source[offset..]
            .find(item)
            .unwrap_or_else(|| panic!("upstream mut_refs_libs.rs should contain {item} in order"));
        offset += relative + item.len();
    }
}

fn mut_refs_libs_error_fragments(case: &str) -> Option<&'static [&'static str]> {
    Some(match case {
        "mut_refs_libs_option_as_mut_write_currently_blocked"
        | "mut_refs_libs_option_as_mut_write_false_tail_currently_blocked" => &[
            "assignment through a dereferenced reference is unsupported in vc_extraction",
            "* ref_int",
        ],
        "mut_refs_libs_option_as_mut_some_observation_currently_blocked" => &[
            "Option::as_mut currently supports only known None observation",
            "returned mutable references are not modeled",
        ],
        "mut_refs_libs_option_as_mut_none_source_option_currently_blocked" => &[
            "Failed to lower obligation",
            "unresolved variable `opt`",
            "current scope",
        ],
        "mut_refs_libs_option_as_slice_none_observation_currently_blocked"
        | "mut_refs_libs_option_as_slice_some_observation_currently_blocked"
        | "mut_refs_libs_option_as_slice_none_false_tail_currently_blocked"
        | "mut_refs_libs_option_as_slice_some_false_tail_currently_blocked" => &[
            "as_slice() on type `Option<u64>`",
            "method is not available in specification context",
        ],
        "mut_refs_libs_option_as_mut_slice_none_observation_currently_blocked"
        | "mut_refs_libs_option_as_mut_slice_write_currently_blocked"
        | "mut_refs_libs_option_as_mut_slice_none_false_tail_currently_blocked"
        | "mut_refs_libs_option_as_mut_slice_write_false_tail_currently_blocked" => &[
            "as_mut_slice() on type `Option<u64>`",
            "method is not available in specification context",
        ],
        "mut_refs_libs_option_insert_mut_ref_currently_blocked"
        | "mut_refs_libs_option_insert_some_mut_ref_currently_blocked"
        | "mut_refs_libs_option_insert_none_false_tail_currently_blocked"
        | "mut_refs_libs_option_insert_some_false_tail_currently_blocked"
        | "mut_refs_libs_option_get_or_insert_none_mut_ref_currently_blocked"
        | "mut_refs_libs_option_get_or_insert_some_mut_ref_currently_blocked"
        | "mut_refs_libs_option_get_or_insert_none_false_tail_currently_blocked"
        | "mut_refs_libs_option_get_or_insert_some_false_tail_currently_blocked" => &[
            "assignment through a dereferenced reference is unsupported in vc_extraction",
            "* r",
        ],
        "mut_refs_libs_option_insert_none_result_observation_currently_blocked"
        | "mut_refs_libs_option_insert_some_result_observation_currently_blocked" => &[
            "collection operation 'insert'",
            "requires a collection receiver, got 'Option<u64>'",
        ],
        "mut_refs_libs_option_get_or_insert_none_result_observation_currently_blocked"
        | "mut_refs_libs_option_get_or_insert_some_result_observation_currently_blocked" => &[
            "get_or_insert() on type `Option<u64>`",
            "method is not available in specification context",
        ],
        "mut_refs_libs_vec_of_mut_refs_currently_blocked"
        | "mut_refs_libs_vec_of_mut_refs_false_tail_currently_blocked"
        | "mut_refs_libs_vec_of_mut_refs_reassign_currently_blocked"
        | "mut_refs_libs_vec_of_mut_refs_reassign_false_tail_currently_blocked" => &[
            "assignment through a dereferenced reference is unsupported in vc_extraction",
            "* v [0]",
        ],
        "mut_refs_libs_vec_push_nested_index_assign_currently_blocked" => &[
            "indexed assignment target is unsupported in vc_extraction",
            "v [1usize] [1usize]",
        ],
        "mut_refs_libs_vec_index_assign_nested_currently_blocked"
        | "mut_refs_libs_vec_index_assign_nested_false_tail_currently_blocked" => &[
            "indexed assignment target is unsupported in vc_extraction",
            "v [1] [1]",
        ],
        "mut_refs_libs_vec_index_out_of_bounds_nested_assign_currently_blocked" => &[
            "indexed assignment target is unsupported in vc_extraction",
            "v [2] [1]",
        ],
        "mut_refs_libs_vec_index_out_of_bounds_assign_currently_blocked" => &[
            "Vec literal indexed assignment is out of bounds",
            "length 3",
            "index is 3",
        ],
        "mut_refs_libs_vec_index_out_of_bounds_mut_ref_currently_blocked"
        | "mut_refs_libs_vec_index_out_of_bounds_read_currently_blocked"
        | "mut_refs_libs_vec_index_out_of_bounds_shared_ref_currently_blocked" => &[
            "Vec literal index is out of bounds",
            "length 3",
            "index is 3",
        ],
        "mut_refs_libs_vec_push_index_mut_ref_currently_blocked" => &[
            "assignment through a dereferenced reference is unsupported in vc_extraction",
            "* r",
            "tuple/index/nested",
        ],
        "mut_refs_libs_vec_index_mut_ref_currently_blocked"
        | "mut_refs_libs_vec_index_mut_ref_false_tail_currently_blocked"
        | "mut_refs_libs_vec_index_mut_ref_fields_currently_blocked"
        | "mut_refs_libs_vec_index_mut_ref_fields_false_tail_currently_blocked"
        | "mut_refs_libs_vec_index_mut_ref_nested_currently_blocked"
        | "mut_refs_libs_vec_index_mut_ref_nested_false_tail_currently_blocked"
        | "mut_refs_libs_vec_index_out_of_bounds_nested_mut_ref_currently_blocked" => &[
            "assignment through a dereferenced reference is unsupported in vc_extraction",
            "* r",
            "tuple/index/nested",
        ],
        "mut_refs_libs_vec_push_of_mut_refs_currently_blocked" => &[
            "assignment through a dereferenced reference is unsupported in vc_extraction",
            "* v [0usize]",
        ],
        "mut_refs_libs_vec_of_mut_refs_has_resolved_currently_blocked" => &[
            "has_resolved",
            "unknown return type for function 'has_resolved'",
        ],
        _ => return None,
    })
}

fn mut_refs_libs_runtime_witnesses() -> &'static [&'static str] {
    &[
        "mut_refs_libs_option_as_mut_runtime_some",
        "mut_refs_libs_option_as_mut_runtime_none",
        "mut_refs_libs_option_as_slice_runtime_none",
        "mut_refs_libs_option_as_slice_runtime_some",
        "mut_refs_libs_option_as_mut_slice_runtime_none",
        "mut_refs_libs_option_as_mut_slice_runtime_some",
        "mut_refs_libs_option_insert_runtime_none",
        "mut_refs_libs_option_insert_runtime_some",
        "mut_refs_libs_option_get_or_insert_runtime_none",
        "mut_refs_libs_option_get_or_insert_runtime_some",
        "mut_refs_libs_vec_index_assign_runtime_scalar",
        "mut_refs_libs_vec_index_assign_runtime_tuple_fields",
        "mut_refs_libs_vec_index_assign_runtime_fields",
        "mut_refs_libs_vec_index_assign_runtime_nested",
        "mut_refs_libs_vec_index_mut_ref_runtime_scalar",
        "mut_refs_libs_vec_index_mut_ref_runtime_tuple_fields",
        "mut_refs_libs_vec_index_mut_ref_runtime_fields",
        "mut_refs_libs_vec_index_mut_ref_runtime_nested",
        "mut_refs_libs_vec_of_mut_refs_runtime_reassign",
    ]
}

struct MutRefsLibsRuntimePair {
    left: u64,
    right: u64,
}

fn option_as_mut_runtime_some() {
    let mut opt = Some(5u64);
    let opt_ref_int = opt.as_mut();
    let ref_int = opt_ref_int.expect("Some value should yield a mutable reference");

    *ref_int = 20u64;

    assert_eq!(opt, Some(20u64));
}

fn option_as_mut_runtime_none() {
    let mut opt = None::<u64>;
    let opt_ref_int = opt.as_mut();

    assert!(opt_ref_int.is_none());
    assert_eq!(opt, None::<u64>);
}

fn option_as_slice_runtime_none() {
    let x = None::<u64>;
    let s = x.as_slice();

    assert!(s.is_empty());
    assert_eq!(x, None::<u64>);
}

fn option_as_slice_runtime_some() {
    let x = Some(20u64);
    let s = x.as_slice();

    assert_eq!(s, &[20u64]);
    assert_eq!(x, Some(20u64));
}

fn option_as_mut_slice_runtime_none() {
    let mut x = None::<u64>;
    let s = x.as_mut_slice();

    assert!(s.is_empty());
    assert!(x.is_none());
}

fn option_as_mut_slice_runtime_some() {
    let mut x = Some(20u64);
    let s = x.as_mut_slice();

    assert_eq!(s, &[20u64]);
    s[0] = 30u64;

    assert_eq!(x, Some(30u64));
}

fn option_insert_runtime_none() {
    let mut x = None::<u64>;
    let r = x.insert(20u64);

    assert_eq!(*r, 20u64);
    *r = 21u64;

    assert_eq!(x, Some(21u64));
}

fn option_insert_runtime_some() {
    let mut x = Some(5u64);
    let r = x.insert(20u64);

    assert_eq!(*r, 20u64);
    *r = 21u64;

    assert_eq!(x, Some(21u64));
}

fn option_get_or_insert_runtime_none() {
    let mut x = None::<u64>;
    let r = x.get_or_insert(20u64);

    assert_eq!(*r, 20u64);
    *r = 21u64;

    assert_eq!(x, Some(21u64));
}

fn option_get_or_insert_runtime_some() {
    let mut x = Some(5u64);
    let r = x.get_or_insert(20u64);

    assert_eq!(*r, 5u64);
    *r = 21u64;

    assert_eq!(x, Some(21u64));
}

fn vec_index_assign_runtime_scalar() {
    let mut v = vec![1u64, 2u64, 3u64];

    v[1usize] = 5u64;

    assert_eq!(v, vec![1u64, 5u64, 3u64]);
    assert_eq!(v[2usize], 3u64);
}

fn vec_index_assign_runtime_tuple_fields() {
    let mut v = vec![(1u64, 11u64), (2u64, 12u64), (3u64, 13u64)];

    v[1usize].0 = 5u64;

    assert_eq!(v[0usize].0, 1u64);
    assert_eq!(v[1usize].0, 5u64);
    assert_eq!(v[1usize].1, 12u64);
    assert_eq!(v[2usize].1, 13u64);
}

fn vec_index_assign_runtime_fields() {
    let mut v = vec![
        MutRefsLibsRuntimePair {
            left: 1u64,
            right: 11u64,
        },
        MutRefsLibsRuntimePair {
            left: 2u64,
            right: 12u64,
        },
        MutRefsLibsRuntimePair {
            left: 3u64,
            right: 13u64,
        },
    ];

    v[1usize].left = 5u64;

    assert_eq!(v[0usize].left, 1u64);
    assert_eq!(v[1usize].left, 5u64);
    assert_eq!(v[1usize].right, 12u64);
    assert_eq!(v[2usize].right, 13u64);
}

fn vec_index_assign_runtime_nested() {
    let mut v = vec![vec![1u64, 2u64, 3u64], vec![4u64, 5u64], vec![6u64]];

    v[1usize][1usize] = 15u64;

    assert_eq!(v[0usize], vec![1u64, 2u64, 3u64]);
    assert_eq!(v[1usize], vec![4u64, 15u64]);
    assert_eq!(v[2usize], vec![6u64]);
}

fn vec_index_mut_ref_runtime_scalar() {
    let mut v = vec![1u64, 2u64, 3u64];
    let r = &mut v[1usize];

    *r = 5u64;

    assert_eq!(v, vec![1u64, 5u64, 3u64]);
    assert_eq!(v[2usize], 3u64);
}

fn vec_index_mut_ref_runtime_tuple_fields() {
    let mut v = vec![(1u64, 11u64), (2u64, 12u64), (3u64, 13u64)];
    let r = &mut v[1usize].0;

    *r = 5u64;

    assert_eq!(v[0usize].0, 1u64);
    assert_eq!(v[1usize].0, 5u64);
    assert_eq!(v[1usize].1, 12u64);
    assert_eq!(v[2usize].1, 13u64);
}

fn vec_index_mut_ref_runtime_fields() {
    let mut v = vec![
        MutRefsLibsRuntimePair {
            left: 1u64,
            right: 11u64,
        },
        MutRefsLibsRuntimePair {
            left: 2u64,
            right: 12u64,
        },
        MutRefsLibsRuntimePair {
            left: 3u64,
            right: 13u64,
        },
    ];
    let r = &mut v[1usize].left;

    *r = 5u64;

    assert_eq!(v[1usize].left, 5u64);
    assert_eq!(v[2usize].right, 13u64);
}

fn vec_index_mut_ref_runtime_nested() {
    let mut v = vec![vec![1u64, 2u64, 3u64], vec![4u64, 5u64], vec![6u64]];
    let r = &mut v[1usize][1usize];

    *r = 15u64;

    assert_eq!(v[0usize], vec![1u64, 2u64, 3u64]);
    assert_eq!(v[1usize], vec![4u64, 15u64]);
    assert_eq!(v[2usize], vec![6u64]);
}

fn vec_of_mut_refs_runtime_reassign() {
    let mut a = 0u64;
    let mut b = 1u64;
    let mut c = 2u64;
    let mut d = 3u64;
    let mut v = vec![&mut a, &mut b, &mut c];

    *v[0usize] = 10u64;
    *v[1usize] = 11u64;
    *v[2usize] = 12u64;

    v[2usize] = &mut d;
    *v[2usize] = 13u64;

    drop(v);

    assert_eq!(a, 10u64);
    assert_eq!(b, 11u64);
    assert_eq!(c, 12u64);
    assert_eq!(d, 13u64);
}

#[test]
fn mut_refs_libs_rs_port_file_is_rust_syntax() {
    parse_mut_refs_libs_port_file();
}

#[test]
fn mut_refs_libs_rs_pinned_upstream_case_shapes_are_present() {
    let path = mut_refs_libs_upstream_path();
    if !path.exists() {
        eprintln!(
            "skipping pinned upstream mut_refs_libs.rs shape check; missing {}",
            path.display()
        );
        return;
    }

    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", path.display()));

    for expected in [
        "test_option_as_mut_spec",
        "test_vec_index_assign",
        "test_vec_index_mut_ref",
        "test_index_out_of_bounds",
        "test_vec_of_mut_refs",
        "test_options_as_mut_slice",
        "test_option_insert_and_get_or_insert",
        "fn test1_fails()",
        "fn test_as_slice_none()",
        "fn test_as_slice_some()",
        "fn test_as_mut_slice_none()",
        "fn test_as_mut_slice_some()",
        "fn fail_as_slice_none()",
        "fn fail_as_slice_some()",
        "fn fail_as_mut_slice_none()",
        "fn fail_as_mut_slice_some()",
        "fn test_insert_none()",
        "fn test_insert_some()",
        "fn test_get_or_insert_none()",
        "fn test_get_or_insert_some()",
        "fn fail_insert_none()",
        "fn fail_insert_some()",
        "fn fail_get_or_insert_none()",
        "fn fail_get_or_insert_some()",
        "fn test_fields()",
        "fn fails_fields()",
        "v[1].0 = 5",
        "fn test_nested()",
        "fn fails_nested()",
        "fn test_mut_ref_fields()",
        "fn fails_mut_ref_fields()",
        "fn test_mut_ref_nested()",
        "fn fails_mut_ref_nested()",
        "fn test_out_of_bounds1()",
        "fn test_out_of_bounds2()",
        "fn test_out_of_bounds3()",
        "fn test_out_of_bounds4()",
        "fn test_out_of_bounds_nested()",
        "fn test_out_of_bounds_nested2()",
        "fn test_vec2()",
        "fn fails_vec2()",
        "assert(has_resolved(v[0]))",
        "v[2] = &mut d",
        "v[3] = 5",
        "let r = &mut v[3]",
        "let r = &v[3]",
        "v[2][1] = 5",
    ] {
        assert!(
            source.contains(expected),
            "pinned upstream mut_refs_libs.rs should contain {expected}"
        );
    }

    assert_contains_in_order(
        &source,
        &[
            "#[test] test_option_as_mut_spec",
            "#[test] test_vec_index_assign",
            "#[test] test_vec_index_mut_ref",
            "#[test] test_index_out_of_bounds",
            "#[test] test_vec_of_mut_refs",
            "#[test] test_options_as_mut_slice",
            "#[test] test_option_insert_and_get_or_insert",
        ],
    );
}

#[test]
fn mut_refs_libs_rs_expected_case_metadata_is_schema_valid() {
    let (source, file) = parse_mut_refs_libs_port_file();
    assert!(
        source.contains("pub type MutRefsLibsExpectedCase")
            && source.contains("MUT_REFS_LIBS_RS_EXPECTED_CASES")
            && source.contains("mut_refs_libs_rs_expected_cases"),
        "mut_refs_libs port should expose typed expected-case metadata and an accessor"
    );

    let cases = parse_expected_case_metadata(&file, "MUT_REFS_LIBS_RS_EXPECTED_CASES");
    assert!(
        cases.len() >= 57,
        "mut_refs_libs port metadata should list the expanded scout cases"
    );

    let mut seen = BTreeSet::new();
    for expected in &cases {
        assert!(
            seen.insert(expected.case.clone()),
            "{} should appear only once in metadata",
            expected.case
        );
        assert!(
            !expected.upstream_case.is_empty(),
            "{} should declare its upstream case",
            expected.case
        );
        assert!(
            matches!(
                expected.status.as_str(),
                "verified" | "counterexample" | "error"
            ),
            "{} has unsupported expected status {}",
            expected.case,
            expected.status
        );
        assert_eq!(
            expected.status,
            expected.status.to_ascii_lowercase(),
            "{} status should be lowercase and must not encode Unknown",
            expected.case
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
                mut_refs_libs_error_fragments(&expected.case).is_some(),
                "{} should have pinned fail-closed diagnostic fragments",
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
            find_function(&file, &expected.case).is_some(),
            "{} should exist in the mut_refs_libs port",
            expected.case
        );
    }

    for required_case in [
        "mut_refs_libs_option_as_mut_write_false_tail_currently_blocked",
        "mut_refs_libs_option_as_mut_slice_write_false_tail_currently_blocked",
        "mut_refs_libs_option_get_or_insert_some_mut_ref_currently_blocked",
        "mut_refs_libs_vec_push_nested_index_assign_currently_blocked",
        "mut_refs_libs_vec_push_tuple_field_index_assign_false_tail_counterexample",
        "mut_refs_libs_vec_push_index_mut_ref_currently_blocked",
        "mut_refs_libs_vec_push_of_mut_refs_currently_blocked",
        "mut_refs_libs_vec_of_mut_refs_has_resolved_currently_blocked",
    ] {
        assert!(
            seen.contains(required_case),
            "metadata should cover {required_case}"
        );
    }

    for runtime_witness in mut_refs_libs_runtime_witnesses() {
        assert!(
            find_function(&file, runtime_witness).is_some(),
            "port should declare runtime witness {runtime_witness}"
        );
    }
}

#[test]
fn mut_refs_libs_rs_expected_case_metadata_matches_manifest() {
    assert_eq!(
        manifest_expected_cases(),
        with_error_patterns(parse_mut_refs_libs_expected_cases()),
        "mut_refs_libs manifest expected_cases should match port metadata and fail-closed patterns exactly"
    );
}

#[test]
fn mut_refs_libs_rs_runtime_witnesses_execute_std_behavior() {
    option_as_mut_runtime_some();
    option_as_mut_runtime_none();
    option_as_slice_runtime_none();
    option_as_slice_runtime_some();
    option_as_mut_slice_runtime_none();
    option_as_mut_slice_runtime_some();
    option_insert_runtime_none();
    option_insert_runtime_some();
    option_get_or_insert_runtime_none();
    option_get_or_insert_runtime_some();
    vec_index_assign_runtime_scalar();
    vec_index_assign_runtime_tuple_fields();
    vec_index_assign_runtime_fields();
    vec_index_assign_runtime_nested();
    vec_index_mut_ref_runtime_scalar();
    vec_index_mut_ref_runtime_tuple_fields();
    vec_index_mut_ref_runtime_fields();
    vec_index_mut_ref_runtime_nested();
    vec_of_mut_refs_runtime_reassign();
}

#[test]
fn mut_refs_libs_rs_expected_cases_match_declared_statuses_and_obligations() {
    let (_, file) = parse_mut_refs_libs_port_file();
    for expected in parse_mut_refs_libs_expected_cases() {
        match expected.status.as_str() {
            "verified" => {
                let (result, obligations) = verify_port_case(&file, &expected);
                assert!(
                    obligations >= expected.min_obligations,
                    "{} ({}) should collect at least {} obligation(s), got {obligations}",
                    expected.case,
                    expected.upstream_case,
                    expected.min_obligations
                );
                assert!(
                    matches!(result, VerifyResult::Verified),
                    "{} ({}) should verify, got: {result:?}",
                    expected.case,
                    expected.upstream_case
                );
            }
            "counterexample" => {
                let (result, obligations) = verify_port_case(&file, &expected);
                assert!(
                    obligations >= expected.min_obligations,
                    "{} ({}) should collect at least {} obligation(s), got {obligations}",
                    expected.case,
                    expected.upstream_case,
                    expected.min_obligations
                );
                assert!(
                    matches!(result, VerifyResult::Counterexample { .. }),
                    "{} ({}) should be rejected, got: {result:?}",
                    expected.case,
                    expected.upstream_case
                );
            }
            "error" => {
                let fragments =
                    mut_refs_libs_error_fragments(&expected.case).unwrap_or_else(|| {
                        panic!(
                            "{} ({}) should have expected diagnostic fragments",
                            expected.case, expected.upstream_case
                        )
                    });
                let message = fail_closed_message(&expected);
                assert_expected_fragments(&expected, &message, fragments);
            }
            other => {
                panic!(
                    "{} ({}) has unsupported expected status {other}",
                    expected.case, expected.upstream_case
                );
            }
        }
    }
}
