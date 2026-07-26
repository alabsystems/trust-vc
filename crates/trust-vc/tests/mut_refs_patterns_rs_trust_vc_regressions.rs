// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Executable guards for the upstream mut_refs_patterns.rs scout slice.
//!
//! These tests intentionally keep upstream mut_refs_patterns.rs as an
//! unsupported gap. They prove direct by-value tuple-struct/enum/literal
//! pattern reads including one irrefutable let-else plus adjacent direct
//! mutable-reference writes, reject reachable by-value and mutable-reference
//! assertions, and pin nested/plain-tuple/const-range/if-let/custom-enum-let-else,
//! guard/or-pattern, resolution-helper, and ghost/tracked/proof
//! mutable-reference pattern diagnostics as fail-closed.

mod common;

use std::path::{Path, PathBuf};
use trust_vc_core::{
    extract_verification_conditions_with_file_context, verify_function_from_file, VerifyResult,
};

fn mut_refs_patterns_port_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/ported/mut_refs_patterns.rs")
}

fn pinned_upstream_mut_refs_patterns_path() -> PathBuf {
    common::pinned_verus_test_path("mut_refs_patterns.rs")
}

fn verus_manifest_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/verus-tests.json")
}

fn active_upstream_cases(source: &str) -> Vec<String> {
    source
        .lines()
        .filter_map(|line| {
            let trimmed = line.trim();
            let rest = trimmed.strip_prefix("#[test] ")?;
            rest.split_whitespace().next().map(str::to_string)
        })
        .collect()
}

fn string_lit(expr: &syn::Expr) -> String {
    match expr {
        syn::Expr::Lit(syn::ExprLit {
            lit: syn::Lit::Str(value),
            ..
        }) => value.value(),
        _ => panic!("expected string literal in mut_refs_patterns metadata"),
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
        _ => panic!("expected usize literal in mut_refs_patterns metadata"),
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
        .unwrap_or_else(|| panic!("mut_refs_patterns port should define {const_name}"));
    referenced_array(expr, const_name)
}

fn parse_expected_case_metadata(source: &str) -> Vec<(String, String, String, usize)> {
    let file = syn::parse_file(source)
        .unwrap_or_else(|err| panic!("mut_refs_patterns port should parse: {err}"));
    port_const_array(&file, "MUT_REFS_PATTERNS_RS_EXPECTED_CASES")
        .elems
        .iter()
        .map(|entry| match entry {
            syn::Expr::Tuple(tuple) if tuple.elems.len() == 4 => {
                let mut elems = tuple.elems.iter();
                (
                    string_lit(elems.next().expect("case id exists")),
                    string_lit(elems.next().expect("upstream case exists")),
                    string_lit(elems.next().expect("status exists")),
                    usize_lit(elems.next().expect("obligation count exists")),
                )
            }
            _ => panic!("expected 4-tuple case metadata entry"),
        })
        .collect()
}

fn parse_string_array_const(source: &str, const_name: &str) -> Vec<String> {
    let file = syn::parse_file(source)
        .unwrap_or_else(|err| panic!("mut_refs_patterns port should parse: {err}"));
    port_const_array(&file, const_name)
        .elems
        .iter()
        .map(string_lit)
        .collect()
}

fn expected_fail_closed_error_pattern_metadata() -> Vec<(String, Vec<String>)> {
    FAIL_CLOSED_FRAGMENTS
        .iter()
        .map(|(case, patterns)| {
            (
                (*case).to_string(),
                patterns
                    .iter()
                    .map(|pattern| (*pattern).to_string())
                    .collect(),
            )
        })
        .collect()
}

fn manifest_row() -> serde_json::Value {
    let source =
        std::fs::read_to_string(verus_manifest_path()).expect("Verus manifest should be readable");
    let manifest: serde_json::Value =
        serde_json::from_str(&source).expect("Verus manifest should parse as JSON");
    manifest["entries"]
        .as_array()
        .expect("Verus manifest should contain entries")
        .iter()
        .find(|entry| {
            entry["upstream_path"].as_str()
                == Some("source/rust_verify_test/tests/mut_refs_patterns.rs")
        })
        .expect("Verus manifest should contain mut_refs_patterns.rs row")
        .clone()
}

fn manifest_expected_case_metadata() -> Vec<(String, String, String, usize)> {
    manifest_row()["expected_cases"]
        .as_array()
        .expect("mut_refs_patterns manifest row should contain expected_cases")
        .iter()
        .map(|case| {
            (
                case["case_id"]
                    .as_str()
                    .expect("manifest case should contain case_id")
                    .to_string(),
                case["upstream_case_id"]
                    .as_str()
                    .expect("manifest case should contain upstream_case_id")
                    .to_string(),
                case["expected_verdict"]
                    .as_str()
                    .expect("manifest case should contain expected_verdict")
                    .to_string(),
                case["min_obligations"]
                    .as_u64()
                    .expect("manifest case should contain min_obligations")
                    .try_into()
                    .expect("min_obligations should fit usize"),
            )
        })
        .collect()
}

fn manifest_fail_closed_error_pattern_metadata() -> Vec<(String, Vec<String>)> {
    manifest_row()["expected_cases"]
        .as_array()
        .expect("mut_refs_patterns manifest row should contain expected_cases")
        .iter()
        .filter_map(|case| {
            let patterns = case["expected_error_patterns"].as_array()?;
            Some((
                case["case_id"]
                    .as_str()
                    .expect("manifest case should contain case_id")
                    .to_string(),
                patterns
                    .iter()
                    .map(|pattern| {
                        pattern
                            .as_str()
                            .expect("expected_error_patterns entries should be strings")
                            .to_string()
                    })
                    .collect(),
            ))
        })
        .collect()
}

fn verify_case(path: &str, case: &str, upstream_case: &str) -> VerifyResult {
    verify_function_from_file(path, case)
        .unwrap_or_else(|err| panic!("{case} ({upstream_case}) should extract: {err}"))
}

fn expect_fail_closed_error_contains_any(
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
        Ok(result) => {
            panic!("{case} ({upstream_case}) should fail closed with Error, got: {result:?}")
        }
    };

    assert!(
        expected_fragments
            .iter()
            .any(|expected_fragment| message.contains(expected_fragment)),
        "{case} ({upstream_case}) error should contain one of {expected_fragments:?}, got: {message}"
    );
}

const EXPECTED_CASE_METADATA: &[(&str, &str, &str, usize)] = &[
    (
        "mut_refs_patterns_direct_mut_ref_write_verified",
        "basic_match_mut_ref direct mutable-reference write baseline",
        "verified",
        2,
    ),
    (
        "mut_refs_patterns_tuple_pattern_then_mut_ref_write_verified",
        "basic_let_stmt_mut_ref tuple pattern followed by direct mutable-reference write",
        "verified",
        2,
    ),
    (
        "mut_refs_patterns_let_tuple_struct_value_read_verified",
        "basic_let_stmt_mut_ref::test_foo irrefutable tuple pattern read",
        "verified",
        1,
    ),
    (
        "mut_refs_patterns_let_tuple_struct_pair_value_read_verified",
        "irrefutable multi-field tuple-struct pattern read",
        "verified",
        2,
    ),
    (
        "mut_refs_patterns_match_tuple_struct_value_read_verified",
        "basic_match_mut_ref::test_foo by-value tuple-struct match read",
        "verified",
        1,
    ),
    (
        "mut_refs_patterns_match_tuple_struct_pair_value_read_verified",
        "basic_match_mut_ref by-value multi-field tuple-struct match read",
        "verified",
        2,
    ),
    (
        "mut_refs_patterns_scalar_literal_match_arm_verified",
        "mut_ref_with_range_and_const_patterns scalar literal arm subset",
        "verified",
        1,
    ),
    (
        "mut_refs_patterns_match_option_some_value_read_verified",
        "basic_match_mut_ref::test_opt by-value enum match read",
        "verified",
        1,
    ),
    (
        "mut_refs_patterns_match_option_none_value_read_verified",
        "basic_match_mut_ref::test_opt by-value None arm read",
        "verified",
        1,
    ),
    (
        "mut_refs_patterns_let_one_variant_enum_value_read_verified",
        "let_explicit_ref_mut_binding by-value one-variant enum let read",
        "verified",
        1,
    ),
    (
        "mut_refs_patterns_let_else_tuple_struct_value_read_verified",
        "basic_let_else_mut_ref::test_foo by-value tuple-struct let-else read",
        "verified",
        1,
    ),
    (
        "mut_refs_patterns_match_option_some_arm_counterexample",
        "basic_match_mut_ref::test_opt_fails1 reachable by-value Some arm",
        "counterexample",
        1,
    ),
    (
        "mut_refs_patterns_match_option_none_arm_counterexample",
        "basic_match_mut_ref::test_opt_fails1 reachable by-value None arm",
        "counterexample",
        1,
    ),
    (
        "mut_refs_patterns_match_tuple_struct_pair_arm_counterexample",
        "basic_match_mut_ref multi-field tuple-struct false arm",
        "counterexample",
        1,
    ),
    (
        "mut_refs_patterns_let_else_option_some_arm_counterexample",
        "basic_let_else_mut_ref::test_opt_fails1 by-value enum let-else false arm",
        "counterexample",
        1,
    ),
    (
        "mut_refs_patterns_direct_mut_ref_wrong_post_counterexample",
        "basic_match_mut_ref direct mutable-reference stale-value assertion",
        "counterexample",
        1,
    ),
    (
        "mut_refs_patterns_tuple_pattern_then_mut_ref_false_tail_counterexample",
        "basic_let_stmt_mut_ref tuple pattern followed by mutable-reference false tail",
        "counterexample",
        1,
    ),
    (
        "mut_refs_patterns_scalar_literal_match_arm_counterexample",
        "mut_ref_with_range_and_const_patterns scalar literal false arm subset",
        "counterexample",
        1,
    ),
    (
        "mut_refs_patterns_mut_ref_const_range_match_currently_blocked",
        "mut_ref_with_range_and_const_patterns mutable-reference const/range pattern boundary",
        "error",
        0,
    ),
    (
        "mut_refs_patterns_plain_tuple_let_verified",
        "let_decl_on_a_field_place plain tuple let-pattern boundary",
        "verified",
        3,
    ),
    (
        "mut_refs_patterns_nested_tuple_subpattern_currently_blocked",
        "nested tuple subpattern inside tuple-struct pattern",
        "error",
        0,
    ),
    (
        "mut_refs_patterns_match_field_place_dot_currently_blocked",
        "match_on_a_field_place_via_dot mutable-reference field-place match",
        "error",
        0,
    ),
    (
        "mut_refs_patterns_match_field_place_tuple_currently_blocked",
        "match_on_a_field_via_underscore tuple field-place match",
        "error",
        0,
    ),
    (
        "mut_refs_patterns_match_mut_ref_read_currently_blocked",
        "basic_match_mut_ref::test_foo mutable-reference match pattern read",
        "error",
        0,
    ),
    (
        "mut_refs_patterns_match_enum_mut_ref_payload_read_currently_blocked",
        "basic_match_mut_ref by-value enum carrying mutable-reference payload",
        "error",
        0,
    ),
    (
        "mut_refs_patterns_match_mut_ref_update_currently_blocked",
        "basic_match_mut_ref::test_foo pattern-bound write",
        "error",
        0,
    ),
    (
        "mut_refs_patterns_let_mut_ref_read_currently_blocked",
        "basic_let_stmt_mut_ref::test_foo mutable-reference let pattern read",
        "error",
        0,
    ),
    (
        "mut_refs_patterns_let_mut_ref_update_currently_blocked",
        "basic_let_stmt_mut_ref::test_foo pattern-bound write",
        "error",
        0,
    ),
    (
        "mut_refs_patterns_explicit_ref_mut_binder_currently_blocked",
        "match_explicit_ref_mut_binding explicit ref mut binder",
        "error",
        0,
    ),
    (
        "mut_refs_patterns_ref_mut_scalar_match_read_currently_blocked",
        "ref_mut_binding_and_nothing_else read-only match ref mut binding",
        "error",
        0,
    ),
    (
        "mut_refs_patterns_ref_mut_scalar_let_read_currently_blocked",
        "ref_mut_binding_and_nothing_else read-only let ref mut binding",
        "error",
        0,
    ),
    (
        "mut_refs_patterns_ref_mut_scalar_match_false_currently_blocked",
        "ref_mut_binding_and_nothing_else read-only match false witness",
        "error",
        0,
    ),
    (
        "mut_refs_patterns_explicit_ref_mut_binder_read_currently_blocked",
        "match_explicit_ref_mut_binding read-only explicit ref mut binder",
        "error",
        0,
    ),
    (
        "mut_refs_patterns_scalar_ref_mut_update_currently_blocked",
        "ref_mut_binding_and_nothing_else pattern-bound scalar write",
        "error",
        0,
    ),
    (
        "mut_refs_patterns_at_binder_currently_blocked",
        "ref_mut_inside_at_binder at-binder pattern boundary",
        "error",
        0,
    ),
    (
        // Reclassified error->verified: the by-value if-let then-branch is
        // soundly handled (o==Some(20) so i==20, else unreachable); pinned by
        // trust-vc-core if_let_soundness_probe.rs. Name kept.
        "mut_refs_patterns_if_let_option_value_currently_blocked",
        "mut_refs_with_if_let by-value if-let pattern boundary",
        "verified",
        1,
    ),
    (
        "mut_refs_patterns_if_let_mut_ref_read_currently_blocked",
        "mut_refs_with_if_let mutable-reference if-let pattern read",
        "error",
        0,
    ),
    (
        "mut_refs_patterns_if_let_ref_mut_binding_currently_blocked",
        "mut_refs_with_if_let explicit ref mut if-let binding",
        "error",
        0,
    ),
    (
        "mut_refs_patterns_let_else_option_some_value_currently_blocked",
        "basic_let_else_mut_ref::test_opt by-value enum let-else read",
        "error",
        0,
    ),
    (
        "mut_refs_patterns_let_else_mut_ref_read_currently_blocked",
        "basic_let_else_mut_ref::test_opt mutable-reference let-else read",
        "error",
        0,
    ),
    (
        "mut_refs_patterns_let_else_field_place_currently_blocked",
        "let_else_on_a_field_place_via_dot mutable-reference field-place let-else",
        "error",
        0,
    ),
    (
        "mut_refs_patterns_ref_mut_inside_immut_ref_currently_blocked",
        "ref_mut_inside_immut_ref Rust shared-reference ref mut rejection",
        "error",
        0,
    ),
    (
        "mut_refs_patterns_ref_mut_guard_currently_blocked",
        "not_support_pattern_mut_ref_binding_with_guard",
        "error",
        0,
    ),
    (
        "mut_refs_patterns_ref_mut_or_pattern_currently_blocked",
        "not_support_pattern_mut_ref_binding_with_or_pat or-pattern boundary",
        "error",
        0,
    ),
    (
        "mut_refs_patterns_let_or_pattern_ref_mut_currently_blocked",
        "not_support_let_pattern_mut_ref_binding_with_or_pat or-pattern boundary",
        "error",
        0,
    ),
    (
        "mut_refs_patterns_has_resolved_currently_blocked",
        "has_resolved resolution predicate boundary",
        "error",
        0,
    ),
    (
        "mut_refs_patterns_mut_ref_current_currently_blocked",
        "mut_ref_current resolution helper boundary",
        "error",
        0,
    ),
    (
        "mut_refs_patterns_mut_ref_future_currently_blocked",
        "mut_ref_future helper boundary",
        "error",
        0,
    ),
    (
        "mut_refs_patterns_after_borrow_currently_blocked",
        "after_borrow resolution helper boundary",
        "error",
        0,
    ),
    (
        "mut_refs_patterns_proof_ref_mut_binding_currently_blocked",
        "mut_ref_ghost_binder_forbidden proof-mode ref mut binder diagnostic",
        "error",
        0,
    ),
    (
        "mut_refs_patterns_ghost_ref_mut_binding_currently_blocked",
        "mut_ref_ghost_binder_forbidden_ghost_type diagnostic",
        "error",
        0,
    ),
    (
        "mut_refs_patterns_tracked_ref_mut_binding_currently_blocked",
        "mut_ref_tracked_binder_forbidden tracked-mode diagnostic",
        "error",
        0,
    ),
];

const FAIL_CLOSED_FRAGMENTS: &[(&str, &[&str])] = &[
    (
        "mut_refs_patterns_mut_ref_const_range_match_currently_blocked",
        &[
            "unresolved variable `accepted`",
            "unresolved variable `pair_ref`",
            "unsupported pattern",
            "range",
            "tuple-struct patterns",
        ],
    ),
    (
        "mut_refs_patterns_nested_tuple_subpattern_currently_blocked",
        &["unresolved variable `i`"],
    ),
    (
        "mut_refs_patterns_match_field_place_dot_currently_blocked",
        &[
            "assignment through a dereferenced reference is unsupported",
            "unresolved variable `i`",
            "unsupported pattern",
        ],
    ),
    (
        "mut_refs_patterns_match_field_place_tuple_currently_blocked",
        &[
            "assignment through a dereferenced reference is unsupported",
            "tuple-struct patterns",
            "unsupported pattern",
            "unresolved variable `i`",
        ],
    ),
    (
        "mut_refs_patterns_match_mut_ref_read_currently_blocked",
        // A mut-ref READ is blocked either by the old "unresolved variable `i`"
        // (binding dropped) or, once `i` binds (ay 4df6ab25), by the true `*x`
        // dereference blocker (routed to trust-wp). Both are fail-closed.
        &[
            "unresolved variable `i`",
            "dereference expressions are not supported",
        ],
    ),
    (
        "mut_refs_patterns_match_enum_mut_ref_payload_read_currently_blocked",
        &[
            "unresolved variable `i`",
            "dereference expressions are not supported",
        ],
    ),
    (
        "mut_refs_patterns_match_mut_ref_update_currently_blocked",
        &["assignment through a dereferenced reference is unsupported"],
    ),
    (
        "mut_refs_patterns_let_mut_ref_read_currently_blocked",
        &[
            "unresolved variable `i`",
            "dereference expressions are not supported",
        ],
    ),
    (
        "mut_refs_patterns_let_mut_ref_update_currently_blocked",
        &["assignment through a dereferenced reference is unsupported"],
    ),
    (
        "mut_refs_patterns_explicit_ref_mut_binder_currently_blocked",
        &["assignment through a dereferenced reference is unsupported"],
    ),
    (
        "mut_refs_patterns_ref_mut_scalar_match_read_currently_blocked",
        &[
            "unresolved variable `i`",
            "dereference expressions are not supported",
        ],
    ),
    (
        "mut_refs_patterns_ref_mut_scalar_let_read_currently_blocked",
        &[
            "dereference expressions are not supported",
            "unsupported unary operator",
        ],
    ),
    (
        "mut_refs_patterns_ref_mut_scalar_match_false_currently_blocked",
        &["unresolved variable `i`"],
    ),
    (
        "mut_refs_patterns_explicit_ref_mut_binder_read_currently_blocked",
        &["unresolved variable `i`"],
    ),
    (
        "mut_refs_patterns_scalar_ref_mut_update_currently_blocked",
        &["assignment through a dereferenced reference is unsupported"],
    ),
    (
        "mut_refs_patterns_at_binder_currently_blocked",
        &["unresolved variable `i`", "unresolved variable `whole`"],
    ),
    (
        "mut_refs_patterns_if_let_mut_ref_read_currently_blocked",
        &[
            "unresolved variable `i`",
            "if-let pattern",
            "dereference expressions are not supported",
        ],
    ),
    (
        "mut_refs_patterns_if_let_ref_mut_binding_currently_blocked",
        &[
            "assignment through a dereferenced reference is unsupported",
            "unresolved variable `i`",
            "if-let pattern",
        ],
    ),
    (
        "mut_refs_patterns_let_else_option_some_value_currently_blocked",
        &["unresolved variable `i`", "let-else pattern"],
    ),
    (
        "mut_refs_patterns_let_else_mut_ref_read_currently_blocked",
        &[
            "unresolved variable `i`",
            "let-else pattern",
            "dereference expressions are not supported",
        ],
    ),
    (
        "mut_refs_patterns_let_else_field_place_currently_blocked",
        &[
            "assignment through a dereferenced reference is unsupported",
            "unresolved variable `i`",
            "let-else pattern",
        ],
    ),
    (
        "mut_refs_patterns_ref_mut_inside_immut_ref_currently_blocked",
        &[
            "cannot borrow",
            "behind a `&` reference",
            "unresolved variable `i`",
        ],
    ),
    (
        "mut_refs_patterns_ref_mut_guard_currently_blocked",
        &[
            "match guards are not yet supported",
            "guard",
            "unresolved variable `i`",
        ],
    ),
    (
        "mut_refs_patterns_ref_mut_or_pattern_currently_blocked",
        &["or-pattern", "unresolved variable `i`"],
    ),
    (
        "mut_refs_patterns_let_or_pattern_ref_mut_currently_blocked",
        &["or-pattern", "unresolved variable `i`"],
    ),
    (
        "mut_refs_patterns_has_resolved_currently_blocked",
        &["has_resolved", "unknown return type"],
    ),
    (
        "mut_refs_patterns_mut_ref_current_currently_blocked",
        &["mut_ref_current", "unknown return type"],
    ),
    (
        "mut_refs_patterns_mut_ref_future_currently_blocked",
        &["mut_ref_future", "unknown return type"],
    ),
    (
        "mut_refs_patterns_after_borrow_currently_blocked",
        &["after_borrow", "unknown return type"],
    ),
    (
        "mut_refs_patterns_proof_ref_mut_binding_currently_blocked",
        &["unresolved variable `i`", "proof", "ref mut"],
    ),
    (
        "mut_refs_patterns_ghost_ref_mut_binding_currently_blocked",
        &["unresolved variable `i`", "Ghost", "unsupported pattern"],
    ),
    (
        "mut_refs_patterns_tracked_ref_mut_binding_currently_blocked",
        &[
            "Tracked",
            "unresolved variable `i`",
            "unsupported method",
            "get",
        ],
    ),
];

fn expected_case(case: &str) -> (&'static str, &'static str, usize) {
    EXPECTED_CASE_METADATA
        .iter()
        .find_map(|(candidate, upstream_case, status, min_obligations)| {
            (*candidate == case).then_some((*upstream_case, *status, *min_obligations))
        })
        .unwrap_or_else(|| panic!("missing expected-case metadata for {case}"))
}

#[test]
fn mut_refs_patterns_rs_port_file_is_rust_syntax() {
    let source = std::fs::read_to_string(mut_refs_patterns_port_path())
        .expect("mut_refs_patterns port should be readable");
    syn::parse_file(&source).expect("mut_refs_patterns port should parse as ordinary Rust syntax");
}

#[test]
fn mut_refs_patterns_rs_pinned_upstream_case_shapes_are_present() {
    let path = pinned_upstream_mut_refs_patterns_path();
    if !path.exists() {
        eprintln!(
            "skipping pinned upstream mut_refs_patterns.rs shape check; missing {}",
            path.display()
        );
        return;
    }

    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", path.display()));
    for expected in [
        "#[test] basic_match_mut_ref",
        "#[test] basic_let_stmt_mut_ref",
        "#[test] match_on_a_field_place_via_dot",
        "#[test] match_on_a_field_via_underscore",
        "#[test] let_decl_on_a_field_place",
        "#[test] match_explicit_ref_mut_binding",
        "#[test] let_explicit_ref_mut_binding",
        "#[test] ref_mut_inside_immut_ref",
        "#[test] ref_mut_inside_at_binder",
        "#[test] ref_mut_binding_and_nothing_else",
        "#[test] mut_ref_with_range_and_const_patterns",
        "#[test] binders_in_pattern_copy_vs_no_copy",
        "#[test] mut_refs_with_if_let",
        "#[test] not_support_pattern_mut_ref_binding_with_guard",
        "#[test] not_support_pattern_mut_ref_binding_with_or_pat",
        "#[test] let_else_on_a_field_place_via_dot",
        "#[test] basic_let_else_mut_ref",
        "#[test] two_mut_ref_borrows_from_enum_no_lifetime",
        "let Foo(i) = o_ref;",
        "match pair.0",
        "let Some(i) = pair.0 else",
        "ref mut y =>",
        "has_resolved",
        "mut_ref_current",
        "mut_ref_future",
    ] {
        assert!(
            source.contains(expected),
            "pinned upstream mut_refs_patterns.rs should still contain {expected}"
        );
    }

    let port_source = std::fs::read_to_string(mut_refs_patterns_port_path())
        .expect("mut_refs_patterns port should be readable");
    assert_eq!(
        active_upstream_cases(&source),
        parse_string_array_const(&port_source, "MUT_REFS_PATTERNS_RS_UPSTREAM_ACTIVE_CASES"),
        "pinned upstream mut_refs_patterns.rs active harness inventory should match the port metadata"
    );
}

#[test]
fn mut_refs_patterns_rs_expected_case_metadata_is_exact() {
    let source = std::fs::read_to_string(mut_refs_patterns_port_path())
        .expect("mut_refs_patterns port should be readable");
    let file = syn::parse_file(&source)
        .unwrap_or_else(|err| panic!("mut_refs_patterns port should parse: {err}"));
    assert!(
        source.contains("mut_refs_patterns_rs_expected_cases")
            && source.contains("upstream_mut_refs_patterns_rs_active_cases"),
        "mut_refs_patterns port should expose expected-case and upstream-inventory helpers"
    );

    let actual = parse_expected_case_metadata(&source);
    let expected = EXPECTED_CASE_METADATA
        .iter()
        .map(|(case, upstream_case, status, min_obligations)| {
            (
                (*case).to_string(),
                (*upstream_case).to_string(),
                (*status).to_string(),
                *min_obligations,
            )
        })
        .collect::<Vec<_>>();
    assert_eq!(
        actual, expected,
        "mut_refs_patterns port expected-case metadata should be exact"
    );

    let mut seen_cases = std::collections::BTreeSet::new();
    for (case, upstream_case, status, min_obligations) in &actual {
        assert!(
            seen_cases.insert(case.clone()),
            "metadata case ids should be unique; duplicate: {case}"
        );
        assert!(
            ["verified", "counterexample", "error"].contains(&status.as_str()),
            "{case} ({upstream_case}) should use a closed expected status, got {status}"
        );
        assert!(
            !status.eq_ignore_ascii_case("unknown"),
            "{case} ({upstream_case}) must not inventory solver Unknown as evidence"
        );
        match status.as_str() {
            "verified" | "counterexample" => assert!(
                *min_obligations > 0,
                "{case} ({upstream_case}) should require at least one collected obligation"
            ),
            "error" => assert_eq!(
                *min_obligations, 0,
                "{case} ({upstream_case}) fail-closed cases should declare zero obligations"
            ),
            _ => unreachable!("status allow-list checked above"),
        }

        assert!(
            file.items.iter().any(|item| matches!(
                item,
                syn::Item::Fn(function) if function.sig.ident == case.as_str()
            )),
            "{case} ({upstream_case}) should name a function in the port"
        );
    }

    for allowed_status in ["verified", "counterexample", "error"] {
        assert!(
            EXPECTED_CASE_METADATA
                .iter()
                .any(|(_, _, status, _)| *status == allowed_status),
            "metadata should include at least one {allowed_status} case"
        );
    }

    assert!(
        !EXPECTED_CASE_METADATA
            .iter()
            .any(|(_, _, status, _)| status.eq_ignore_ascii_case("unknown")),
        "solver Unknown must not be accepted as mut_refs_patterns evidence"
    );
}

#[test]
fn mut_refs_patterns_rs_expected_case_metadata_matches_manifest() {
    let source = std::fs::read_to_string(mut_refs_patterns_port_path())
        .expect("mut_refs_patterns port should be readable");
    assert_eq!(
        parse_expected_case_metadata(&source),
        manifest_expected_case_metadata(),
        "mut_refs_patterns port metadata should match the manifest inventory exactly"
    );
    assert_eq!(
        expected_fail_closed_error_pattern_metadata(),
        manifest_fail_closed_error_pattern_metadata(),
        "mut_refs_patterns fail-closed metadata should match manifest expected_error_patterns exactly"
    );
}

#[test]
fn mut_refs_patterns_rs_metadata_covers_required_gap_families() {
    let source = std::fs::read_to_string(mut_refs_patterns_port_path())
        .expect("mut_refs_patterns port should be readable");
    let actual = parse_expected_case_metadata(&source);
    let haystack = actual
        .iter()
        .map(|(case, upstream_case, status, _)| format!("{case} {upstream_case} {status}"))
        .collect::<Vec<_>>()
        .join("\n");

    for required_fragment in [
        "direct mutable-reference write",
        "tuple-struct pattern read",
        "const/range pattern",
        "plain tuple let-pattern",
        "nested tuple subpattern",
        "mutable-reference match pattern read",
        "pattern-bound write",
        "explicit ref mut",
        "by-value enum let-else",
        "mutable-reference let-else",
        "if-let",
        "guard",
        "or-pattern",
        "has_resolved",
        "mut_ref_current",
        "mut_ref_future",
        "after_borrow",
        "ghost",
        "tracked",
        "proof",
    ] {
        assert!(
            haystack.contains(required_fragment),
            "mut_refs_patterns metadata should cover required gap family fragment {required_fragment:?}"
        );
    }
}

#[test]
fn mut_refs_patterns_rs_verified_subset_verifies_from_file() {
    let path = mut_refs_patterns_port_path();
    let path = path
        .to_str()
        .expect("mut_refs_patterns port path should be UTF-8");

    for (case, upstream_case, status, _) in EXPECTED_CASE_METADATA
        .iter()
        .filter(|(_, _, status, _)| *status == "verified")
    {
        let result = verify_case(path, case, upstream_case);
        assert!(
            matches!(result, VerifyResult::Verified),
            "{case} ({upstream_case}) should verify, got: {result:?}"
        );
        assert_eq!(*status, "verified");
    }
}

#[test]
fn mut_refs_patterns_rs_counterexample_subset_is_rejected_from_file() {
    let path = mut_refs_patterns_port_path();
    let path = path
        .to_str()
        .expect("mut_refs_patterns port path should be UTF-8");

    for (case, upstream_case, status, _) in EXPECTED_CASE_METADATA
        .iter()
        .filter(|(_, _, status, _)| *status == "counterexample")
    {
        let result = verify_case(path, case, upstream_case);
        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "{case} ({upstream_case}) should produce a counterexample, got: {result:?}"
        );
        assert_eq!(*status, "counterexample");
    }
}

#[test]
fn mut_refs_patterns_rs_non_error_subset_collects_min_obligations() {
    let path = mut_refs_patterns_port_path();
    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|err| panic!("mut_refs_patterns port should read: {err}"));
    let file = syn::parse_file(&source)
        .unwrap_or_else(|err| panic!("mut_refs_patterns port should parse: {err}"));

    for (case, upstream_case, status, min_obligations) in EXPECTED_CASE_METADATA
        .iter()
        .filter(|(_, _, status, _)| *status != "error")
    {
        let function = file
            .items
            .iter()
            .find_map(|item| match item {
                syn::Item::Fn(function) if function.sig.ident == *case => Some(function),
                _ => None,
            })
            .unwrap_or_else(|| {
                panic!("{case} ({upstream_case}) should exist in mut_refs_patterns port")
            });
        let vc = extract_verification_conditions_with_file_context(&file, function)
            .unwrap_or_else(|err| panic!("{case} ({upstream_case}) should extract: {err}"));

        assert!(
            vc.obligations().len() >= *min_obligations,
            "{case} ({upstream_case}) should collect at least {min_obligations} obligation(s), got {}",
            vc.obligations().len()
        );
        assert!(*status == "verified" || *status == "counterexample");
    }
}

#[test]
fn mut_refs_patterns_rs_mut_ref_pattern_boundaries_fail_closed_from_file() {
    let path = mut_refs_patterns_port_path();
    let path = path
        .to_str()
        .expect("mut_refs_patterns port path should be UTF-8");

    let metadata_error_cases = EXPECTED_CASE_METADATA
        .iter()
        .filter_map(|(case, _, status, _)| (*status == "error").then_some(*case))
        .collect::<Vec<_>>();
    let fragment_error_cases = FAIL_CLOSED_FRAGMENTS
        .iter()
        .map(|(case, _)| *case)
        .collect::<Vec<_>>();
    assert_eq!(
        fragment_error_cases, metadata_error_cases,
        "every metadata error case should have exact fail-closed fragments"
    );

    for (case, expected_fragments) in FAIL_CLOSED_FRAGMENTS {
        let (upstream_case, status, _) = expected_case(case);
        assert_eq!(status, "error");
        expect_fail_closed_error_contains_any(path, case, upstream_case, expected_fragments);
    }
}
