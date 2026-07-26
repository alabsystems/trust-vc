// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Executable guards for the current upstream refs.rs scout slice.
//!
//! These tests intentionally do not claim full Verus refs parity. They prove
//! the listed upstream-derived reference slices execute through TrustVc while
//! the manifest keeps `source/rust_verify_test/tests/refs.rs` fail-closed.

mod common;

use std::{
    collections::BTreeMap,
    path::{Path, PathBuf},
};
use trust_vc_core::{
    extract_verification_conditions_with_file_context, verify_function_from_file, VerifyResult,
};

type ExpectedCase = (&'static str, &'static str, &'static str, usize);

fn refs_port_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/ported/refs.rs")
}

fn verus_manifest_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/verus-tests.json")
}

fn pinned_upstream_refs_path() -> PathBuf {
    common::pinned_verus_test_path("refs.rs")
}

fn verify_case(path: &str, case: &str, upstream_case: &str) -> VerifyResult {
    let result = verify_function_from_file(path, case)
        .unwrap_or_else(|err| panic!("{case} ({upstream_case}) should extract: {err}"));
    if let VerifyResult::Unknown { reason, .. } = &result {
        panic!(
            "{case} ({upstream_case}) returned solver Unknown, which is not stable evidence: {reason}"
        );
    }
    result
}

fn obligation_count(case: &str, upstream_case: &str) -> usize {
    let path = refs_port_path();
    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|err| panic!("{} should be readable: {err}", path.display()));
    let file = syn::parse_file(&source)
        .unwrap_or_else(|err| panic!("{} should parse as Rust syntax: {err}", path.display()));
    let func = file
        .items
        .iter()
        .find_map(|item| match item {
            syn::Item::Fn(func) if func.sig.ident == case => Some(func),
            _ => None,
        })
        .unwrap_or_else(|| {
            panic!(
                "{case} ({upstream_case}) should exist in {}",
                path.display()
            )
        });
    let vc = extract_verification_conditions_with_file_context(&file, func)
        .unwrap_or_else(|err| panic!("{case} ({upstream_case}) should extract VCs: {err}"));

    vc.obligations().len()
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
            panic!(
                "{case} ({upstream_case}) returned solver Unknown, which is not stable evidence: {reason}"
            )
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

fn literal_string(expr: &syn::Expr) -> String {
    match expr {
        syn::Expr::Lit(syn::ExprLit {
            lit: syn::Lit::Str(lit),
            ..
        }) => lit.value(),
        _ => panic!("expected string literal in refs.rs expected-case metadata"),
    }
}

fn literal_usize(expr: &syn::Expr) -> usize {
    match expr {
        syn::Expr::Lit(syn::ExprLit {
            lit: syn::Lit::Int(lit),
            ..
        }) => lit
            .base10_parse::<usize>()
            .unwrap_or_else(|err| panic!("expected usize literal in refs.rs metadata: {err}")),
        _ => panic!("expected usize literal in refs.rs expected-case metadata"),
    }
}

fn parse_expected_case_metadata(source: &str) -> Vec<(String, String, String, usize)> {
    let file = syn::parse_file(source).expect("refs port should parse as Rust syntax");
    let const_item = file
        .items
        .iter()
        .find_map(|item| match item {
            syn::Item::Const(item) if item.ident == "REFS_RS_EXPECTED_CASES" => Some(item),
            _ => None,
        })
        .expect("refs port should define REFS_RS_EXPECTED_CASES");

    let syn::Expr::Reference(reference) = const_item.expr.as_ref() else {
        panic!("REFS_RS_EXPECTED_CASES should be a referenced array");
    };
    let syn::Expr::Array(array) = reference.expr.as_ref() else {
        panic!("REFS_RS_EXPECTED_CASES should reference an array");
    };

    array
        .elems
        .iter()
        .map(|entry| {
            let syn::Expr::Tuple(tuple) = entry else {
                panic!("expected tuple metadata entry");
            };
            assert_eq!(
                tuple.elems.len(),
                4,
                "metadata entries should have case, upstream case, status, and min obligations"
            );
            (
                literal_string(&tuple.elems[0]),
                literal_string(&tuple.elems[1]),
                literal_string(&tuple.elems[2]),
                literal_usize(&tuple.elems[3]),
            )
        })
        .collect()
}

fn expected_metadata() -> Vec<(String, String, String, usize)> {
    EXPECTED_CASE_METADATA
        .iter()
        .map(|(case, upstream_case, status, min_obligations)| {
            (
                (*case).to_string(),
                (*upstream_case).to_string(),
                (*status).to_string(),
                *min_obligations,
            )
        })
        .collect()
}

fn fail_closed_pattern_metadata() -> BTreeMap<String, Vec<String>> {
    UNSUPPORTED_CASES
        .iter()
        .map(|(case, _, expected_fragments)| {
            (
                (*case).to_string(),
                expected_fragments
                    .iter()
                    .map(|fragment| (*fragment).to_string())
                    .collect(),
            )
        })
        .collect()
}

fn attach_error_patterns(
    cases: Vec<(String, String, String, usize)>,
) -> Vec<(String, String, String, usize, Vec<String>)> {
    let patterns = fail_closed_pattern_metadata();
    cases
        .into_iter()
        .map(|(case, upstream_case, status, min_obligations)| {
            let expected_patterns = patterns.get(&case).cloned().unwrap_or_default();
            (
                case,
                upstream_case,
                status,
                min_obligations,
                expected_patterns,
            )
        })
        .collect()
}

fn manifest_expected_case_metadata() -> Vec<(String, String, String, usize, Vec<String>)> {
    let source =
        std::fs::read_to_string(verus_manifest_path()).expect("Verus manifest should be readable");
    let manifest: serde_json::Value =
        serde_json::from_str(&source).expect("Verus manifest should parse as JSON");
    let row = manifest["entries"]
        .as_array()
        .expect("Verus manifest should contain entries")
        .iter()
        .find(|entry| {
            entry["upstream_path"].as_str() == Some("source/rust_verify_test/tests/refs.rs")
        })
        .expect("Verus manifest should contain refs.rs row");

    row["expected_cases"]
        .as_array()
        .expect("refs manifest row should contain expected_cases")
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
                case["expected_error_patterns"]
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
            )
        })
        .collect()
}

const EXPECTED_CASE_METADATA: &[ExpectedCase] = &[
    ("refs_local_borrow_deref", "test_ref_0", "verified", 2),
    ("refs_shared_param_alias_deref", "test_ref_1", "verified", 2),
    ("refs_shared_param_read", "test_ref_1", "verified", 2),
    (
        "refs_return_ref_identity",
        "test_return_ref_0",
        "verified",
        2,
    ),
    (
        "refs_return_ref_caller_alias",
        "test_return_ref_0",
        "verified",
        2,
    ),
    (
        "refs_return_ref_caller_alias_inferred",
        "test_return_ref_0",
        "verified",
        2,
    ),
    (
        "refs_return_ref_named_lifetime",
        "test_return_ref_named_lifetime",
        "verified",
        2,
    ),
    (
        "refs_return_ref_named_lifetime_caller",
        "test_return_ref_named_lifetime",
        "verified",
        2,
    ),
    (
        "refs_slice_view_from_shared_reference",
        "deref_vec_ok fixed slice view surrogate",
        "verified",
        2,
    ),
    (
        "refs_slice_view_wrong_index_counterexample",
        "deref_vec_fails fixed slice view false-tail surrogate",
        "counterexample",
        1,
    ),
    (
        "refs_vec_view_through_shared_reference",
        "deref_vec_ok shared Vec reference view surrogate",
        "verified",
        2,
    ),
    (
        "refs_vec_view_through_shared_reference_wrong_len_counterexample",
        "deref_vec_fails shared Vec reference view false-tail surrogate",
        "counterexample",
        1,
    ),
    ("refs_local_mut_borrow_deref", "test_ref_0", "verified", 2),
    ("refs_mut_param_alias_deref", "test_ref_1", "verified", 2),
    (
        "refs_mut_param_forward_read_callee",
        "test_mut_ref_forward",
        "verified",
        2,
    ),
    (
        "refs_mut_param_forward_read",
        "test_mut_ref_forward",
        "verified",
        2,
    ),
    (
        "refs_mut_ref_to_shared_ref_argument_preserves_local",
        "mutref_arg_ref_unsupported",
        "verified",
        2,
    ),
    (
        "refs_mut_ref_typing_invariant",
        "test_mut_ref_typing_invariant",
        "verified",
        2,
    ),
    (
        "refs_mut_ref_typing_invariant_counterexample",
        "test_mut_ref_typing_invariant",
        "counterexample",
        1,
    ),
    (
        "refs_mut_ref_manual_old_snapshot_add1",
        "test_mut_ref_arg_exec manual old-state snapshot surrogate",
        "verified",
        2,
    ),
    (
        "refs_mut_ref_coerce_to_shared_ref_after_update",
        "mut_ref_coerce_to_ref_with_old_issue671 mutable-to-shared coercion surrogate",
        "verified",
        2,
    ),
    (
        "refs_local_mut_borrow_assignment",
        "test_ref_0 local &mut writeback surrogate",
        "verified",
        2,
    ),
    (
        "refs_mut_param_alias_assignment",
        "test_ref_1 scalar &mut parameter writeback surrogate",
        "verified",
        2,
    ),
    (
        "refs_mut_ref_field_borrow_assignment",
        "test_mut_ref_field_pass_1 field-borrow writeback surrogate",
        "verified",
        2,
    ),
    (
        "refs_mut_ref_field_borrow_assignment_wrong_value_counterexample",
        "test_mut_ref_field_pass_1 field-borrow stale-value surrogate",
        "counterexample",
        1,
    ),
    (
        "refs_mut_ref_arg_exec_add1_concrete",
        "test_mut_ref_arg_exec concrete add1 callee",
        "verified",
        2,
    ),
    (
        "refs_mut_ref_arg_exec_add1_wrong_value_counterexample",
        "test_mut_ref_arg_exec concrete add1 callee stale-value assertion",
        "counterexample",
        1,
    ),
    (
        "refs_mut_ref_forward_div2_callee",
        "test_mut_ref_forward concrete div2 callee",
        "verified",
        2,
    ),
    (
        "refs_mut_ref_shadow_noop",
        "test_mut_ref_shadow concrete no-op callee",
        "verified",
        2,
    ),
    (
        "refs_mut_ref_shadow_preserves_value",
        "test_mut_ref_shadow concrete shadowed alias",
        "verified",
        2,
    ),
    (
        "refs_mut_ref_shadow_wrong_value_counterexample",
        "test_mut_ref_shadow concrete shadowed alias stale-value assertion",
        "counterexample",
        1,
    ),
    (
        "refs_mut_param_alias_reborrow_assignment_currently_blocked",
        "test_ref_1 mutable-reference parameter reborrow writeback boundary",
        "verified",
        2,
    ),
    (
        "refs_mut_ref_arg_exec_caller_currently_blocked",
        "test_mut_ref_arg_exec caller post-call local assertion boundary",
        "error",
        0,
    ),
    (
        "refs_mut_ref_arg_exec_direct_param_write_currently_blocked",
        "test_mut_ref_arg_exec direct parameter dereference write boundary",
        "verified",
        2,
    ),
    // AUDITED FLIP 2026-07-09: slice B: body-assert old() renders entry; with no requires the assert over an unconstrained entry is a GENUINE CE (probed: a = u64::MAX)
    (
        "refs_mut_ref_arg_exec_old_state_currently_blocked",
        "test_mut_ref_arg_exec old-state contract boundary",
        "counterexample",
        1,
    ),
    // AUDITED FLIP (2026-07-09): error -> verified. Mut-ref slice A
    // (old(P)/*old(P) in contracts) landed: `requires(*old(a) < 10)` on a
    // scalar &mut param now parses to the entry symbol and the case
    // genuinely verifies (probed firsthand; directionality pinned by the
    // mut_ref_old_contracts battery). Body-assert old() (the sibling
    // old_state case) remains fail-closed — slice B.
    (
        "refs_mut_ref_arg_exec_old_requires_currently_blocked",
        "test_mut_ref_arg_exec old-state requires boundary",
        "verified",
        1,
    ),
    (
        "refs_mut_ref_field_and_update_currently_blocked",
        "test_mut_ref_field_and_update_pass evaluation-order/projection boundary",
        "error",
        0,
    ),
    (
        "refs_mut_ref_self_receiver_currently_blocked",
        "test_mut_ref_arg_self_pass_1 mutable self receiver boundary",
        "error",
        0,
    ),
    (
        "refs_mut_ref_generic_currently_blocked",
        "test_mut_ref_generic_1 generic mutable-reference boundary",
        "error",
        0,
    ),
    (
        "refs_tracked_mut_ref_borrow_currently_blocked",
        "test_mut_ref_arg_proof_pass tracked mutable-reference boundary",
        "error",
        0,
    ),
    (
        "refs_overloaded_deref_currently_blocked",
        "test_overloaded_deref overloaded-deref boundary",
        "error",
        0,
    ),
];

const UNSUPPORTED_CASES: &[(&str, &str, &[&str])] = &[
    (
        "refs_mut_ref_arg_exec_caller_currently_blocked",
        "test_mut_ref_arg_exec caller post-call local assertion boundary",
        &[
            "unresolved variable `a`",
            "&mut not supported",
            "mutable-reference",
        ],
    ),
    // refs_mut_ref_arg_exec_old_state_currently_blocked removed 2026-07-09: audited slice-B flip (see expected-cases table).
    // refs_mut_ref_arg_exec_old_requires_currently_blocked removed 2026-07-09:
    // it now VERIFIES via mut-ref slice A (old() in contracts) — see the
    // audited flip in the expected-cases table.
    (
        "refs_mut_ref_field_and_update_currently_blocked",
        "test_mut_ref_field_and_update_pass evaluation-order/projection boundary",
        &[
            "assignment through a mutable-reference projection is unsupported",
            "unsupported",
            "borrow",
            "pair",
        ],
    ),
    (
        "refs_mut_ref_self_receiver_currently_blocked",
        "test_mut_ref_arg_self_pass_1 mutable self receiver boundary",
        &[
            "unresolved variable `value`",
            "unsupported method",
            "method",
            "unknown return type",
            "add1",
        ],
    ),
    (
        "refs_mut_ref_generic_currently_blocked",
        "test_mut_ref_generic_1 generic mutable-reference boundary",
        &["generic", "type parameter", "unsupported", "unknown type"],
    ),
    (
        "refs_tracked_mut_ref_borrow_currently_blocked",
        "test_mut_ref_arg_proof_pass tracked mutable-reference boundary",
        &["Tracked", "borrow", "unsupported method", "method"],
    ),
    (
        "refs_overloaded_deref_currently_blocked",
        "test_overloaded_deref overloaded-deref boundary",
        &["Deref", "deref", "unsupported", "unknown return type"],
    ),
];

#[test]
fn refs_rs_port_file_is_rust_syntax() {
    let source = std::fs::read_to_string(refs_port_path()).expect("refs port should be readable");
    syn::parse_file(&source).expect("refs port should parse as ordinary Rust syntax");
}

#[test]
fn refs_rs_pinned_upstream_case_shapes_are_present() {
    let path = pinned_upstream_refs_path();
    if !path.exists() {
        eprintln!(
            "skipping pinned upstream refs.rs shape check; missing {}",
            path.display()
        );
        return;
    }

    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", path.display()));
    for expected in [
        "#[test] test_ref_0",
        "#[test] test_ref_1",
        "#[test] test_return_ref_0",
        "#[test] test_return_ref_named_lifetime",
        "#[test] test_mut_ref_arg_exec",
        "fn add1(a: &mut u64)",
        "requires *old(a) < 10",
        "fn caller()",
        "#[test] test_mut_ref_arg_proof_fail",
        "#[ignore] #[test] test_mut_ref_arg_proof_pass",
        "fn add1(Tracked(a): Tracked<&mut int>)",
        "#[test] test_mut_ref_arg_invalid_spec",
        "in requires, use `old(a)`",
        "#[test] test_mut_ref_arg_invalid_spec_decreases",
        "#[test] test_mut_ref_arg_spec",
        "&mut parameter not allowed for spec functions",
        "#[test] test_mut_ref_arg_self_pass_1",
        "#[test] test_mut_ref_arg_self_pass_2",
        "#[test] test_mut_ref_arg_self_complex_pass",
        "pub fn add1(&mut self)",
        "#[test] test_mut_ref_generic_1",
        "fn add1<A>(a: &mut A)",
        "#[test] test_mut_ref_old_shadow",
        "#[test] test_mut_ref_forward",
        "fn div2(a: &mut u64)",
        "#[test] test_mut_ref_trigger_0",
        "#[test] test_mut_ref_old_trigger",
        "#[test] test_mut_ref_shadow",
        "fn foo(x: &mut u32)",
        "#[test] test_mut_ref_field_pass_1",
        "#[test] test_mut_ref_field_pass_2",
        "#[test] test_mut_ref_field_and_update_pass",
        "fn add1(a: &mut u32, b: &mut i32)",
        "s.a = add1(&mut s.a)",
        "#[test] deref_vec_ok",
        "#[test] deref_vec_fails",
        "#[test] deref_vec_alone1",
        "let s2: &[u8] = &v;",
        "assert(s0@ == s2@);",
        "#[test] test_mut_ref_typing_invariant",
        "#[test] mutref_arg_ref_unsupported",
        "#[test] mut_ref_coerce_to_ref_with_old_issue671",
        "#[test] test_overloaded_deref",
        "fn do_exec_deref(x: &X)",
    ] {
        assert!(
            source.contains(expected),
            "pinned upstream refs.rs should still contain {expected}"
        );
    }
}

#[test]
fn refs_rs_expected_case_metadata_is_exact() {
    let source = std::fs::read_to_string(refs_port_path()).expect("refs port should be readable");
    assert!(
        source.contains("REFS_RS_EXPECTED_CASES") && source.contains("refs_rs_expected_cases"),
        "refs port metadata should expose the expected-case inventory"
    );

    let actual = parse_expected_case_metadata(&source);
    assert_eq!(
        actual,
        expected_metadata(),
        "refs port metadata should exactly match the regression inventory"
    );

    for (case, upstream_case, status, min_obligations) in &actual {
        assert!(
            matches!(status.as_str(), "verified" | "counterexample" | "error"),
            "{case} ({upstream_case}) should use a schema-valid status, got {status}"
        );
        assert!(
            !status.eq_ignore_ascii_case("unknown"),
            "{case} ({upstream_case}) must not inventory Unknown as evidence"
        );
        if status == "error" {
            assert_eq!(
                *min_obligations, 0,
                "{case} ({upstream_case}) error metadata should not count obligations"
            );
            assert!(
                UNSUPPORTED_CASES
                    .iter()
                    .any(|(unsupported_case, unsupported_upstream, _)| {
                        *unsupported_case == case && *unsupported_upstream == upstream_case
                    }),
                "{case} ({upstream_case}) error metadata should have fail-closed fragments"
            );
        }
    }

    for (case, upstream_case, _) in UNSUPPORTED_CASES {
        assert!(
            actual
                .iter()
                .any(|(actual_case, actual_upstream, status, min_obligations)| {
                    actual_case == case
                        && actual_upstream == upstream_case
                        && status == "error"
                        && *min_obligations == 0
                }),
            "{case} ({upstream_case}) fail-closed case should be present as error metadata"
        );
    }
}

#[test]
fn refs_rs_expected_case_metadata_matches_manifest() {
    let source = std::fs::read_to_string(refs_port_path()).expect("refs port should be readable");

    assert_eq!(
        manifest_expected_case_metadata(),
        attach_error_patterns(parse_expected_case_metadata(&source)),
        "refs manifest expected_cases should match port metadata and fail-closed patterns exactly"
    );
}

#[test]
fn refs_rs_verified_subset_verifies_from_file() {
    let path = refs_port_path();
    let path = path.to_str().expect("port path should be UTF-8");

    for (case, upstream_case, status, min_obligations) in EXPECTED_CASE_METADATA
        .iter()
        .filter(|(_, _, status, _)| *status == "verified")
    {
        let result = verify_case(path, case, upstream_case);
        assert!(
            matches!(result, VerifyResult::Verified),
            "{case} ({upstream_case}) should verify, got: {result:?}"
        );
        assert_eq!(*status, "verified");

        let obligations = obligation_count(case, upstream_case);
        assert!(
            obligations >= *min_obligations,
            "{case} ({upstream_case}) should have at least {min_obligations} obligations, got {obligations}"
        );
    }
}

#[test]
fn refs_rs_counterexample_subset_is_rejected_from_file() {
    let path = refs_port_path();
    let path = path.to_str().expect("port path should be UTF-8");

    for (case, upstream_case, status, min_obligations) in EXPECTED_CASE_METADATA
        .iter()
        .filter(|(_, _, status, _)| *status == "counterexample")
    {
        let result = verify_case(path, case, upstream_case);
        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "{case} ({upstream_case}) should be rejected, got: {result:?}"
        );
        assert_eq!(*status, "counterexample");

        let obligations = obligation_count(case, upstream_case);
        assert!(
            obligations >= *min_obligations,
            "{case} ({upstream_case}) should have at least {min_obligations} obligations, got {obligations}"
        );
    }
}

#[test]
fn refs_rs_unsupported_mutation_subset_fails_closed_from_file() {
    let path = refs_port_path();
    let path = path.to_str().expect("port path should be UTF-8");

    for (case, upstream_case, expected_messages) in UNSUPPORTED_CASES {
        expect_fail_closed_error_contains_any(path, case, upstream_case, expected_messages);
    }
}
