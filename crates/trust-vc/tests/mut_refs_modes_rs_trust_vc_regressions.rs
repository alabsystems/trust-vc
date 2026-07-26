// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Executable guards for the first upstream mut_refs_modes.rs TrustVc scout.
//!
//! These tests intentionally keep the upstream file classified as an
//! unsupported gap. They pin only Rust-valid executable mutable-reference and
//! Ghost wrapper behavior, reject concrete stale-snapshot/wrong-post-state
//! assertions, and keep Verus-only resolution/old-state/tracked helper
//! surfaces fail-closed.

mod common;

use std::path::PathBuf;
use trust_vc_core::{
    extract_verification_conditions_with_file_context, verify_function_from_file, VerifyResult,
};

fn mut_refs_modes_port_path() -> PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../evals/verus/ported/mut_refs_modes.rs")
}

fn mut_refs_modes_upstream_path() -> PathBuf {
    common::pinned_verus_test_path("mut_refs_modes.rs")
}

fn verus_manifest_path() -> PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/verus-tests.json")
}

fn active_upstream_cases(source: &str) -> Vec<String> {
    source
        .lines()
        .filter_map(|line| {
            let trimmed = line.trim();
            let marker = "#[test]";
            let start = trimmed.find(marker)?;
            let rest = trimmed[start + marker.len()..].trim();
            rest.split_whitespace().next().map(str::to_string)
        })
        .collect()
}

fn string_literal(expr: &syn::Expr, field: &str) -> String {
    match expr {
        syn::Expr::Lit(syn::ExprLit {
            lit: syn::Lit::Str(lit),
            ..
        }) => lit.value(),
        _ => panic!("expected string literal for {field}"),
    }
}

fn usize_literal(expr: &syn::Expr, field: &str) -> usize {
    match expr {
        syn::Expr::Lit(syn::ExprLit {
            lit: syn::Lit::Int(lit),
            ..
        }) => lit
            .base10_parse()
            .unwrap_or_else(|err| panic!("failed to parse {field} as usize: {err}")),
        _ => panic!("expected usize literal for {field}"),
    }
}

fn string_slice(expr: &syn::Expr, field: &str) -> Vec<String> {
    let syn::Expr::Reference(reference) = expr else {
        panic!("expected referenced string-slice literal for {field}");
    };
    let syn::Expr::Array(array) = reference.expr.as_ref() else {
        panic!("expected array literal for {field}");
    };

    array
        .elems
        .iter()
        .map(|entry| string_literal(entry, field))
        .collect()
}

fn port_expected_case_metadata() -> Vec<(String, String, String, usize)> {
    let source = std::fs::read_to_string(mut_refs_modes_port_path())
        .expect("mut_refs_modes port should be readable");
    let file = syn::parse_file(&source).expect("mut_refs_modes port should parse as Rust syntax");
    let item = file
        .items
        .iter()
        .find_map(|item| match item {
            syn::Item::Const(item) if item.ident == "MUT_REFS_MODES_RS_EXPECTED_CASES" => {
                Some(item)
            }
            _ => None,
        })
        .expect("mut_refs_modes port should expose MUT_REFS_MODES_RS_EXPECTED_CASES");

    let syn::Expr::Reference(reference) = item.expr.as_ref() else {
        panic!("MUT_REFS_MODES_RS_EXPECTED_CASES should be a borrowed slice literal");
    };
    let syn::Expr::Array(array) = reference.expr.as_ref() else {
        panic!("MUT_REFS_MODES_RS_EXPECTED_CASES should borrow an array literal");
    };

    array
        .elems
        .iter()
        .map(|entry| {
            let syn::Expr::Tuple(tuple) = entry else {
                panic!("MUT_REFS_MODES_RS_EXPECTED_CASES entry should be a tuple");
            };
            assert_eq!(
                tuple.elems.len(),
                4,
                "metadata entries should be (case, upstream, status, min_obligations)"
            );

            (
                string_literal(&tuple.elems[0], "case"),
                string_literal(&tuple.elems[1], "upstream_case"),
                string_literal(&tuple.elems[2], "status"),
                usize_literal(&tuple.elems[3], "min_obligations"),
            )
        })
        .collect()
}

fn port_fail_closed_error_pattern_metadata() -> Vec<(String, Vec<String>)> {
    let source = std::fs::read_to_string(mut_refs_modes_port_path())
        .expect("mut_refs_modes port should be readable");
    let file = syn::parse_file(&source).expect("mut_refs_modes port should parse as Rust syntax");
    let item = file
        .items
        .iter()
        .find_map(|item| match item {
            syn::Item::Const(item)
                if item.ident == "MUT_REFS_MODES_RS_FAIL_CLOSED_ERROR_PATTERNS" =>
            {
                Some(item)
            }
            _ => None,
        })
        .expect("mut_refs_modes port should expose MUT_REFS_MODES_RS_FAIL_CLOSED_ERROR_PATTERNS");

    let syn::Expr::Reference(reference) = item.expr.as_ref() else {
        panic!("MUT_REFS_MODES_RS_FAIL_CLOSED_ERROR_PATTERNS should be a borrowed slice literal");
    };
    let syn::Expr::Array(array) = reference.expr.as_ref() else {
        panic!("MUT_REFS_MODES_RS_FAIL_CLOSED_ERROR_PATTERNS should borrow an array literal");
    };

    array
        .elems
        .iter()
        .map(|entry| {
            let syn::Expr::Tuple(tuple) = entry else {
                panic!("MUT_REFS_MODES_RS_FAIL_CLOSED_ERROR_PATTERNS entry should be a tuple");
            };
            assert_eq!(
                tuple.elems.len(),
                2,
                "error-pattern metadata entries should be (case, patterns)"
            );

            (
                string_literal(&tuple.elems[0], "case"),
                string_slice(&tuple.elems[1], "expected_error_patterns"),
            )
        })
        .collect()
}

fn expected_fail_closed_error_pattern_metadata() -> Vec<(String, Vec<String>)> {
    FAIL_CLOSED_CASES
        .iter()
        .map(|(case, _, patterns)| {
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
                == Some("source/rust_verify_test/tests/mut_refs_modes.rs")
        })
        .expect("Verus manifest should contain mut_refs_modes.rs row")
        .clone()
}

fn manifest_expected_case_metadata() -> Vec<(String, String, String, usize)> {
    manifest_row()["expected_cases"]
        .as_array()
        .expect("mut_refs_modes manifest row should contain expected_cases")
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
        .expect("mut_refs_modes manifest row should contain expected_cases")
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

fn verify_port_case(case: &str, upstream_case: &str) -> (VerifyResult, usize) {
    let path = mut_refs_modes_port_path();
    let path_str = path
        .to_str()
        .expect("mut_refs_modes port path should be UTF-8");
    let result = verify_function_from_file(path_str, case)
        .unwrap_or_else(|err| panic!("{case} ({upstream_case}) should extract: {err}"));

    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|err| panic!("{} should be readable: {err}", path.display()));
    let file = syn::parse_file(&source)
        .unwrap_or_else(|err| panic!("{} should parse as Rust syntax: {err}", path.display()));
    let function = file
        .items
        .iter()
        .find_map(|item| match item {
            syn::Item::Fn(function) if function.sig.ident == case => Some(function),
            _ => None,
        })
        .unwrap_or_else(|| {
            panic!(
                "{case} ({upstream_case}) should exist in {}",
                path.display()
            )
        });
    let vc = extract_verification_conditions_with_file_context(&file, function)
        .unwrap_or_else(|err| panic!("{case} ({upstream_case}) should extract VCs: {err}"));

    (result, vc.obligations().len())
}

fn fail_closed_message(case: &str, upstream_case: &str) -> String {
    let path = mut_refs_modes_port_path();
    let path = path
        .to_str()
        .expect("mut_refs_modes port path should be UTF-8");

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

const VERIFIED_CASES: &[(&str, &str, usize)] = &[
    (
        "mut_refs_modes_exec_local_mut_borrow_verified",
        "mut_borrow_of_exec_local_in_tracked_local_decl executable analogue",
        2,
    ),
    (
        "mut_refs_modes_exec_struct_field_mut_ref_write_verified",
        "modify_exec_place_in_proof_code executable struct-field analogue",
        2,
    ),
    (
        "mut_refs_modes_exec_field_borrow_write_verified",
        "mut_ref_tracked_place_in_proof_code executable field-borrow analogue",
        2,
    ),
    (
        "mut_refs_modes_exec_param_alias_write_verified",
        "tracked_swap_requires_non_exec_place2 executable parameter-alias analogue",
        2,
    ),
    (
        "mut_refs_modes_exec_two_local_swap_verified",
        "tracked_swap_requires_non_exec_place executable two-local swap analogue",
        2,
    ),
    (
        "mut_refs_modes_ghost_wrapper_snapshot_read_verified",
        "ghost_places_dont_count_as_moves executable Ghost<T> snapshot analogue",
        1,
    ),
    (
        "mut_refs_modes_ghost_wrapper_copy_read_verified",
        "ghost_overloaded_deref_1 Ghost<T> copy/view analogue",
        1,
    ),
    (
        "mut_refs_modes_tracked_wrapper_copy_verified",
        "tracked_overloaded_deref_1 Tracked<T> copy wrapper analogue",
        1,
    ),
    (
        "mut_refs_modes_ghost_tuple_projection_verified",
        "ghost_auto_deref_1 Ghost<T> tuple projection boundary",
        2,
    ),
];

const COUNTEREXAMPLE_CASES: &[(&str, &str, usize)] = &[
    (
        "mut_refs_modes_stale_exec_snapshot_counterexample",
        "ghost_places_dont_resolve stale snapshot analogue",
        1,
    ),
    (
        "mut_refs_modes_exec_two_local_swap_wrong_post_counterexample",
        "tracked_swap_requires_non_exec_place wrong post-state analogue",
        1,
    ),
    (
        "mut_refs_modes_ghost_wrapper_false_tail_counterexample",
        "ghost_overloaded_deref_1 Ghost<T> false-tail analogue",
        1,
    ),
    (
        "mut_refs_modes_tracked_wrapper_false_tail_counterexample",
        "tracked_overloaded_deref_1 Tracked<T> false-tail analogue",
        1,
    ),
];

const FAIL_CLOSED_CASES: &[(&str, &str, &[&str])] = &[
    (
        "mut_refs_modes_has_resolved_currently_blocked",
        "has_resolved mutable-reference resolution predicates",
        &["has_resolved"],
    ),
    (
        "mut_refs_modes_old_state_after_mut_ref_write_currently_blocked",
        "final/old mutable-reference post-state reasoning",
        &["Unsupported old-state expression `old(...)`", "old"],
    ),
    (
        "mut_refs_modes_ghost_constructor_currently_blocked",
        "Ghost constructor boundary for wrapped ghost-place mutation",
        &["Ghost::new"],
    ),
    (
        "mut_refs_modes_tracked_get_currently_blocked",
        "Tracked<T> get overloaded-deref boundary",
        &["get"],
    ),
    (
        "mut_refs_modes_tracked_borrow_currently_blocked",
        "Tracked<T> borrow auto-deref boundary",
        &["borrow"],
    ),
    (
        "mut_refs_modes_tracked_swap_currently_blocked",
        "tracked_swap requires proof-mode non-exec places",
        &["tracked_swap"],
    ),
    (
        "mut_refs_modes_tracked_take_currently_blocked",
        "tracked_take requires proof-mode non-exec places",
        &["tracked_take"],
    ),
    (
        "mut_refs_modes_mut_ref_tracked_currently_blocked",
        "mut_ref_tracked proof-only tracked mutable-reference conversion",
        &["&mut not supported"],
    ),
];

const EXPECTED_CASE_METADATA: &[(&str, &str, &str, usize)] = &[
    (
        "mut_refs_modes_exec_local_mut_borrow_verified",
        "mut_borrow_of_exec_local_in_tracked_local_decl executable analogue",
        "verified",
        2,
    ),
    (
        "mut_refs_modes_exec_struct_field_mut_ref_write_verified",
        "modify_exec_place_in_proof_code executable struct-field analogue",
        "verified",
        2,
    ),
    (
        "mut_refs_modes_exec_field_borrow_write_verified",
        "mut_ref_tracked_place_in_proof_code executable field-borrow analogue",
        "verified",
        2,
    ),
    (
        "mut_refs_modes_exec_param_alias_write_verified",
        "tracked_swap_requires_non_exec_place2 executable parameter-alias analogue",
        "verified",
        2,
    ),
    (
        "mut_refs_modes_exec_two_local_swap_verified",
        "tracked_swap_requires_non_exec_place executable two-local swap analogue",
        "verified",
        2,
    ),
    (
        "mut_refs_modes_ghost_wrapper_snapshot_read_verified",
        "ghost_places_dont_count_as_moves executable Ghost<T> snapshot analogue",
        "verified",
        1,
    ),
    (
        "mut_refs_modes_ghost_wrapper_copy_read_verified",
        "ghost_overloaded_deref_1 Ghost<T> copy/view analogue",
        "verified",
        1,
    ),
    (
        "mut_refs_modes_tracked_wrapper_copy_verified",
        "tracked_overloaded_deref_1 Tracked<T> copy wrapper analogue",
        "verified",
        1,
    ),
    (
        "mut_refs_modes_stale_exec_snapshot_counterexample",
        "ghost_places_dont_resolve stale snapshot analogue",
        "counterexample",
        1,
    ),
    (
        "mut_refs_modes_exec_two_local_swap_wrong_post_counterexample",
        "tracked_swap_requires_non_exec_place wrong post-state analogue",
        "counterexample",
        1,
    ),
    (
        "mut_refs_modes_ghost_wrapper_false_tail_counterexample",
        "ghost_overloaded_deref_1 Ghost<T> false-tail analogue",
        "counterexample",
        1,
    ),
    (
        "mut_refs_modes_tracked_wrapper_false_tail_counterexample",
        "tracked_overloaded_deref_1 Tracked<T> false-tail analogue",
        "counterexample",
        1,
    ),
    (
        "mut_refs_modes_has_resolved_currently_blocked",
        "resolve_tracked_param_but_not_ghost_param",
        "error",
        0,
    ),
    (
        "mut_refs_modes_old_state_after_mut_ref_write_currently_blocked",
        "wrapped_params",
        "error",
        0,
    ),
    (
        "mut_refs_modes_ghost_tuple_projection_verified",
        "ghost_auto_deref_1 Ghost<T> tuple projection boundary",
        "verified",
        2,
    ),
    (
        "mut_refs_modes_ghost_constructor_currently_blocked",
        "modify_ghost_wrapped_type_in_proof_code Ghost constructor boundary",
        "error",
        0,
    ),
    (
        "mut_refs_modes_tracked_get_currently_blocked",
        "tracked_overloaded_deref_1 Tracked<T> get boundary",
        "error",
        0,
    ),
    (
        "mut_refs_modes_tracked_borrow_currently_blocked",
        "tracked_auto_deref_1 Tracked<T> borrow boundary",
        "error",
        0,
    ),
    (
        "mut_refs_modes_tracked_swap_currently_blocked",
        "tracked_swap_requires_non_exec_place",
        "error",
        0,
    ),
    (
        "mut_refs_modes_tracked_take_currently_blocked",
        "tracked_take_requires_non_exec_place",
        "error",
        0,
    ),
    (
        "mut_refs_modes_mut_ref_tracked_currently_blocked",
        "mut_ref_tracked3",
        "error",
        0,
    ),
];

const PINNED_UPSTREAM_ACTIVE_CASES: &[&str] = &[
    "mut_borrow_of_ghost_local_in_proof_fn",
    "mut_borrow_of_tracked_local_in_proof_fn",
    "mut_borrow_of_ghost_local_in_exec_fn",
    "mut_borrow_of_tracked_local_in_exec_fn",
    "mut_borrow_of_ghost_local_in_proof_block",
    "mut_borrow_of_tracked_local_in_proof_block_to_ghost",
    "mut_borrow_of_exec_local_in_proof_block_to_tracked",
    "mut_borrow_of_exec_local_in_tracked_local_decl",
    "mut_borrow_lifetime_error",
    "mut_borrow_lifetime_error2",
    "mut_borrow_in_ghost_decl",
    "mut_borrow_in_spec_fn",
    "mut_borrow_in_assert_by",
    "modify_tracked_place_in_exec_code",
    "modify_ghost_place_in_exec_code",
    "modify_ghost_place_in_assert_by",
    "modify_tracked_place_in_proof_code",
    "modify_ghost_place_in_proof_code",
    "modify_exec_place_in_proof_code",
    "modify_exec_place_in_proof_code2",
    "modify_tracked_type_in_proof_code",
    "modify_tracked_wrapped_type_in_proof_code",
    "modify_ghost_wrapped_type_in_proof_code",
    "mut_ref_tracked_place_in_proof_code",
    "mut_ref_tracked_place_in_proof_code2",
    "mut_ref_ghost_place_in_proof_code",
    "no_mutation_through_ghost_mut_ref",
    "no_mutation_through_ghost_mut_ref2",
    "no_mutation_through_ghost_mut_ref3",
    "no_mut_ref_through_ghost_mut_ref",
    "no_mut_ref_through_ghost_mut_ref2",
    "no_mut_ref_through_ghost_mut_ref3",
    "read_through_ghost_mut_ref_ok",
    "cant_move_out_of_tracked_location",
    "ghost_places_dont_count_as_moves",
    "ghost_places_dont_resolve",
    "ghost_places_dont_resolve2",
    "tracked_places_lifetime_error",
    "tracked_places_lifetime_error2",
    "tracked_places_lifetime_error3",
    "struct_with_ghost_and_tracked_fields",
    "reading_ghost_field_is_not_move",
    "modify_ghost_fields_through_mut_refs",
    "modify_ghost_fields_doesnt_reinitialize1",
    "modify_ghost_fields_doesnt_reinitialize2",
    "deref_ghost_mut_ref_is_ghost",
    "dont_resolve_ghost_field",
    "dont_resolve_ghost_field2",
    "resolve_tracked_param_but_not_ghost_param",
    "read_from_borrowed_ghost_location_and_then_assign_to_mut_ref",
    "tracked_swap_requires_non_exec_place",
    "tracked_swap_requires_non_exec_place2",
    "tracked_swap_requires_non_exec_place3",
    "tracked_swap_requires_non_exec_place4",
    "tracked_swap_requires_non_exec_place5",
    "tracked_swap_requires_non_exec_place6",
    "tracked_swap_requires_non_exec_place7",
    "tracked_swap_requires_non_exec_place8",
    "tracked_swap_requires_non_exec_place9",
    "tracked_take_requires_non_exec_place",
    "tracked_take_requires_non_exec_place2",
    "tracked_take_requires_non_exec_place3",
    "tracked_take_requires_non_exec_place4",
    "tracked_swap_option_not_ok",
    "wrapped_params",
    "wrapped_params_reborrow",
    "wrapped_mut_ref_params_resolved",
    "tracked_overloaded_deref_1",
    "tracked_overloaded_deref_2",
    "tracked_overloaded_deref_3",
    "tracked_overloaded_deref_lifetime_1",
    "tracked_overloaded_deref_lifetime_2",
    "ghost_overloaded_deref_1",
    "ghost_overloaded_deref_2",
    "ghost_overloaded_deref_3",
    "ghost_overloaded_deref_4",
    "ghost_overloaded_deref_lifetime",
    "tracked_auto_deref_1",
    "tracked_auto_deref_2",
    "tracked_auto_deref_3",
    "tracked_auto_deref_lifetime_1",
    "tracked_auto_deref_lifetime_2",
    "ghost_auto_deref_1",
    "ghost_auto_deref_2",
    "ghost_auto_deref_3",
    "ghost_auto_deref_4",
    "ghost_auto_deref_lifetime",
    "deref_generic_use_err_deref_tracked",
    "deref_generic_use_err_deref_mut_tracked",
    "deref_generic_use_err_deref_ghost",
    "deref_generic_use_err_deref_mut_ghost",
    "tracked_deref_explicit",
    "tracked_deref_mut_explicit",
    "old_mut_ref_tracked_overloaded_deref_1",
    "old_mut_ref_ghost_overloaded_deref_1",
    "old_mut_ref_tracked_auto_deref_1",
    "old_mut_ref_ghost_auto_deref_1",
    "old_mut_ref_overloaded_deref_mode_err_tracked_borrow",
    "old_mut_ref_overloaded_deref_mode_err_tracked_borrow_mut",
    "old_mut_ref_overloaded_deref_mode_err_ghost_borrow",
    "old_mut_ref_overloaded_deref_mode_err_ghost_borrow_mut",
    "old_mut_ref_auto_deref_mode_err_tracked_borrow",
    "old_mut_ref_auto_deref_mode_err_tracked_borrow_mut",
    "old_mut_ref_auto_deref_mode_err_ghost_borrow",
    "old_mut_ref_auto_deref_mode_err_ghost_borrow_mut",
    "write_in_proof_mode_with_decoration_1",
    "write_in_proof_mode_with_decoration_2",
    "write_in_proof_mode_with_decoration_3",
    "write_in_proof_mode_with_decoration_4",
    "write_in_proof_mode_with_decoration_5",
    "write_in_proof_mode_with_decoration_6",
    "mut_ref_tracked1",
    "mut_ref_tracked2",
    "mut_ref_tracked3",
    "mut_ref_tracked4",
    "mut_ref_tracked5",
    "mut_ref_tracked6",
    "mut_ref_tracked7",
    "mut_ref_tracked8",
    "mut_ref_tracked9_proph",
    "mut_ref_tracked10_proph",
];

#[test]
fn mut_refs_modes_rs_port_file_is_rust_syntax() {
    let source = std::fs::read_to_string(mut_refs_modes_port_path())
        .expect("mut_refs_modes port should be readable");
    syn::parse_file(&source).expect("mut_refs_modes port should parse as ordinary Rust syntax");
}

#[test]
fn mut_refs_modes_rs_expected_case_metadata_is_exact() {
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
        port_expected_case_metadata(),
        expected,
        "mut_refs_modes port metadata should match the regression inventory exactly"
    );

    let mut expected_case_names = EXPECTED_CASE_METADATA
        .iter()
        .map(|(case, _, _, _)| *case)
        .collect::<Vec<_>>();
    expected_case_names.sort_unstable();

    let mut categorized_case_names = VERIFIED_CASES
        .iter()
        .map(|(case, _, _)| *case)
        .chain(COUNTEREXAMPLE_CASES.iter().map(|(case, _, _)| *case))
        .chain(FAIL_CLOSED_CASES.iter().map(|(case, _, _)| *case))
        .collect::<Vec<_>>();
    categorized_case_names.sort_unstable();

    assert_eq!(
        expected_case_names, categorized_case_names,
        "every metadata case should have exactly one regression expectation"
    );
}

#[test]
fn mut_refs_modes_rs_fail_closed_error_pattern_metadata_is_exact() {
    let source = std::fs::read_to_string(mut_refs_modes_port_path())
        .expect("mut_refs_modes port should be readable");
    assert!(
        source.contains("MUT_REFS_MODES_RS_FAIL_CLOSED_ERROR_PATTERNS")
            && source.contains("mut_refs_modes_rs_fail_closed_error_patterns"),
        "mut_refs_modes port should expose fail-closed error-pattern metadata helpers"
    );

    let actual = port_fail_closed_error_pattern_metadata();
    assert_eq!(
        actual,
        expected_fail_closed_error_pattern_metadata(),
        "mut_refs_modes fail-closed error-pattern metadata should match the regression inventory exactly"
    );
    for (case, patterns) in actual {
        assert!(
            !patterns.is_empty(),
            "{case} should declare at least one stable expected_error_patterns fragment"
        );
    }
}

#[test]
fn mut_refs_modes_rs_expected_case_metadata_matches_manifest() {
    assert_eq!(
        port_expected_case_metadata(),
        manifest_expected_case_metadata(),
        "mut_refs_modes port metadata should match the manifest inventory exactly"
    );
    assert_eq!(
        port_fail_closed_error_pattern_metadata(),
        manifest_fail_closed_error_pattern_metadata(),
        "mut_refs_modes fail-closed metadata should match manifest expected_error_patterns exactly"
    );
}

#[test]
fn mut_refs_modes_rs_pinned_upstream_case_shapes_are_present() {
    let path = mut_refs_modes_upstream_path();
    if !path.exists() {
        eprintln!(
            "skipping pinned upstream mut_refs_modes.rs shape check; missing {}",
            path.display()
        );
        return;
    }

    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", path.display()));

    let cases = active_upstream_cases(&source);
    let expected_cases = PINNED_UPSTREAM_ACTIVE_CASES
        .iter()
        .map(|case| (*case).to_string())
        .collect::<Vec<_>>();
    assert_eq!(
        cases, expected_cases,
        "pinned upstream mut_refs_modes.rs active case inventory changed"
    );

    for expected in [
        "let tracked mut_ret = &mut x;",
        "cannot access spec-mode place in executable context",
        "cannot mutate exec-mode place in proof-code",
        "let tracked z = &mut mut_ref.y.borrow_mut().0;",
        "assert(has_resolved(mut_ref));",
        "let ghost snapshot = mut_ref;",
        "assert(has_resolved(snapshot)); // FAILS",
        "struct Pair<A, B>(Tracked<A>, Ghost<B>);",
        "tracked_swap(a_ref, b_ref);",
        "let tracked x = x.tracked_take();",
        "ensures final(x).view() == old(x).view() + 1",
        "let tracked y: &mut Ghost<u64> = &mut *x;",
        "let ghost y: u64 = x.0;",
        "`mut_ref_tracked` must be in a 'proof' block",
        "mut_borrow_of_exec_local_in_tracked_local_decl",
        "ghost_places_dont_count_as_moves",
        "ghost_places_dont_resolve",
        "has_resolved",
        "tracked_swap_requires_non_exec_place",
        "tracked_take_requires_non_exec_place",
        "mut_ref_tracked1",
        "mut_ref_tracked3",
        "ghost_auto_deref_1",
    ] {
        assert!(
            source.contains(expected),
            "upstream mut_refs_modes.rs should contain {expected}"
        );
    }
}

#[test]
fn mut_refs_modes_rs_verified_subset_verifies_from_file() {
    for (case, upstream_case, min_obligations) in VERIFIED_CASES {
        let (result, obligations) = verify_port_case(case, upstream_case);
        assert!(
            obligations >= *min_obligations,
            "{case} ({upstream_case}) should collect at least {min_obligations} obligation(s), got {obligations}"
        );
        assert!(
            matches!(result, VerifyResult::Verified),
            "{case} ({upstream_case}) should verify, got: {result:?}"
        );
    }
}

#[test]
fn mut_refs_modes_rs_stale_snapshot_assertion_is_rejected_from_file() {
    for (case, upstream_case, min_obligations) in COUNTEREXAMPLE_CASES {
        let (result, obligations) = verify_port_case(case, upstream_case);
        assert!(
            obligations >= *min_obligations,
            "{case} ({upstream_case}) should collect at least {min_obligations} obligation(s), got {obligations}"
        );
        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "{case} ({upstream_case}) should be rejected, got: {result:?}"
        );
    }
}

#[test]
fn mut_refs_modes_rs_verus_resolution_surfaces_fail_closed_from_file() {
    for (case, upstream_case, expected_fragments) in FAIL_CLOSED_CASES {
        let message = fail_closed_message(case, upstream_case);
        for expected_fragment in *expected_fragments {
            assert!(
                message.contains(expected_fragment),
                "{case} ({upstream_case}) error should contain {expected_fragment:?}, got: {message}"
            );
        }
    }
}
