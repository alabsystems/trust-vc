// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Executable guards for the current upstream arrays.rs scout slice.
//!
//! These tests intentionally do not claim full Verus arrays parity. They prove
//! the listed upstream-derived slices execute through TrustVc while the manifest
//! keeps `source/rust_verify_test/tests/arrays.rs` fail-closed.

use std::{
    collections::{BTreeMap, BTreeSet},
    path::PathBuf,
};
use trust_vc_core::{verify_function_from_file, VerifyResult};

fn arrays_port_path() -> PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/ported/arrays.rs")
}

fn verus_manifest_path() -> PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/verus-tests.json")
}

const EXPECTED_CASES: &[(&str, &str, &str, usize)] = &[
    ("array_index_from_requires", "test1", "verified", 2),
    ("array_view_len_from_fixed_type", "test1", "verified", 1),
    (
        "array_literal_view_values",
        "test_array_literals",
        "verified",
        3,
    ),
    (
        "array_literal_named_view_values_exact",
        "test_array_literals",
        "verified",
        1,
    ),
    (
        "array_literal_concrete_param_view_values",
        "test_array_literals",
        "verified",
        1,
    ),
    (
        "array_repeat_view_values",
        "test_array_repeat",
        "verified",
        3,
    ),
    (
        "array_repeat_named_view_values_exact",
        "test_array_repeat",
        "verified",
        1,
    ),
    (
        "array_repeat_concrete_param_view_values",
        "test_array_repeat",
        "verified",
        1,
    ),
    (
        "array_literal_six_view_values_exact",
        "test_array_literals",
        "verified",
        6,
    ),
    (
        "array_repeat_six_view_values_exact",
        "test_array_repeat",
        "verified",
        6,
    ),
    (
        "array_clone_repeat_literal",
        "test_array_clone",
        "verified",
        1,
    ),
    (
        "array_index_assignment_repeat_literal",
        "test1",
        "verified",
        1,
    ),
    (
        "array_parenthesized_index_assignment_repeat_literal",
        "test1",
        "verified",
        1,
    ),
    (
        "array_index_assignment_pair_literal_exact",
        "test1",
        "verified",
        1,
    ),
    (
        "array_index_assignment_copied_param_array",
        "test1",
        "verified",
        1,
    ),
    (
        "array_index_assignment_copied_struct_field_array",
        "test1",
        "verified",
        2,
    ),
    (
        "array_index_add_assign_repeat_literal",
        "test_array_set_assign_op",
        "verified",
        1,
    ),
    (
        "array_parenthesized_index_add_assign_repeat_literal",
        "test_array_set_assign_op",
        "verified",
        1,
    ),
    (
        "array_index_mul_assign_binary_rhs_precedence",
        "test_array_set_assign_op",
        "verified",
        1,
    ),
    (
        "array_index_add_assign_param_array",
        "test_array_set_assign_op",
        "verified",
        1,
    ),
    (
        "array_index_add_assign_mut_ref_param_array",
        "test_array_set_assign_op",
        "verified",
        1,
    ),
    (
        "array_index_assign_mut_ref_local_snapshot",
        "test_array_set_assign_op",
        "verified",
        1,
    ),
    (
        "array_index_assign_mut_ref_usize_twenty",
        "test_array_set_assign_op",
        "verified",
        1,
    ),
    (
        "array_index_add_assign_mut_ref_dependent_index",
        "test_array_set_assign_op",
        "verified",
        1,
    ),
    (
        "array_index_set_mut_ref_u8_twenty",
        "test_array_set",
        "verified",
        1,
    ),
    (
        "array_to_slice_view_len_and_index",
        "test_array_to_slice",
        "verified",
        2,
    ),
    (
        "array_to_slice_ref_view_len_exact",
        "test_array_to_slice",
        "verified",
        1,
    ),
    (
        "array_to_slice_ref_coercion_view_len_exact",
        "test_array_to_slice",
        "verified",
        1,
    ),
    (
        "array_to_slice_literal_view_len_and_index_exact",
        "test_array_to_slice",
        "verified",
        2,
    ),
    (
        "array_to_slice_local_ref_coercion_view_len_and_index_exact",
        "test_array_to_slice",
        "verified",
        1,
    ),
    (
        "array_to_slice_literal_view_contains_exact",
        "test_array_to_slice",
        "verified",
        3,
    ),
    (
        "array_literal_inequality",
        "test_array_literals",
        "verified",
        2,
    ),
    (
        "array_literal_view_to_seq_index",
        "test_array_literals",
        "verified",
        2,
    ),
    (
        "array_literal_view_to_seq_inequality",
        "test_array_literals",
        "verified",
        1,
    ),
    (
        "array_literal_view_to_seq_contains",
        "test_array_literals",
        "verified",
        2,
    ),
    (
        "array_named_inequality_and_contains",
        "test_array_literals",
        "verified",
        1,
    ),
    (
        "array_literal_view_seq_binding_contains",
        "test_array_literals",
        "verified",
        2,
    ),
    (
        "array_literal_view_seq_binding_reuse",
        "test_array_literals",
        "verified",
        2,
    ),
    (
        "array_literal_view_contains",
        "test_array_literals",
        "verified",
        2,
    ),
    (
        "array_named_view_contains",
        "test_array_literals",
        "verified",
        2,
    ),
    (
        "array_index_assign_local_snapshot_wrong_value_counterexample",
        "test_array_set_assign_op",
        "counterexample",
        1,
    ),
    (
        "array_to_slice_literal_view_false_tail_counterexample",
        "test_array_to_slice",
        "counterexample",
        1,
    ),
    (
        "array_literal_view_seq_binding_false_tail_counterexample",
        "test_array_literals",
        "counterexample",
        1,
    ),
    (
        "array_named_view_contains_false_tail_counterexample",
        "test_array_literals",
        "counterexample",
        1,
    ),
    (
        "array_const_generic_view_len_currently_blocked",
        "test1",
        "verified",
        1,
    ),
    (
        "array_index_add_assign_mut_ref_old_state_currently_blocked",
        "test_array_set_assign_op",
        "error",
        0,
    ),
    (
        "array_index_add_assign_mut_ref_alias_currently_blocked",
        "test_array_set_assign_op",
        "error",
        0,
    ),
    (
        "array_index_assignment_struct_field_target_verified",
        "test1",
        "verified",
        1,
    ),
    (
        "array_index_assignment_copied_borrowed_struct_field_array",
        "test1",
        "verified",
        1,
    ),
    (
        "array_index_add_assign_side_effect_index_currently_blocked",
        "test_array_set_assign_op_with_idx_side_effect",
        "error",
        0,
    ),
];

const VERIFIED_CASES: &[(&str, &str)] = &[
    ("array_index_from_requires", "test1/test/test7"),
    ("array_view_len_from_fixed_type", "test1/test3"),
    (
        "array_literal_view_values",
        "test_array_literals/test1 subset",
    ),
    (
        "array_literal_named_view_values_exact",
        "test_array_literals/test1 local named array",
    ),
    (
        "array_literal_concrete_param_view_values",
        "test_array_literals/test2 concrete u8 parameter subset",
    ),
    ("array_repeat_view_values", "test_array_repeat/test1 subset"),
    (
        "array_repeat_named_view_values_exact",
        "test_array_repeat/test1 local named repeat array",
    ),
    (
        "array_repeat_concrete_param_view_values",
        "test_array_repeat/test2 concrete Copy parameter subset",
    ),
    (
        "array_literal_six_view_values_exact",
        "test_array_literals/test1",
    ),
    (
        "array_repeat_six_view_values_exact",
        "test_array_repeat/test1",
    ),
    ("array_clone_repeat_literal", "test_array_clone/test"),
    (
        "array_index_assignment_repeat_literal",
        "test1/test10 indexed assignment subset",
    ),
    (
        "array_parenthesized_index_assignment_repeat_literal",
        "test1/test10 parenthesized indexed assignment subset",
    ),
    (
        "array_index_assignment_pair_literal_exact",
        "test1/test10 exact literal pair indexed assignment",
    ),
    (
        "array_index_assignment_copied_param_array",
        "test1/test6 copied fixed array parameter assignment",
    ),
    (
        "array_index_assignment_copied_struct_field_array",
        "test1/test9 copied fixed array struct-field local assignment",
    ),
    (
        "array_index_assignment_copied_borrowed_struct_field_array",
        "test1/test9 copied borrowed struct-field local array assignment",
    ),
    (
        "array_index_assignment_struct_field_target_verified",
        "test1/test9 direct owned struct-field indexed assignment target",
    ),
    (
        "array_index_add_assign_repeat_literal",
        "test_array_set_assign_op indexed assignment-op update",
    ),
    (
        "array_parenthesized_index_add_assign_repeat_literal",
        "test_array_set_assign_op parenthesized assignment-op update",
    ),
    (
        "array_index_mul_assign_binary_rhs_precedence",
        "test_array_set_assign_op assignment-op RHS precedence",
    ),
    (
        "array_index_add_assign_param_array",
        "test_array_set_assign_op fixed array parameter update subset",
    ),
    (
        "array_index_add_assign_mut_ref_param_array",
        "test_array_set_assign_op direct &mut fixed array parameter update subset",
    ),
    (
        "array_index_assign_mut_ref_local_snapshot",
        "test_array_set_assign_op direct &mut indexed assignment with local pre-state snapshot",
    ),
    (
        "array_index_assign_mut_ref_usize_twenty",
        "test_array_set_assign_op direct &mut fixed usize[20] parameter update subset",
    ),
    (
        "array_index_add_assign_mut_ref_dependent_index",
        "test_array_set_assign_op dependent &mut fixed usize[20] indexed update",
    ),
    (
        "array_index_set_mut_ref_u8_twenty",
        "test_array_set direct &mut fixed u8[20] indexed set subset",
    ),
    (
        "array_to_slice_view_len_and_index",
        "test_array_to_slice/test2 subset",
    ),
    (
        "array_to_slice_ref_view_len_exact",
        "test_array_to_slice/test1",
    ),
    (
        "array_to_slice_ref_coercion_view_len_exact",
        "test_array_to_slice/test1 exact array-to-slice coercion",
    ),
    (
        "array_to_slice_literal_view_len_and_index_exact",
        "test_array_to_slice/test2",
    ),
    (
        "array_to_slice_local_ref_coercion_view_len_and_index_exact",
        "test_array_to_slice/test2 exact local array-to-slice coercion",
    ),
    (
        "array_to_slice_literal_view_contains_exact",
        "test_array_to_slice borrowed array contains",
    ),
    ("array_literal_inequality", "test_array_literals/test4"),
    (
        "array_literal_view_to_seq_index",
        "test_array_literals/test5 subset",
    ),
    (
        "array_literal_view_to_seq_inequality",
        "test_array_literals/test5 Seq inequality subset",
    ),
    (
        "array_literal_view_to_seq_contains",
        "test_array_literals/test6 subset",
    ),
    (
        "array_named_inequality_and_contains",
        "test_array_literals/test4 exact named-array passing prefix",
    ),
    (
        "array_literal_view_seq_binding_contains",
        "test_array_literals/test6",
    ),
    (
        "array_literal_view_seq_binding_reuse",
        "test_array_literals/test6 statement-local Seq binding reuse",
    ),
    (
        "array_literal_view_contains",
        "test_array_literals/test4/test6",
    ),
    ("array_named_view_contains", "test_array_literals/test4"),
    (
        "array_const_generic_view_len_currently_blocked",
        "test1/test5 and test_array_to_slice/test3 const-generic view-len (audited flip: N+1usize and !=N false mutations both non-Verified, 2026-07-04 reconcile ledger)",
    ),
];

const COUNTEREXAMPLE_CASES: &[(&str, &str)] = &[
    (
        "array_index_assign_local_snapshot_wrong_value_counterexample",
        "test_array_set_assign_op local indexed-assignment snapshot false value assertion",
    ),
    (
        "array_to_slice_literal_view_false_tail_counterexample",
        "test_array_to_slice borrowed array view false-tail surrogate",
    ),
    (
        "array_literal_view_seq_binding_false_tail_counterexample",
        "test_array_literals/test6 Seq binding false-tail surrogate",
    ),
    (
        "array_named_view_contains_false_tail_counterexample",
        "test_array_literals named-array contains false-tail surrogate",
    ),
];

const FAIL_CLOSED_CASES: &[(&str, &str, &[&str])] = &[
    (
        "array_index_add_assign_mut_ref_old_state_currently_blocked",
        "test_array_set_assign_op &mut old-state postcondition",
        &[
            "Unsupported old-state expression `old(...)`",
            "array/reference places",
            "current state as pre-state",
        ],
    ),
    (
        "array_index_add_assign_mut_ref_alias_currently_blocked",
        "test_array_set_assign_op borrowed &mut array alias update",
        &[
            "indexed assignment through a borrowed array/reference alias",
            "aliased state as an independent array",
        ],
    ),
    (
        "array_index_add_assign_side_effect_index_currently_blocked",
        "test_array_set_assign_op_with_idx_side_effect",
        &[
            "unsupported expression",
            "&mut not supported",
            "side-effect-free",
        ],
    ),
];

#[derive(Debug, Eq, PartialEq)]
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
        .unwrap_or_else(|| panic!("arrays port should define {const_name}"));

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
    let array = referenced_array_const(file, "ARRAYS_RS_FAIL_CLOSED_ERROR_PATTERNS");
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
    let array = referenced_array_const(file, "ARRAYS_RS_EXPECTED_CASES");
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
            "duplicate arrays metadata for {case_id}"
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

fn manifest_expected_case_metadata() -> Vec<CaseMetadata> {
    let source =
        std::fs::read_to_string(verus_manifest_path()).expect("Verus manifest should be readable");
    let manifest: serde_json::Value =
        serde_json::from_str(&source).expect("Verus manifest should parse as JSON");
    let row = manifest["entries"]
        .as_array()
        .expect("Verus manifest should contain entries")
        .iter()
        .find(|entry| {
            entry["upstream_path"].as_str() == Some("source/rust_verify_test/tests/arrays.rs")
        })
        .expect("Verus manifest should contain arrays.rs row");

    row["expected_cases"]
        .as_array()
        .expect("arrays manifest row should contain expected_cases")
        .iter()
        .map(|case| CaseMetadata {
            case_id: case["case_id"]
                .as_str()
                .expect("manifest case should contain case_id")
                .to_string(),
            upstream_case_id: case["upstream_case_id"]
                .as_str()
                .expect("manifest case should contain upstream_case_id")
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

fn expected_metadata() -> Vec<CaseMetadata> {
    let error_patterns: BTreeMap<&str, Vec<String>> = FAIL_CLOSED_CASES
        .iter()
        .map(|(case_id, _, fragments)| {
            (
                *case_id,
                fragments
                    .iter()
                    .map(|fragment| (*fragment).to_string())
                    .collect(),
            )
        })
        .collect();

    EXPECTED_CASES
        .iter()
        .map(
            |(case_id, upstream_case_id, expected_verdict, min_obligations)| CaseMetadata {
                case_id: (*case_id).to_string(),
                upstream_case_id: (*upstream_case_id).to_string(),
                expected_verdict: (*expected_verdict).to_string(),
                min_obligations: *min_obligations,
                expected_error_patterns: error_patterns.get(case_id).cloned().unwrap_or_default(),
            },
        )
        .collect()
}

#[test]
fn arrays_rs_expected_case_metadata_is_exact() {
    let source =
        std::fs::read_to_string(arrays_port_path()).expect("arrays port should be readable");
    let file = syn::parse_file(&source).expect("arrays port should parse as ordinary Rust syntax");
    assert_eq!(metadata_entries(&file), expected_metadata());
    assert!(
        source.contains("arrays_rs_expected_cases"),
        "arrays port should export expected-case metadata"
    );
    assert!(
        source.contains("arrays_rs_fail_closed_error_patterns"),
        "arrays port should export fail-closed error-pattern metadata"
    );
}

#[test]
fn arrays_rs_expected_case_metadata_matches_manifest() {
    let source =
        std::fs::read_to_string(arrays_port_path()).expect("arrays port should be readable");
    let file = syn::parse_file(&source).expect("arrays port should parse as ordinary Rust syntax");

    assert_eq!(
        manifest_expected_case_metadata(),
        metadata_entries(&file),
        "arrays manifest expected_cases should match port metadata exactly"
    );
}

#[test]
fn arrays_rs_verified_subset_verifies_from_file() {
    let path = arrays_port_path();
    let path = path.to_str().expect("port path should be UTF-8");

    for (case, upstream_case) in VERIFIED_CASES {
        let result = verify_function_from_file(path, case)
            .unwrap_or_else(|err| panic!("{case} ({upstream_case}) should extract: {err}"));
        assert!(
            matches!(result, VerifyResult::Verified),
            "{case} ({upstream_case}) should verify, got: {result:?}"
        );
    }
}

#[test]
fn arrays_rs_counterexample_subset_is_rejected_from_file() {
    let path = arrays_port_path();
    let path = path.to_str().expect("port path should be UTF-8");

    for (case, upstream_case) in COUNTEREXAMPLE_CASES {
        let result = verify_function_from_file(path, case)
            .unwrap_or_else(|err| panic!("{case} ({upstream_case}) should extract: {err}"));
        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "{case} ({upstream_case}) should be rejected without relying on Unknown, got: {result:?}"
        );
    }
}

#[test]
fn arrays_rs_struct_field_array_slice_is_guarded() {
    let path = arrays_port_path();
    let path = path.to_str().expect("port path should be UTF-8");

    for case in [
        "array_index_assignment_copied_struct_field_array",
        "array_index_assignment_struct_field_target_verified",
    ] {
        let verified = verify_function_from_file(path, case)
            .unwrap_or_else(|err| panic!("{case} should extract: {err}"));
        assert!(
            matches!(verified, VerifyResult::Verified),
            "{case} should verify, got: {verified:?}"
        );
    }
}

#[test]
fn arrays_rs_unported_priority_features_fail_closed() {
    let path = arrays_port_path();
    let path = path.to_str().expect("port path should be UTF-8");

    for (case, upstream_case, expected_fragments) in FAIL_CLOSED_CASES {
        match verify_function_from_file(path, case) {
            Err(err) => {
                let message = err.to_string();
                assert!(
                    expected_fragments
                        .iter()
                        .all(|fragment| message.contains(fragment)),
                    "{case} ({upstream_case}) error should mention all of {expected_fragments:?}, got: {message}"
                );
            }
            Ok(VerifyResult::Error { message }) => {
                assert!(
                    expected_fragments
                        .iter()
                        .all(|fragment| message.contains(fragment)),
                    "{case} ({upstream_case}) error should mention all of {expected_fragments:?}, got: {message}"
                );
            }
            Ok(VerifyResult::Unknown { reason, .. }) => {
                assert!(
                    !reason.contains("Solver returned unknown")
                        && expected_fragments
                            .iter()
                            .all(|fragment| reason.contains(fragment)),
                    "{case} ({upstream_case}) should fail closed before solver Unknown and mention all of {expected_fragments:?}, got: {reason}"
                );
            }
            Ok(other) => {
                panic!("{case} ({upstream_case}) should fail closed until parity lands, got: {other:?}");
            }
        }
    }
}
