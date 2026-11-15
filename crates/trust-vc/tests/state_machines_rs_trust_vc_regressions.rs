// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Executable guards for the first upstream state_machines.rs TrustVc scout
//! slice.
//!
//! The port now exercises the NATIVE D1a `state_machine!` expansion
//! (`trust_vc_core::state_machine_dsl`): the upstream `relation_codegen` init
//! relation in both directions with its inductiveness lemma, the assert-free
//! `tr2` relation, the `lemma_doesnt_verify` families as counterexamples, and
//! the upstream diagnostic cases reported through a client function each. The
//! entry stays classified as an unsupported gap — the tokenized half,
//! `assert`/`match`/`property!`, labels, generics and collection/machine-int
//! fields are still refused.
//!
//! The LEMMA-CONJUNCTION rule is pinned here: a verified case that references
//! a machine counts only if every generated INIT/IND lemma of that machine is
//! itself a verified case. A lemma's ensures is ASSUMED at its call sites, so
//! a client of a machine that is not inductive verifies on its own; without
//! this rule the manifest could credit it.

mod common;

use std::{
    collections::{BTreeMap, BTreeSet},
    path::{Path, PathBuf},
};
use trust_vc_core::{verify_function_from_file, VerifyResult};

fn state_machines_port_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/ported/state_machines.rs")
}

fn verus_manifest_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/verus-tests.json")
}

fn pinned_upstream_state_machines_path() -> PathBuf {
    common::pinned_verus_test_path("state_machines.rs")
}

fn verify_case(path: &str, case: &str, upstream_case: &str) -> VerifyResult {
    verify_function_from_file(path, case)
        .unwrap_or_else(|err| panic!("{case} ({upstream_case}) should extract: {err}"))
}

fn expect_fail_closed(path: &str, case: &str, upstream_case: &str, expected_fragments: &[&str]) {
    let message = match verify_function_from_file(path, case) {
        Err(err) => err.to_string(),
        Ok(VerifyResult::Error { message }) => message,
        Ok(result) => {
            panic!("{case} ({upstream_case}) should fail closed with Error, got: {result:?}")
        }
    };

    for expected_fragment in expected_fragments {
        assert!(
            message.contains(expected_fragment),
            "{case} ({upstream_case}) error should contain {expected_fragment:?}, got: {message}"
        );
    }
}

const EXPECTED_CASE_METADATA: &[(&str, &str, &str, usize)] = &[
    (
        "state_machine_relation_codegen_tr1_verified",
        "relation_codegen",
        "verified",
        4,
    ),
    (
        "state_machine_init_branch_relation_verified",
        "relation_codegen",
        "verified",
        3,
    ),
    (
        "tokenized_bool_add_remove_surrogate_verified",
        "bool_codegen",
        "verified",
        4,
    ),
    (
        "state_machine_relation_wrong_post_counterexample",
        "relation_codegen",
        "counterexample",
        1,
    ),
    (
        "tokenized_bool_have_missing_counterexample",
        "bool_codegen",
        "counterexample",
        1,
    ),
    (
        "state_machine_macro_surface_currently_blocked",
        "state_machine! macro surface",
        "error",
        0,
    ),
    (
        "tokenized_state_machine_macro_surface_currently_blocked",
        "tokenized_state_machine! macro surface",
        "error",
        0,
    ),
    ("rc_init_inductive", "relation_codegen", "verified", 1),
    ("rc_correct_init", "relation_codegen", "verified", 1),
    ("rc_rev_init", "relation_codegen", "verified", 1),
    ("rc_tr2_inductive", "relation_codegen", "verified", 1),
    ("rc_correct_tr2_noassert", "relation_codegen", "verified", 1),
    ("rc_rev_tr2_noassert", "relation_codegen", "verified", 1),
    ("rc_rev_init_wrong", "relation_codegen", "counterexample", 1),
    (
        "ldv_tr_inductive",
        "lemma_doesnt_verify",
        "counterexample",
        1,
    ),
    (
        "ldv_init_inductive",
        "lemma_doesnt_verify_init",
        "counterexample",
        1,
    ),
    ("sm_dupe_name_fail_error", "dupe_name_fail", "error", 0),
    (
        "sm_birds_eye_nontokenized_error",
        "test_birds_eye_nontokenized_error",
        "error",
        0,
    ),
    (
        "sm_normal_sm_sharding_error",
        "normal_sm_sharding",
        "error",
        0,
    ),
    (
        "sm_init_wf_init_missing_error",
        "init_wf_init_missing",
        "error",
        0,
    ),
    (
        "sm_init_wf_init_dupe_error",
        "init_wf_init_dupe",
        "error",
        0,
    ),
    (
        "sm_init_wf_init_dupe_conditional_error",
        "init_wf_init_dupe_conditional",
        "error",
        0,
    ),
    ("sm_init_wf_init_if_error", "init_wf_init_if", "error", 0),
    (
        "sm_init_wf_init_else_error",
        "init_wf_init_else",
        "error",
        0,
    ),
    ("sm_init_wf_update_error", "init_wf_update", "error", 0),
    ("sm_init_wf_update2_error", "init_wf_update2", "error", 0),
    ("sm_init_wf_assert_error", "init_wf_assert", "error", 0),
    (
        "sm_normal_wf_update_dupe_error",
        "normal_wf_update_dupe",
        "error",
        0,
    ),
    (
        "sm_normal_wf_update_dupe_conditional_error",
        "normal_wf_update_dupe_conditional",
        "error",
        0,
    ),
    (
        "sm_normal_wf_update_dupe_conditional2_error",
        "normal_wf_update_dupe_conditional2",
        "error",
        0,
    ),
    (
        "sm_normal_wf_update_init_error",
        "normal_wf_update_init",
        "error",
        0,
    ),
    (
        "sm_readonly_wf_update_error",
        "readonly_wf_update",
        "error",
        0,
    ),
    (
        "sm_property_wf_update_error",
        "property_wf_update",
        "error",
        0,
    ),
    ("sm_readonly_wf_init_error", "readonly_wf_init", "error", 0),
    ("sm_property_wf_init_error", "property_wf_init", "error", 0),
    ("sm_field_not_found_error", "field_not_found", "error", 0),
    (
        "sm_no_let_repeated_idents_error",
        "no_let_repeated_idents",
        "error",
        0,
    ),
    (
        "sm_no_let_repeated_idents2_error",
        "no_let_repeated_idents2",
        "error",
        0,
    ),
    (
        "sm_no_let_repeated_idents3_error",
        "no_let_repeated_idents3",
        "error",
        0,
    ),
    ("sm_pre_in_init_error", "pre_in_init", "error", 0),
    (
        "sm_self_in_transition_error",
        "self_in_transition",
        "error",
        0,
    ),
    (
        "sm_post_in_transition_error",
        "post_in_transition",
        "error",
        0,
    ),
    ("sm_super_error", "super_error", "error", 0),
    (
        "sm_duplicate_inductive_lemma_error",
        "duplicate_inductive_lemma",
        "error",
        0,
    ),
    (
        "sm_missing_inductive_lemma_error",
        "missing_inductive_lemma",
        "error",
        0,
    ),
    (
        "sm_missing_inductive_lemma_init_error",
        "missing_inductive_lemma_init",
        "error",
        0,
    ),
    (
        "sm_inductive_lemma_readonly_error",
        "inductive_lemma_readonly",
        "error",
        0,
    ),
    (
        "sm_inductive_lemma_property_error",
        "inductive_lemma_property",
        "error",
        0,
    ),
    ("sm_lemma_wrong_args_error", "lemma_wrong_args", "error", 0),
    (
        "sm_lemma_bad_transition_name_error",
        "lemma_bad_transition_name",
        "error",
        0,
    ),
    (
        "sm_lemma_bad_generic_params_error",
        "lemma_bad_generic_params",
        "error",
        0,
    ),
    (
        "sm_lemma_bad_return_type_error",
        "lemma_bad_return_type",
        "error",
        0,
    ),
    ("sm_lemma_bad_header_error", "lemma_bad_header", "error", 0),
    (
        "sm_conflicting_attrs_error",
        "conflicting_attrs",
        "error",
        0,
    ),
    (
        "sm_explicit_mode_inv_error",
        "explicit_mode_inv",
        "error",
        0,
    ),
    (
        "sm_explicit_mode_field_error",
        "explicit_mode_field",
        "error",
        0,
    ),
    (
        "sm_explicit_mode_proof_error",
        "explicit_mode_proof",
        "error",
        0,
    ),
    ("sm_inv_wrong_params_error", "inv_wrong_params", "error", 0),
    ("sm_inv_wrong_ret_error", "inv_wrong_ret", "error", 0),
    (
        "sm_inv_wrong_generics_error",
        "inv_wrong_generics",
        "error",
        0,
    ),
    ("sm_multiple_fields_error", "multiple_fields", "error", 0),
    ("sm_no_fields_error", "no_fields", "error", 0),
    (
        "sm_field_name_reserved_ident1_error",
        "field_name_reserved_ident1",
        "error",
        0,
    ),
    (
        "sm_field_name_reserved_ident2_error",
        "field_name_reserved_ident2",
        "error",
        0,
    ),
    (
        "sm_let_name_reserved_ident1_error",
        "let_name_reserved_ident1",
        "error",
        0,
    ),
    (
        "sm_let_name_reserved_ident2_error",
        "let_name_reserved_ident2",
        "error",
        0,
    ),
    (
        "sm_arg_reserved_ident1_error",
        "arg_reserved_ident1",
        "error",
        0,
    ),
    (
        "sm_arg_reserved_ident2_error",
        "arg_reserved_ident2",
        "error",
        0,
    ),
    (
        "sm_sm_name_reserved_ident1_error",
        "sm_name_reserved_ident1",
        "error",
        0,
    ),
    (
        "sm_sm_name_reserved_ident2_error",
        "sm_name_reserved_ident2",
        "error",
        0,
    ),
];

const VERIFIED_CASES: &[(&str, &str)] = &[
    (
        "state_machine_relation_codegen_tr1_verified",
        "relation_codegen",
    ),
    (
        "state_machine_init_branch_relation_verified",
        "relation_codegen",
    ),
    (
        "tokenized_bool_add_remove_surrogate_verified",
        "bool_codegen",
    ),
    ("rc_init_inductive", "relation_codegen"),
    ("rc_correct_init", "relation_codegen"),
    ("rc_rev_init", "relation_codegen"),
    ("rc_tr2_inductive", "relation_codegen"),
    ("rc_correct_tr2_noassert", "relation_codegen"),
    ("rc_rev_tr2_noassert", "relation_codegen"),
];

const COUNTEREXAMPLE_CASES: &[(&str, &str)] = &[
    (
        "state_machine_relation_wrong_post_counterexample",
        "relation_codegen",
    ),
    ("tokenized_bool_have_missing_counterexample", "bool_codegen"),
    ("rc_rev_init_wrong", "relation_codegen"),
    ("ldv_tr_inductive", "lemma_doesnt_verify"),
    ("ldv_init_inductive", "lemma_doesnt_verify_init"),
];

const FAIL_CLOSED_CASES: &[(&str, &str, &[&str])] = &[
    (
        "state_machine_macro_surface_currently_blocked",
        "state_machine! macro surface",
        &["unsupported macro", "state_machine"],
    ),
    (
        "tokenized_state_machine_macro_surface_currently_blocked",
        "tokenized_state_machine! macro surface",
        &["unsupported macro", "tokenized_state_machine"],
    ),
    (
        "sm_dupe_name_fail_error",
        "dupe_name_fail",
        &["state_machine!", "duplicate item name"],
    ),
    (
        "sm_birds_eye_nontokenized_error",
        "test_birds_eye_nontokenized_error",
        &[
            "state_machine!",
            "`birds_eye` only makes sense for tokenized state machines",
        ],
    ),
    (
        "sm_normal_sm_sharding_error",
        "normal_sm_sharding",
        &[
            "state_machine!",
            "sharding strategy only makes sense for tokenized state machines",
        ],
    ),
    (
        "sm_init_wf_init_missing_error",
        "init_wf_init_missing",
        &["state_machine!", "procedure does not initialize"],
    ),
    (
        "sm_init_wf_init_dupe_error",
        "init_wf_init_dupe",
        &["state_machine!", "might be initialized multiple times"],
    ),
    (
        "sm_init_wf_init_dupe_conditional_error",
        "init_wf_init_dupe_conditional",
        &["state_machine!", "might be initialized multiple times"],
    ),
    (
        "sm_init_wf_init_if_error",
        "init_wf_init_if",
        &["state_machine!", "the else-branch does not initialize"],
    ),
    (
        "sm_init_wf_init_else_error",
        "init_wf_init_else",
        &["state_machine!", "the if-branch does not initialize"],
    ),
    (
        "sm_init_wf_update_error",
        "init_wf_update",
        &[
            "state_machine!",
            "'update' statement not allowed in initialization",
        ],
    ),
    (
        "sm_init_wf_update2_error",
        "init_wf_update2",
        &[
            "state_machine!",
            "'update' statement not allowed in initialization",
        ],
    ),
    (
        "sm_init_wf_assert_error",
        "init_wf_assert",
        &[
            "state_machine!",
            "'assert' statement not allowed in initialization",
        ],
    ),
    (
        "sm_normal_wf_update_dupe_error",
        "normal_wf_update_dupe",
        &["state_machine!", "might be updated multiple times"],
    ),
    (
        "sm_normal_wf_update_dupe_conditional_error",
        "normal_wf_update_dupe_conditional",
        &["state_machine!", "might be updated multiple times"],
    ),
    (
        "sm_normal_wf_update_dupe_conditional2_error",
        "normal_wf_update_dupe_conditional2",
        &["state_machine!", "might be updated multiple times"],
    ),
    (
        "sm_normal_wf_update_init_error",
        "normal_wf_update_init",
        &["state_machine!", "'init' statement not allowed"],
    ),
    (
        "sm_readonly_wf_update_error",
        "readonly_wf_update",
        &[
            "state_machine!",
            "statement not allowed in readonly transition",
        ],
    ),
    (
        "sm_property_wf_update_error",
        "property_wf_update",
        &[
            "state_machine!",
            "statement not allowed in property definition",
        ],
    ),
    (
        "sm_readonly_wf_init_error",
        "readonly_wf_init",
        &[
            "state_machine!",
            "statement not allowed outside 'init' routine",
        ],
    ),
    (
        "sm_property_wf_init_error",
        "property_wf_init",
        &[
            "state_machine!",
            "statement not allowed outside 'init' routine",
        ],
    ),
    (
        "sm_field_not_found_error",
        "field_not_found",
        &["state_machine!", "field 'whats_this' not found"],
    ),
    (
        "sm_no_let_repeated_idents_error",
        "no_let_repeated_idents",
        &["state_machine!", "bound variables with the same name"],
    ),
    (
        "sm_no_let_repeated_idents2_error",
        "no_let_repeated_idents2",
        &["state_machine!", "bound variables with the same name"],
    ),
    (
        "sm_no_let_repeated_idents3_error",
        "no_let_repeated_idents3",
        &["state_machine!", "bound variables with the same name"],
    ),
    (
        "sm_pre_in_init_error",
        "pre_in_init",
        &["state_machine!", "no previous state to refer to"],
    ),
    (
        "sm_self_in_transition_error",
        "self_in_transition",
        &["state_machine!", "`self` is meaningless"],
    ),
    (
        "sm_post_in_transition_error",
        "post_in_transition",
        &["state_machine!", "cannot refer directly to `post`"],
    ),
    (
        "sm_super_error",
        "super_error",
        &["state_machine!", "`super::` path not allowed here"],
    ),
    (
        "sm_duplicate_inductive_lemma_error",
        "duplicate_inductive_lemma",
        &["state_machine!", "duplicate 'inductive' lemma"],
    ),
    (
        "sm_missing_inductive_lemma_error",
        "missing_inductive_lemma",
        &["state_machine!", "missing inductiveness proofs for"],
    ),
    (
        "sm_missing_inductive_lemma_init_error",
        "missing_inductive_lemma_init",
        &["state_machine!", "missing inductiveness proofs for"],
    ),
    (
        "sm_inductive_lemma_readonly_error",
        "inductive_lemma_readonly",
        &[
            "state_machine!",
            "does not make sense for a 'readonly' transition",
        ],
    ),
    (
        "sm_inductive_lemma_property_error",
        "inductive_lemma_property",
        &[
            "state_machine!",
            "does not make sense for a 'property' definition",
        ],
    ),
    (
        "sm_lemma_wrong_args_error",
        "lemma_wrong_args",
        &["state_machine!", "params for 'inductive' lemma should be"],
    ),
    (
        "sm_lemma_bad_transition_name_error",
        "lemma_bad_transition_name",
        &["state_machine!", "could not find transition"],
    ),
    (
        "sm_lemma_bad_generic_params_error",
        "lemma_bad_generic_params",
        &["state_machine!", "should have no generic parameters"],
    ),
    (
        "sm_lemma_bad_return_type_error",
        "lemma_bad_return_type",
        &["state_machine!", "should have no return type"],
    ),
    (
        "sm_lemma_bad_header_error",
        "lemma_bad_header",
        &[
            "state_machine!",
            "the precondition and postcondition are implicit",
        ],
    ),
    (
        "sm_conflicting_attrs_error",
        "conflicting_attrs",
        &["state_machine!", "conflicting attributes"],
    ),
    (
        "sm_explicit_mode_inv_error",
        "explicit_mode_inv",
        &["state_machine!", "should not be explicitly labelled"],
    ),
    (
        "sm_explicit_mode_field_error",
        "explicit_mode_field",
        &["state_machine!", "should not be explicitly labelled"],
    ),
    (
        "sm_explicit_mode_proof_error",
        "explicit_mode_proof",
        &["state_machine!", "should not be explicitly labelled"],
    ),
    (
        "sm_inv_wrong_params_error",
        "inv_wrong_params",
        &[
            "state_machine!",
            "an invariant function must take 1 argument (self)",
        ],
    ),
    (
        "sm_inv_wrong_ret_error",
        "inv_wrong_ret",
        &["state_machine!", "an invariant function must return a bool"],
    ),
    (
        "sm_inv_wrong_generics_error",
        "inv_wrong_generics",
        &[
            "state_machine!",
            "an invariant function must take 0 type arguments",
        ],
    ),
    (
        "sm_multiple_fields_error",
        "multiple_fields",
        &[
            "state_machine!",
            "Expected only one declaration of `fields` block",
        ],
    ),
    (
        "sm_no_fields_error",
        "no_fields",
        &["state_machine!", "'fields' declaration was not found"],
    ),
    (
        "sm_field_name_reserved_ident1_error",
        "field_name_reserved_ident1",
        &["state_machine!", "reserved identifier"],
    ),
    (
        "sm_field_name_reserved_ident2_error",
        "field_name_reserved_ident2",
        &["state_machine!", "reserved identifier"],
    ),
    (
        "sm_let_name_reserved_ident1_error",
        "let_name_reserved_ident1",
        &["state_machine!", "reserved identifier"],
    ),
    (
        "sm_let_name_reserved_ident2_error",
        "let_name_reserved_ident2",
        &["state_machine!", "reserved identifier"],
    ),
    (
        "sm_arg_reserved_ident1_error",
        "arg_reserved_ident1",
        &["state_machine!", "reserved identifier"],
    ),
    (
        "sm_arg_reserved_ident2_error",
        "arg_reserved_ident2",
        &["state_machine!", "reserved identifier"],
    ),
    (
        "sm_sm_name_reserved_ident1_error",
        "sm_name_reserved_ident1",
        &["state_machine!", "reserved identifier"],
    ),
    (
        "sm_sm_name_reserved_ident2_error",
        "sm_name_reserved_ident2",
        &["state_machine!", "reserved identifier"],
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
        .unwrap_or_else(|| panic!("state_machines port should define {const_name}"));

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
    let array = referenced_array_const(file, "STATE_MACHINES_RS_EXPECTED_ERROR_PATTERNS");
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
    let array = referenced_array_const(file, "STATE_MACHINES_RS_EXPECTED_CASES");
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
            "duplicate state_machines metadata for {case_id}"
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

fn expected_error_pattern_entries() -> BTreeMap<String, Vec<String>> {
    FAIL_CLOSED_CASES
        .iter()
        .map(|&(case, _, patterns)| {
            (
                case.to_string(),
                patterns
                    .iter()
                    .map(|pattern| (*pattern).to_string())
                    .collect(),
            )
        })
        .collect()
}

fn expected_metadata_from_tests() -> Vec<CaseMetadata> {
    let mut patterns_by_case = expected_error_pattern_entries();

    EXPECTED_CASE_METADATA
        .iter()
        .map(
            |(case_id, upstream_case_id, expected_verdict, min_obligations)| CaseMetadata {
                case_id: (*case_id).to_string(),
                upstream_case_id: (*upstream_case_id).to_string(),
                expected_verdict: (*expected_verdict).to_string(),
                min_obligations: *min_obligations,
                expected_error_patterns: patterns_by_case.remove(*case_id).unwrap_or_default(),
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
                == Some("source/rust_verify_test/tests/state_machines.rs")
        })
        .expect("Verus manifest should contain state_machines.rs row");

    row["expected_cases"]
        .as_array()
        .expect("state_machines.rs row should contain expected_cases")
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

#[test]
fn state_machines_rs_port_file_is_rust_syntax() {
    let source = std::fs::read_to_string(state_machines_port_path())
        .expect("state_machines port should be readable");
    syn::parse_file(&source).expect("state_machines port should parse as ordinary Rust syntax");
}

#[test]
fn state_machines_rs_pinned_upstream_case_shapes_are_present() {
    let path = pinned_upstream_state_machines_path();
    if !path.exists() {
        eprintln!(
            "skipping pinned upstream state_machines.rs shape check; missing {}",
            path.display()
        );
        return;
    }

    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", path.display()));
    for expected in [
        "dupe_name_fail",
        "test_birds_eye_init_error",
        "relation_codegen",
        "relation_codegen_special",
        "nondet_tokenizing",
        "test_let_pattern",
        "bool_codegen",
        "persistent_bool_codegen",
        // The upstream cases this port now carries, by upstream id.
        "test_birds_eye_nontokenized_error",
        "normal_sm_sharding",
        "init_wf_init_missing",
        "init_wf_init_dupe",
        "init_wf_init_dupe_conditional",
        "init_wf_init_if",
        "init_wf_init_else",
        "init_wf_update",
        "init_wf_update2",
        "init_wf_assert",
        "normal_wf_update_dupe",
        "normal_wf_update_dupe_conditional",
        "normal_wf_update_dupe_conditional2",
        "normal_wf_update_init",
        "readonly_wf_update",
        "property_wf_update",
        "readonly_wf_init",
        "property_wf_init",
        "field_not_found",
        "no_let_repeated_idents",
        "no_let_repeated_idents2",
        "no_let_repeated_idents3",
        "pre_in_init",
        "self_in_transition",
        "post_in_transition",
        "super_error",
        "duplicate_inductive_lemma",
        "missing_inductive_lemma",
        "missing_inductive_lemma_init",
        "inductive_lemma_readonly",
        "inductive_lemma_property",
        "lemma_wrong_args",
        "lemma_bad_transition_name",
        "lemma_bad_generic_params",
        "lemma_bad_return_type",
        "lemma_bad_header",
        "lemma_doesnt_verify",
        "lemma_doesnt_verify_init",
        "conflicting_attrs",
        "explicit_mode_inv",
        "explicit_mode_field",
        "explicit_mode_proof",
        "inv_wrong_params",
        "inv_wrong_ret",
        "inv_wrong_generics",
        "multiple_fields",
        "no_fields",
        "field_name_reserved_ident1",
        "field_name_reserved_ident2",
        "sm_name_reserved_ident1",
        "sm_name_reserved_ident2",
        "let_name_reserved_ident1",
        "let_name_reserved_ident2",
        "arg_reserved_ident1",
        "arg_reserved_ident2",
    ] {
        assert!(
            source.contains(expected),
            "pinned upstream state_machines.rs should still contain {expected}"
        );
    }
}

#[test]
fn state_machines_rs_expected_case_metadata_is_exact() {
    let source = std::fs::read_to_string(state_machines_port_path())
        .expect("state_machines port should be readable");
    let file =
        syn::parse_file(&source).expect("state_machines port should parse as ordinary Rust syntax");

    assert_eq!(
        metadata_entries(&file),
        expected_metadata_from_tests(),
        "state_machines port expected-case metadata should match the regression inventory"
    );
    assert_eq!(
        error_pattern_entries(&file),
        expected_error_pattern_entries(),
        "state_machines port error-pattern metadata should match fail-closed cases"
    );
    assert!(
        source.contains("state_machines_rs_expected_cases")
            && source.contains("state_machines_rs_expected_error_patterns"),
        "state_machines port should expose expected-case and error-pattern metadata accessors"
    );
}

#[test]
fn state_machines_rs_expected_case_metadata_matches_manifest() {
    let source = std::fs::read_to_string(state_machines_port_path())
        .expect("state_machines port should be readable");
    let file =
        syn::parse_file(&source).expect("state_machines port should parse as ordinary Rust syntax");

    assert_eq!(
        metadata_entries(&file),
        manifest_expected_metadata(),
        "state_machines manifest expected_cases should match port metadata exactly"
    );
}

#[test]
fn state_machines_rs_error_cases_have_expected_error_patterns() {
    let source = std::fs::read_to_string(state_machines_port_path())
        .expect("state_machines port should be readable");
    let file =
        syn::parse_file(&source).expect("state_machines port should parse as ordinary Rust syntax");
    let mut patterns_by_case = error_pattern_entries(&file);

    for expected_case in metadata_entries(&file) {
        if expected_case.expected_verdict == "error" {
            assert_eq!(
                expected_case.min_obligations, 0,
                "{} ({}) error evidence should not declare obligations",
                expected_case.case_id, expected_case.upstream_case_id
            );
            let expected_patterns = patterns_by_case
                .remove(&expected_case.case_id)
                .unwrap_or_else(|| {
                    panic!(
                        "{} ({}) should have expected_error_patterns metadata",
                        expected_case.case_id, expected_case.upstream_case_id
                    )
                });
            assert!(
                !expected_patterns.is_empty(),
                "{} ({}) expected_error_patterns should not be empty",
                expected_case.case_id,
                expected_case.upstream_case_id
            );
        } else {
            assert!(
                !patterns_by_case.contains_key(&expected_case.case_id),
                "{} ({}) non-error metadata should not declare expected_error_patterns",
                expected_case.case_id,
                expected_case.upstream_case_id
            );
        }
    }

    assert!(
        patterns_by_case.is_empty(),
        "expected_error_patterns should not contain orphan cases: {patterns_by_case:?}"
    );
}

#[test]
fn state_machines_rs_verified_subset_verifies_from_file() {
    let path = state_machines_port_path();
    let path = path
        .to_str()
        .expect("state_machines port path should be UTF-8");

    for (case, upstream_case) in VERIFIED_CASES {
        let result = verify_case(path, case, upstream_case);
        assert!(
            matches!(result, VerifyResult::Verified),
            "{case} ({upstream_case}) should verify, got: {result:?}"
        );
    }
}

#[test]
fn state_machines_rs_counterexample_subset_is_rejected_from_file() {
    let path = state_machines_port_path();
    let path = path
        .to_str()
        .expect("state_machines port path should be UTF-8");

    for (case, upstream_case) in COUNTEREXAMPLE_CASES {
        let result = verify_case(path, case, upstream_case);
        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "{case} ({upstream_case}) should produce a counterexample, got: {result:?}"
        );
    }
}

#[test]
fn state_machines_rs_macro_surfaces_fail_closed_from_file() {
    let path = state_machines_port_path();
    let path = path
        .to_str()
        .expect("state_machines port path should be UTF-8");

    for (case, upstream_case, expected_fragments) in FAIL_CLOSED_CASES {
        expect_fail_closed(path, case, upstream_case, expected_fragments);
    }
}

/// Every machine the port declares, with the lemmas D1a generates for it.
fn port_machine_lemmas() -> Vec<(String, String, &'static str)> {
    let source = std::fs::read_to_string(state_machines_port_path())
        .expect("state_machines port should be readable");
    let file =
        syn::parse_file(&source).expect("state_machines port should parse as ordinary Rust syntax");
    trust_vc_core::state_machine_dsl::machine_lemmas(&file)
}

/// The identifiers a case's body and contract mention.
fn case_idents(case: &str) -> BTreeSet<String> {
    fn walk(items: &[syn::Item], case: &str, out: &mut BTreeSet<String>) {
        for item in items {
            match item {
                syn::Item::Fn(func) if func.sig.ident == case => {
                    fn idents(tokens: proc_macro2::TokenStream, out: &mut BTreeSet<String>) {
                        for tree in tokens {
                            match tree {
                                proc_macro2::TokenTree::Ident(ident) => {
                                    out.insert(ident.to_string());
                                }
                                proc_macro2::TokenTree::Group(group) => idents(group.stream(), out),
                                _ => {}
                            }
                        }
                    }
                    idents(quote::ToTokens::to_token_stream(func), out);
                }
                syn::Item::Mod(module) => {
                    if let Some((_, inner)) = &module.content {
                        walk(inner, case, out);
                    }
                }
                _ => {}
            }
        }
    }
    let source = std::fs::read_to_string(state_machines_port_path())
        .expect("state_machines port should be readable");
    let file =
        syn::parse_file(&source).expect("state_machines port should parse as ordinary Rust syntax");
    let mut out = BTreeSet::new();
    walk(&file.items, case, &mut out);
    out
}

#[test]
fn state_machines_rs_every_generated_lemma_is_an_expected_case() {
    let lemmas = port_machine_lemmas();
    assert!(
        !lemmas.is_empty(),
        "the port should declare at least one admitted state machine"
    );
    let expected: BTreeSet<&str> = EXPECTED_CASE_METADATA
        .iter()
        .map(|(case, _, _, _)| *case)
        .collect();
    for (machine, lemma, kind) in &lemmas {
        assert!(
            matches!(*kind, "init" | "transition"),
            "unexpected lemma kind {kind}"
        );
        assert!(
            expected.contains(lemma.as_str()),
            "lemma {lemma} of machine {machine} is generated but is not an expected case"
        );
    }
}

/// A verified case counts for a machine only if EVERY generated lemma of that
/// machine verifies too.
#[test]
fn state_machines_rs_verified_cases_only_credit_inductive_machines() {
    let lemmas = port_machine_lemmas();
    let mut by_machine: BTreeMap<String, Vec<String>> = BTreeMap::new();
    for (machine, lemma, _) in &lemmas {
        by_machine
            .entry(machine.clone())
            .or_default()
            .push(lemma.clone());
    }
    let verified: BTreeSet<&str> = VERIFIED_CASES.iter().map(|(case, _)| *case).collect();
    let path = state_machines_port_path();
    let path = path
        .to_str()
        .expect("state_machines port path should be UTF-8");

    for (case, upstream_case) in VERIFIED_CASES {
        let idents = case_idents(case);
        for (machine, machine_lemmas) in &by_machine {
            if !idents.contains(machine) {
                continue;
            }
            for lemma in machine_lemmas {
                assert!(
                    verified.contains(lemma.as_str()),
                    "{case} ({upstream_case}) references machine {machine}, whose generated lemma \
                     {lemma} is not listed as verified"
                );
                let result = verify_case(path, lemma, upstream_case);
                assert!(
                    matches!(result, VerifyResult::Verified),
                    "{case} ({upstream_case}) references machine {machine}, whose generated lemma \
                     {lemma} does not verify: {result:?}"
                );
            }
        }
    }
}

/// The machine body each `error` case feeds the expander, keyed by case id.
///
/// The client of an error case is `fn <case>(s: <Machine>::State)`, so the
/// machine is read off the client's parameter type and the body is the token
/// stream of the file-root `trust_vc::state_machine! { <Machine> { .. } }`.
fn ported_error_machine_bodies() -> BTreeMap<String, String> {
    let source = std::fs::read_to_string(state_machines_port_path())
        .expect("state_machines port should be readable");
    let file =
        syn::parse_file(&source).expect("state_machines port should parse as ordinary Rust syntax");

    let mut machines: BTreeMap<String, String> = BTreeMap::new();
    for item in &file.items {
        let syn::Item::Macro(item_macro) = item else {
            continue;
        };
        if item_macro
            .mac
            .path
            .segments
            .last()
            .is_none_or(|segment| segment.ident != "state_machine")
        {
            continue;
        }
        let mut tokens = item_macro.mac.tokens.clone().into_iter();
        let Some(proc_macro2::TokenTree::Ident(name)) = tokens.next() else {
            continue;
        };
        let Some(proc_macro2::TokenTree::Group(body)) = tokens.next() else {
            continue;
        };
        machines.insert(name.to_string(), body.stream().to_string());
    }

    let mut by_case = BTreeMap::new();
    for (case, _, verdict, _) in EXPECTED_CASE_METADATA {
        if *verdict != "error" {
            continue;
        }
        let client = file
            .items
            .iter()
            .find_map(|item| match item {
                syn::Item::Fn(func) if func.sig.ident == case => Some(func),
                _ => None,
            })
            .unwrap_or_else(|| panic!("error case {case} should have a client fn in the port"));
        // The two scout-era macro-boundary cases take no machine parameter:
        // they pin STATEMENT-position refusals, which have no DSL input to
        // compare. Everything else is a `fn <case>(s: <Machine>::State)`.
        let Some(syn::FnArg::Typed(arg)) = client.sig.inputs.first() else {
            continue;
        };
        let syn::Type::Path(path) = arg.ty.as_ref() else {
            panic!("{case} should take a `<Machine>::State` parameter");
        };
        if path.path.segments.len() != 2 || path.path.segments[1].ident != "State" {
            continue;
        }
        let machine = path.path.segments[0].ident.to_string();
        let body = machines
            .get(&machine)
            .unwrap_or_else(|| {
                panic!("{case} names machine {machine}, which the port never declares")
            })
            .clone();
        by_case.insert((*case).to_string(), body);
    }
    by_case
}

/// Upstream's own macro input for one `#[test] <case>` block: the machine
/// body, with `#[sharding(..)]` removed (the one documented adaptation when a
/// tokenized machine is ported to the non-tokenized surface).
fn pinned_upstream_machine_body(source: &str, upstream_case: &str) -> String {
    let marker = format!("#[test] {upstream_case} ");
    let start = source
        .find(&marker)
        .unwrap_or_else(|| panic!("pinned upstream should carry #[test] {upstream_case}"));
    let rest = &source[start..];
    let (invocation, tokenized) = ["tokenized_state_machine!", "state_machine!"]
        .iter()
        .filter_map(|needle| {
            rest.find(needle)
                .map(|at| (at + needle.len(), needle.starts_with("tokenized")))
        })
        .min_by_key(|(at, _)| *at)
        .unwrap_or_else(|| panic!("{upstream_case} should invoke a state machine macro"));

    // Skip `{ <Name>` and take the machine body, braces balanced, without the
    // outer pair (the port side is a token group's stream, which has none).
    let rest = &rest[invocation..];
    let open = rest.find('{').expect("a macro invocation opens a brace");
    let after_name = rest[open + 1..]
        .find('{')
        .expect("a machine body opens a brace")
        + open
        + 1;
    let mut depth = 0usize;
    for (offset, ch) in rest[after_name..].char_indices() {
        match ch {
            '{' => depth += 1,
            '}' => {
                depth -= 1;
                if depth == 0 {
                    let body = &rest[after_name + 1..after_name + offset];
                    // `#[sharding(..)]` is dropped only where the adaptation
                    // drops it: porting a TOKENIZED machine. A non-tokenized
                    // upstream case keeps it, because there it is the defect
                    // under test (`normal_sm_sharding`).
                    return if tokenized {
                        strip_sharding(body)
                    } else {
                        body.to_string()
                    };
                }
            }
            _ => {}
        }
    }
    panic!("{upstream_case} machine body is unbalanced");
}

/// Drop `#[sharding(..)]` attributes — the single token-level difference the
/// tokenized -> non-tokenized adaptation is allowed to make.
fn strip_sharding(body: &str) -> String {
    let mut out = String::new();
    let mut rest = body;
    while let Some(at) = rest.find("#[sharding") {
        out.push_str(&rest[..at]);
        let close = rest[at..].find(")]").expect("a sharding attribute closes") + at + 2;
        rest = &rest[close..];
    }
    out.push_str(rest);
    out
}

/// A machine body reduced to its TOKENS, so comments and layout cannot hide a
/// difference and cannot cause a spurious one.
fn normalized_machine_input(body: &str) -> String {
    body.parse::<proc_macro2::TokenStream>()
        .unwrap_or_else(|err| panic!("machine body should tokenize: {err}\n{body}"))
        .to_string()
}

/// Every ported diagnostic machine is upstream's OWN input, not a reduction of
/// it.
///
/// A reduced input can keep the expected message while silently dropping the
/// check-ORDER evidence the case exists to record — upstream's
/// `inv_wrong_params` carries an `init!` and an explicitly moded
/// `#[inductive]` lemma, and reports the INVARIANT error in spite of both. The
/// only differences this admits are the documented adaptation (tokenized ->
/// `state_machine!`, `#[sharding(..)]` dropped), comments and whitespace.
#[test]
fn state_machines_rs_ported_error_machines_are_upstreams_own_input() {
    let path = pinned_upstream_state_machines_path();
    if !path.exists() {
        eprintln!(
            "skipping pinned upstream state_machines.rs input check; missing {}",
            path.display()
        );
        return;
    }
    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", path.display()));

    let ported = ported_error_machine_bodies();
    // Every error case EXCEPT the two scout-era statement-position boundaries,
    // which refuse a macro call rather than a machine.
    assert_eq!(
        ported.len(),
        EXPECTED_CASE_METADATA
            .iter()
            .filter(|(_, _, verdict, _)| *verdict == "error")
            .count()
            - 2,
        "every machine-bearing error case should contribute a machine body"
    );

    for (case, upstream_case, verdict, _) in EXPECTED_CASE_METADATA {
        if *verdict != "error" {
            continue;
        }
        let Some(ported_body) = ported.get(*case) else {
            continue;
        };
        let upstream_body = pinned_upstream_machine_body(&source, upstream_case);
        assert_eq!(
            normalized_machine_input(ported_body),
            normalized_machine_input(&upstream_body),
            "{case} should feed upstream's own {upstream_case} input to the expander"
        );
    }
}

/// The EXTRACTED obligation count of every non-error case, MEASURED
/// 2026-09-17 (`extract_verification_conditions_with_file_context`, the lens
/// used throughout this increment).
///
/// This is a DIFFERENT quantity from the manifest's `min_obligations` — see
/// the two tests below — and it is the one that is load-bearing here: an
/// inductiveness lemma extracts its requires conjuncts plus its postcondition,
/// so a relation that silently lost a conjunct shows up as a smaller number.
const MEASURED_EXTRACTED_OBLIGATIONS: &[(&str, usize)] = &[
    // pre-existing scout cases
    ("state_machine_relation_codegen_tr1_verified", 8),
    ("state_machine_init_branch_relation_verified", 7),
    ("tokenized_bool_add_remove_surrogate_verified", 5),
    ("state_machine_relation_wrong_post_counterexample", 2),
    ("tokenized_bool_have_missing_counterexample", 2),
    // D1a cases
    ("rc_init_inductive", 7),
    ("rc_correct_init", 4),
    ("rc_rev_init", 4),
    ("rc_tr2_inductive", 7),
    ("rc_correct_tr2_noassert", 4),
    ("rc_rev_tr2_noassert", 4),
    ("rc_rev_init_wrong", 4),
    ("ldv_tr_inductive", 7),
    ("ldv_init_inductive", 7),
];

/// The manifest's `min_obligations` is the CAPTURED-obligation floor, not the
/// extracted count.
///
/// MEASURED 2026-09-17 through the evidence lane's own artifact (`cargo
/// trust-vc check --emit-certificate` over this port): the evidence gate
/// compares `min_obligations` against `observed_case.obligation_count`
/// (`cargo-trust-vc/src/evidence.rs:6396`), which is built from the
/// obligations a certificate CAPTURES — status `verified` / `counterexample` /
/// `unknown` / `error`, i.e. everything except `assumed`, `skipped` and
/// `uncaptured` (`evidence.rs:9259-9277`, `verify.rs:129-136`). For every D1a
/// case that is exactly 1: the generated lemma's requires conjuncts are
/// ASSUMED and only the postcondition is checked. Declaring the extracted
/// count (7 or 4) there would have been a floor the lane can never meet, and
/// it would have failed the moment this entry was promoted out of
/// `unsupported-gap`. The extracted floor lives in
/// `MEASURED_EXTRACTED_OBLIGATIONS` instead, asserted by the test below, and
/// `crates/cargo-trust-vc/tests/state_machine_check_cli.rs` pins the captured
/// side against a real certificate.
#[test]
fn state_machines_rs_non_error_cases_meet_their_measured_obligation_floor() {
    let source = std::fs::read_to_string(state_machines_port_path())
        .expect("state_machines port should be readable");
    let file = trust_vc_core::parse_file_allow_tracked(&source)
        .expect("state_machines port should parse through the shared entry");

    let measured: BTreeMap<&str, usize> = MEASURED_EXTRACTED_OBLIGATIONS
        .iter()
        .copied()
        .collect::<BTreeMap<_, _>>();
    let non_error: BTreeSet<&str> = EXPECTED_CASE_METADATA
        .iter()
        .filter(|(_, _, verdict, _)| *verdict != "error")
        .map(|(case, _, _, _)| *case)
        .collect();
    assert_eq!(
        measured.keys().copied().collect::<BTreeSet<_>>(),
        non_error,
        "every non-error case needs a measured extracted-obligation floor"
    );

    for (case, upstream_case, verdict, min_obligations) in EXPECTED_CASE_METADATA {
        if *verdict == "error" {
            continue;
        }
        let func = file
            .items
            .iter()
            .find_map(|item| match item {
                syn::Item::Fn(func) if func.sig.ident == case => Some(func),
                _ => None,
            })
            .unwrap_or_else(|| panic!("{case} ({upstream_case}) should exist in the port"));
        let vc = trust_vc_core::extract_verification_conditions_with_file_context(&file, func)
            .unwrap_or_else(|err| panic!("{case} ({upstream_case}) should extract VCs: {err}"));
        let obligations = vc.obligations().len();
        let extracted_floor = measured[*case];
        assert_eq!(
            obligations, extracted_floor,
            "{case} ({upstream_case}) extracted-obligation count moved: expected {extracted_floor}, got {obligations}"
        );
        assert!(
            obligations >= *min_obligations,
            "{case} ({upstream_case}) declares a manifest floor of {min_obligations} it cannot even extract ({obligations})"
        );
    }
}

/// `expand_file` is an EXACT no-op on every corpus file that declares no
/// item-position `state_machine!`.
///
/// This is the structural half of the extraction A/B: the A/B measures
/// verdicts, this measures the AST, and together they say that the shared
/// parse entry (`tracked_syntax::parse_file_allow_tracked`) cannot move a
/// corpus file that does not opt in. MEASURED 2026-09-17: only
/// `state_machines.rs` changes.
#[test]
fn expand_file_is_a_no_op_on_every_other_ported_corpus_file() {
    let ported_dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/ported");
    let mut checked = 0usize;
    let mut skipped_unparsable = Vec::new();
    let mut moved = Vec::new();
    let mut entries: Vec<PathBuf> = std::fs::read_dir(&ported_dir)
        .expect("ported corpus directory should be readable")
        .filter_map(|entry| entry.ok().map(|entry| entry.path()))
        .filter(|path| path.extension().is_some_and(|ext| ext == "rs"))
        .collect();
    entries.sort();
    assert!(
        entries.len() > 100,
        "the ported corpus should be the whole corpus, found {}",
        entries.len()
    );

    for path in entries {
        let name = path
            .file_name()
            .and_then(|name| name.to_str())
            .unwrap_or_default()
            .to_string();
        let source = std::fs::read_to_string(&path).expect("ported file should be readable");
        // Plain `syn` is the right lens here: a file it cannot parse never
        // reaches `expand_file` as an unexpanded AST either.
        let Ok(mut file) = syn::parse_file(&source) else {
            skipped_unparsable.push(name);
            continue;
        };
        let before = quote::ToTokens::to_token_stream(&file).to_string();
        trust_vc_core::state_machine_dsl::expand_file(&mut file);
        let after = quote::ToTokens::to_token_stream(&file).to_string();
        if before != after {
            moved.push(name);
        }
        checked += 1;
    }

    assert_eq!(
        moved,
        vec!["state_machines.rs".to_string()],
        "only the file that invokes trust_vc::state_machine! may be rewritten"
    );
    assert!(
        checked > 100,
        "the no-op claim should cover the corpus, checked {checked} files (skipped: {skipped_unparsable:?})"
    );
}
