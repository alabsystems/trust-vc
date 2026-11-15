// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Executable TrustVc port of upstream Verus
// `source/rust_verify_test/tests/state_machines.rs`.
//
// The upstream file is a macro and diagnostic suite for Verus `state_machine!`
// and `tokenized_state_machine!`. TrustVc now EXPANDS the non-tokenized
// `state_machine!` surface natively (D1a, `trust_vc_core::state_machine_dsl`):
// an item-position `trust_vc::state_machine!` with int/bool/file-local-datatype
// fields becomes definitional relations plus `#[trust_vc::proof]` inductiveness
// lemmas, checked by the ordinary proof pipeline on ay.
//
// What this port records:
// - the upstream `relation_codegen` init relation, proven equivalent in BOTH
//   directions against an explicitly written relation, plus its inductiveness
//   lemma (`rc_*`);
// - the same for `tr2` with its `assert` removed (adapted: `assert` is refused
//   in D1a, see the manifest's known_gaps);
// - the upstream `lemma_doesnt_verify` / `lemma_doesnt_verify_init` families,
//   adapted from tokenized to non-tokenized, as counterexamples;
// - the upstream diagnostic cases that are natively non-tokenized, each
//   reported through a client function that mentions the refused machine, plus
//   the tokenized diagnostic cases whose well-formedness rule is identical
//   after dropping `#[sharding(..)]` (adapted);
// - the scalar/boolean surrogates and the statement-position macro boundaries
//   the first scout recorded, unchanged.
//
// The entry stays `unsupported-gap`: the tokenized half, `assert`/`match`/
// `property!`, labels, generics, collection and machine-int fields, `Step`,
// `show::` and the generated token APIs are all still out of scope.

#![allow(dead_code, unused_macros)]

use trust_vc_types::int;

macro_rules! state_machine {
    ($($tokens:tt)*) => {
        ()
    };
}

macro_rules! tokenized_state_machine {
    ($($tokens:tt)*) => {
        ()
    };
}

#[derive(Clone, Copy, PartialEq, Eq)]
struct ScalarState {
    x: u64,
    y: u64,
    z: u64,
}

// (case_id, upstream_case_id, expected_verdict, min_obligations).
//
// `min_obligations` is the manifest's quantity: the number of obligations a
// proof CERTIFICATE captures (status verified/counterexample/unknown/error —
// never `assumed`), which is what the evidence gate compares against
// (cargo-trust-vc/src/evidence.rs:6396, :9259-9277). It is NOT
// `vc.obligations().len()`: a generated D1a inductiveness lemma extracts 7
// obligations and CHECKS exactly 1, because its requires conjuncts are
// assumed. MEASURED 2026-09-17 with `cargo trust-vc check --emit-certificate`
// over this file; the extracted counts are pinned separately in
// crates/trust-vc/tests/state_machines_rs_trust_vc_regressions.rs
// (`MEASURED_EXTRACTED_OBLIGATIONS`).
pub const STATE_MACHINES_RS_EXPECTED_CASES: &[(&str, &str, &str, usize)] = &[
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
    (
        "rc_init_inductive",
        "relation_codegen",
        "verified",
        1,
    ),
    (
        "rc_correct_init",
        "relation_codegen",
        "verified",
        1,
    ),
    (
        "rc_rev_init",
        "relation_codegen",
        "verified",
        1,
    ),
    (
        "rc_tr2_inductive",
        "relation_codegen",
        "verified",
        1,
    ),
    (
        "rc_correct_tr2_noassert",
        "relation_codegen",
        "verified",
        1,
    ),
    (
        "rc_rev_tr2_noassert",
        "relation_codegen",
        "verified",
        1,
    ),
    (
        "rc_rev_init_wrong",
        "relation_codegen",
        "counterexample",
        1,
    ),
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
    (
        "sm_dupe_name_fail_error",
        "dupe_name_fail",
        "error",
        0,
    ),
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
    (
        "sm_init_wf_init_if_error",
        "init_wf_init_if",
        "error",
        0,
    ),
    (
        "sm_init_wf_init_else_error",
        "init_wf_init_else",
        "error",
        0,
    ),
    (
        "sm_init_wf_update_error",
        "init_wf_update",
        "error",
        0,
    ),
    (
        "sm_init_wf_update2_error",
        "init_wf_update2",
        "error",
        0,
    ),
    (
        "sm_init_wf_assert_error",
        "init_wf_assert",
        "error",
        0,
    ),
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
    (
        "sm_readonly_wf_init_error",
        "readonly_wf_init",
        "error",
        0,
    ),
    (
        "sm_property_wf_init_error",
        "property_wf_init",
        "error",
        0,
    ),
    (
        "sm_field_not_found_error",
        "field_not_found",
        "error",
        0,
    ),
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
    (
        "sm_pre_in_init_error",
        "pre_in_init",
        "error",
        0,
    ),
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
    (
        "sm_super_error",
        "super_error",
        "error",
        0,
    ),
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
    (
        "sm_lemma_wrong_args_error",
        "lemma_wrong_args",
        "error",
        0,
    ),
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
    (
        "sm_lemma_bad_header_error",
        "lemma_bad_header",
        "error",
        0,
    ),
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
    (
        "sm_inv_wrong_params_error",
        "inv_wrong_params",
        "error",
        0,
    ),
    (
        "sm_inv_wrong_ret_error",
        "inv_wrong_ret",
        "error",
        0,
    ),
    (
        "sm_inv_wrong_generics_error",
        "inv_wrong_generics",
        "error",
        0,
    ),
    (
        "sm_multiple_fields_error",
        "multiple_fields",
        "error",
        0,
    ),
    (
        "sm_no_fields_error",
        "no_fields",
        "error",
        0,
    ),
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

pub const STATE_MACHINES_RS_EXPECTED_ERROR_PATTERNS: &[(&str, &[&str])] = &[
    (
        "state_machine_macro_surface_currently_blocked",
        &["unsupported macro", "state_machine"],
    ),
    (
        "tokenized_state_machine_macro_surface_currently_blocked",
        &["unsupported macro", "tokenized_state_machine"],
    ),
    (
        "sm_dupe_name_fail_error",
        &["state_machine!", "duplicate item name"],
    ),
    (
        "sm_birds_eye_nontokenized_error",
        &["state_machine!", "`birds_eye` only makes sense for tokenized state machines"],
    ),
    (
        "sm_normal_sm_sharding_error",
        &["state_machine!", "sharding strategy only makes sense for tokenized state machines"],
    ),
    (
        "sm_init_wf_init_missing_error",
        &["state_machine!", "procedure does not initialize"],
    ),
    (
        "sm_init_wf_init_dupe_error",
        &["state_machine!", "might be initialized multiple times"],
    ),
    (
        "sm_init_wf_init_dupe_conditional_error",
        &["state_machine!", "might be initialized multiple times"],
    ),
    (
        "sm_init_wf_init_if_error",
        &["state_machine!", "the else-branch does not initialize"],
    ),
    (
        "sm_init_wf_init_else_error",
        &["state_machine!", "the if-branch does not initialize"],
    ),
    (
        "sm_init_wf_update_error",
        &["state_machine!", "'update' statement not allowed in initialization"],
    ),
    (
        "sm_init_wf_update2_error",
        &["state_machine!", "'update' statement not allowed in initialization"],
    ),
    (
        "sm_init_wf_assert_error",
        &["state_machine!", "'assert' statement not allowed in initialization"],
    ),
    (
        "sm_normal_wf_update_dupe_error",
        &["state_machine!", "might be updated multiple times"],
    ),
    (
        "sm_normal_wf_update_dupe_conditional_error",
        &["state_machine!", "might be updated multiple times"],
    ),
    (
        "sm_normal_wf_update_dupe_conditional2_error",
        &["state_machine!", "might be updated multiple times"],
    ),
    (
        "sm_normal_wf_update_init_error",
        &["state_machine!", "'init' statement not allowed"],
    ),
    (
        "sm_readonly_wf_update_error",
        &["state_machine!", "statement not allowed in readonly transition"],
    ),
    (
        "sm_property_wf_update_error",
        &["state_machine!", "statement not allowed in property definition"],
    ),
    (
        "sm_readonly_wf_init_error",
        &["state_machine!", "statement not allowed outside 'init' routine"],
    ),
    (
        "sm_property_wf_init_error",
        &["state_machine!", "statement not allowed outside 'init' routine"],
    ),
    (
        "sm_field_not_found_error",
        &["state_machine!", "field 'whats_this' not found"],
    ),
    (
        "sm_no_let_repeated_idents_error",
        &["state_machine!", "bound variables with the same name"],
    ),
    (
        "sm_no_let_repeated_idents2_error",
        &["state_machine!", "bound variables with the same name"],
    ),
    (
        "sm_no_let_repeated_idents3_error",
        &["state_machine!", "bound variables with the same name"],
    ),
    (
        "sm_pre_in_init_error",
        &["state_machine!", "no previous state to refer to"],
    ),
    (
        "sm_self_in_transition_error",
        &["state_machine!", "`self` is meaningless"],
    ),
    (
        "sm_post_in_transition_error",
        &["state_machine!", "cannot refer directly to `post`"],
    ),
    (
        "sm_super_error",
        &["state_machine!", "`super::` path not allowed here"],
    ),
    (
        "sm_duplicate_inductive_lemma_error",
        &["state_machine!", "duplicate 'inductive' lemma"],
    ),
    (
        "sm_missing_inductive_lemma_error",
        &["state_machine!", "missing inductiveness proofs for"],
    ),
    (
        "sm_missing_inductive_lemma_init_error",
        &["state_machine!", "missing inductiveness proofs for"],
    ),
    (
        "sm_inductive_lemma_readonly_error",
        &["state_machine!", "does not make sense for a 'readonly' transition"],
    ),
    (
        "sm_inductive_lemma_property_error",
        &["state_machine!", "does not make sense for a 'property' definition"],
    ),
    (
        "sm_lemma_wrong_args_error",
        &["state_machine!", "params for 'inductive' lemma should be"],
    ),
    (
        "sm_lemma_bad_transition_name_error",
        &["state_machine!", "could not find transition"],
    ),
    (
        "sm_lemma_bad_generic_params_error",
        &["state_machine!", "should have no generic parameters"],
    ),
    (
        "sm_lemma_bad_return_type_error",
        &["state_machine!", "should have no return type"],
    ),
    (
        "sm_lemma_bad_header_error",
        &["state_machine!", "the precondition and postcondition are implicit"],
    ),
    (
        "sm_conflicting_attrs_error",
        &["state_machine!", "conflicting attributes"],
    ),
    (
        "sm_explicit_mode_inv_error",
        &["state_machine!", "should not be explicitly labelled"],
    ),
    (
        "sm_explicit_mode_field_error",
        &["state_machine!", "should not be explicitly labelled"],
    ),
    (
        "sm_explicit_mode_proof_error",
        &["state_machine!", "should not be explicitly labelled"],
    ),
    (
        "sm_inv_wrong_params_error",
        &["state_machine!", "an invariant function must take 1 argument (self)"],
    ),
    (
        "sm_inv_wrong_ret_error",
        &["state_machine!", "an invariant function must return a bool"],
    ),
    (
        "sm_inv_wrong_generics_error",
        &["state_machine!", "an invariant function must take 0 type arguments"],
    ),
    (
        "sm_multiple_fields_error",
        &["state_machine!", "Expected only one declaration of `fields` block"],
    ),
    (
        "sm_no_fields_error",
        &["state_machine!", "'fields' declaration was not found"],
    ),
    (
        "sm_field_name_reserved_ident1_error",
        &["state_machine!", "reserved identifier"],
    ),
    (
        "sm_field_name_reserved_ident2_error",
        &["state_machine!", "reserved identifier"],
    ),
    (
        "sm_let_name_reserved_ident1_error",
        &["state_machine!", "reserved identifier"],
    ),
    (
        "sm_let_name_reserved_ident2_error",
        &["state_machine!", "reserved identifier"],
    ),
    (
        "sm_arg_reserved_ident1_error",
        &["state_machine!", "reserved identifier"],
    ),
    (
        "sm_arg_reserved_ident2_error",
        &["state_machine!", "reserved identifier"],
    ),
    (
        "sm_sm_name_reserved_ident1_error",
        &["state_machine!", "reserved identifier"],
    ),
    (
        "sm_sm_name_reserved_ident2_error",
        &["state_machine!", "reserved identifier"],
    ),
];

pub fn state_machines_rs_expected_cases(
) -> &'static [(&'static str, &'static str, &'static str, usize)] {
    STATE_MACHINES_RS_EXPECTED_CASES
}

pub fn state_machines_rs_expected_error_patterns(
) -> &'static [(&'static str, &'static [&'static str])] {
    STATE_MACHINES_RS_EXPECTED_ERROR_PATTERNS
}


// ---------------------------------------------------------------------------
// upstream `relation_codegen`: the `initialize` relation, verbatim.

trust_vc::state_machine! { RcInit {
    fields {
        pub x: int,
        pub y: int,
        pub z: int,
    }

    init! {
        initialize(x: int, y: int, z: int) {
            init x = x;
            init y = y;
            require(y <= z);
            if x == y {
                init z = z;
            } else {
                init z = z + 1;
            }
        }
    }

    #[invariant]
    pub fn the_inv(self) -> bool {
        self.y <= self.z
    }

    #[inductive(initialize)]
    fn rc_init_inductive(post: Self, x: int, y: int, z: int) {}
} }

#[trust_vc::spec]
fn rc_rel_init(post: RcInit::State, x: int, y: int, z: int) -> bool {
    post.x == x && post.y == y && y <= z && (if x == y { post.z == z } else { post.z == z + 1 })
}

#[trust_vc::proof]
#[trust_vc::requires(RcInit::State::initialize(post, x, y, z))]
#[trust_vc::ensures(rc_rel_init(post, x, y, z))]
fn rc_correct_init(post: RcInit::State, x: int, y: int, z: int) {}

#[trust_vc::proof]
#[trust_vc::requires(rc_rel_init(post, x, y, z))]
#[trust_vc::ensures(RcInit::State::initialize(post, x, y, z))]
fn rc_rev_init(post: RcInit::State, x: int, y: int, z: int) {}

#[trust_vc::spec]
fn rc_rel_init_wrong(post: RcInit::State, x: int, y: int, z: int) -> bool {
    post.x == x && post.y == y && y <= z && (if x == y { post.z == z } else { post.z == z + 2 })
}

#[trust_vc::proof]
#[trust_vc::requires(rc_rel_init_wrong(post, x, y, z))]
#[trust_vc::ensures(RcInit::State::initialize(post, x, y, z))]
fn rc_rev_init_wrong(post: RcInit::State, x: int, y: int, z: int) {}

// ---------------------------------------------------------------------------
// upstream `relation_codegen` tr2, ADAPTED: the `assert(pre.y <= pre.z)` in the
// else-branch is dropped (D1a refuses `assert`), so the expected relation is
// upstream's `rel_tr2_strong` with the assert conjunct removed.

trust_vc::state_machine! { RcTr2 {
    fields {
        pub x: int,
        pub y: int,
        pub z: int,
    }

    transition! {
        tr2(b: bool, c: bool) {
            if b {
                update z = pre.z + 1;
            }
            require(c);
        }
    }

    #[invariant]
    pub fn the_inv(self) -> bool {
        self.y <= self.z
    }

    #[inductive(tr2)]
    fn rc_tr2_inductive(pre: Self, post: Self, b: bool, c: bool) {}
} }

#[trust_vc::spec]
fn rc_rel_tr2_noassert(pre: RcTr2::State, post: RcTr2::State, b: bool, c: bool) -> bool {
    (if b { post.z == pre.z + 1 } else { post.z == pre.z })
        && c
        && pre.x == post.x
        && pre.y == post.y
}

#[trust_vc::proof]
#[trust_vc::requires(RcTr2::State::tr2(pre, post, b, c))]
#[trust_vc::ensures(rc_rel_tr2_noassert(pre, post, b, c))]
fn rc_correct_tr2_noassert(pre: RcTr2::State, post: RcTr2::State, b: bool, c: bool) {}

#[trust_vc::proof]
#[trust_vc::requires(rc_rel_tr2_noassert(pre, post, b, c))]
#[trust_vc::ensures(RcTr2::State::tr2(pre, post, b, c))]
fn rc_rev_tr2_noassert(pre: RcTr2::State, post: RcTr2::State, b: bool, c: bool) {}

// ---------------------------------------------------------------------------
// upstream `lemma_doesnt_verify` / `lemma_doesnt_verify_init`, ADAPTED from
// tokenized to non-tokenized (the `#[sharding(variable)]` attribute is dropped;
// the inductiveness rule is identical).

trust_vc::state_machine! { LemmaFails {
    fields {
        pub t: int,
    }

    transition! {
        tr(x: int) {
            update t = x;
        }
    }

    #[invariant]
    pub fn the_inv(self) -> bool {
        self.t == 5
    }

    #[inductive(tr)]
    pub fn ldv_tr_inductive(pre: Self, post: Self, x: int) {}
} }

trust_vc::state_machine! { LemmaFailsInit {
    fields {
        pub t: int,
    }

    init! {
        tr(x: int) {
            init t = x;
        }
    }

    #[invariant]
    pub fn the_inv(self) -> bool {
        self.t == 5
    }

    #[inductive(tr)]
    pub fn ldv_init_inductive(post: Self, x: int) {}
} }

// ---------------------------------------------------------------------------
// upstream diagnostic cases: every machine below is REFUSED, and the client
// function that mentions it fails closed with the upstream message.

trust_vc::state_machine! { DupeName {
        fields {
            pub v: Map<int, int>,
        }

        transition! {
            some_name() {
            }
        }

        transition! {
            some_name() {
            }
        }
} }
#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn sm_dupe_name_fail_error(s: DupeName::State) {}
trust_vc::state_machine! { BirdsEyeNt {
        fields { pub t: int }

        transition! {
            tr() {
                birds_eye let x = 5; // error
                update t = 5;
            }
        }
} }
#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn sm_birds_eye_nontokenized_error(s: BirdsEyeNt::State) {}
trust_vc::state_machine! { NormalSharding {
        fields {
            #[sharding(variable)]
            pub t: int,
        }
} }
#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn sm_normal_sm_sharding_error(s: NormalSharding::State) {}
trust_vc::state_machine! { InitMissing {
        fields {
            pub t: int,
        }

        init! {
            init() {
            }
        }
} }
#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn sm_init_wf_init_missing_error(s: InitMissing::State) {}
trust_vc::state_machine! { InitDupe {
        fields {
            pub t: int,
        }

        init! {
            init() {
                init t = 5;
                init t = 6;
            }
        }
} }
#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn sm_init_wf_init_dupe_error(s: InitDupe::State) {}
trust_vc::state_machine! { InitDupeCond {
        fields {
            pub t: int,
        }

        init! {
            init() {
                init t = 5;
                if 1 + 2 == 3 {
                    init t = 6;
                } else {
                    init t = 7;
                }
            }
        }
} }
#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn sm_init_wf_init_dupe_conditional_error(s: InitDupeCond::State) {}
trust_vc::state_machine! { InitIfBranch {
        fields {
            pub t: int,
        }

        init! {
            init() {
                if 1 + 2 == 3 {
                    init t = 6;
                } else {
                }
            }
        }
} }
#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn sm_init_wf_init_if_error(s: InitIfBranch::State) {}
trust_vc::state_machine! { InitElseBranch {
        fields {
            pub t: int,
        }

        init! {
            init() {
                if 1 + 2 == 3 {
                } else {
                    init t = 6;
                }
            }
        }
} }
#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn sm_init_wf_init_else_error(s: InitElseBranch::State) {}
trust_vc::state_machine! { InitUpdate {
        fields {
            pub t: int,
        }

        init! {
            init() {
                init t = 6;
                update t = 5;
            }
        }
} }
#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn sm_init_wf_update_error(s: InitUpdate::State) {}
trust_vc::state_machine! { InitUpdate2 {
        fields {
            pub t: int,
        }

        init! {
            init() {
                update t = 5;
            }
        }
} }
#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn sm_init_wf_update2_error(s: InitUpdate2::State) {}
trust_vc::state_machine! { InitAssert {
        fields {
            pub t: int,
        }

        init! {
            init() {
                assert(true);
                init t = 6;
            }
        }
} }
#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn sm_init_wf_assert_error(s: InitAssert::State) {}
trust_vc::state_machine! { UpdateDupe {
        fields {
            pub t: int,
        }

        transition! {
            tr() {
                update t = 5;
                update t = 6;
            }
        }
} }
#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn sm_normal_wf_update_dupe_error(s: UpdateDupe::State) {}
trust_vc::state_machine! { UpdateDupeCond {
        fields {
            pub t: int,
        }

        transition! {
            tr() {
                update t = 5;
                if true {
                    update t = 6;
                }
            }
        }
} }
#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn sm_normal_wf_update_dupe_conditional_error(s: UpdateDupeCond::State) {}
trust_vc::state_machine! { UpdateDupeCond2 {
        fields {
            pub t: int,
        }

        transition! {
            tr() {
                update t = 5;
                if true {
                } else {
                    update t = 6;
                }
            }
        }
} }
#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn sm_normal_wf_update_dupe_conditional2_error(s: UpdateDupeCond2::State) {}
trust_vc::state_machine! { UpdateInit {
        fields {
            pub t: int,
        }

        transition! {
            tr() {
                init t = 5;
            }
        }
} }
#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn sm_normal_wf_update_init_error(s: UpdateInit::State) {}
trust_vc::state_machine! { ReadonlyUpdate {
        fields {
            pub t: int,
        }

        readonly! {
            tr() {
                update t = 5;
            }
        }
} }
#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn sm_readonly_wf_update_error(s: ReadonlyUpdate::State) {}
trust_vc::state_machine! { PropertyUpdate {
        fields {
            pub t: int,
        }

        property! {
            tr() {
                update t = 5;
            }
        }
} }
#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn sm_property_wf_update_error(s: PropertyUpdate::State) {}
trust_vc::state_machine! { ReadonlyInit {
        fields {
            pub t: int,
        }

        readonly! {
            tr() {
                init t = 5;
            }
        }
} }
#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn sm_readonly_wf_init_error(s: ReadonlyInit::State) {}
trust_vc::state_machine! { PropertyInit {
        fields {
            pub t: int,
        }

        property! {
            tr() {
                init t = 5;
            }
        }
} }
#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn sm_property_wf_init_error(s: PropertyInit::State) {}
trust_vc::state_machine! { FieldNotFound {
        fields {
            pub t: int,
        }

        transition! {
            tr() {
                update whats_this = 5;
            }
        }
} }
#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn sm_field_not_found_error(s: FieldNotFound::State) {}
trust_vc::state_machine! { LetRepeat1 {
        fields {
            pub t: Map<int, int>
        }

        transition! {
            tr() {
                if true {
                    let x = 5;
                } else {
                    let x = 5;
                }
            }
        }
} }
#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn sm_no_let_repeated_idents_error(s: LetRepeat1::State) {}
trust_vc::state_machine! { LetRepeat2 {
        fields {
            pub t: Map<int, int>
        }

        transition! {
            tr() {
                let x = 5;
                let x = 5;
            }
        }
} }
#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn sm_no_let_repeated_idents2_error(s: LetRepeat2::State) {}
trust_vc::state_machine! { LetRepeat3 {
        fields {
            pub t: Map<int, int>
        }

        transition! {
            tr(x: int) {
                let x = 5;
            }
        }
} }
#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn sm_no_let_repeated_idents3_error(s: LetRepeat3::State) {}
trust_vc::state_machine! { PreInInit {
        fields {
            pub t: int,
        }

        init! {
            init() {
                update t = pre.t;
            }
        }
} }
#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn sm_pre_in_init_error(s: PreInInit::State) {}
trust_vc::state_machine! { SelfInTransition {
        fields {
            pub t: int,
        }

        transition! {
            tr() {
                update t = self.t;
            }
        }
} }
#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn sm_self_in_transition_error(s: SelfInTransition::State) {}
trust_vc::state_machine! { PostInTransition {
        fields {
            pub t: int,
        }

        transition! {
            tr() {
                update t = post.t;
            }
        }
} }
#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn sm_post_in_transition_error(s: PostInTransition::State) {}
struct Bar {}
trust_vc::state_machine! { SuperPath {
        fields { pub t: int }

        transition! {
            // this is disallowed because the macro would try to copy the path into
            // an inner module
            tr(foo: super::Bar) {
                update t = 5;
            }
        }
} }
#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn sm_super_error(s: SuperPath::State) {}
trust_vc::state_machine! { DupLemma {
        fields {
            pub t: int,
        }

        transition! {
            tr(x: int) {
                update t = x;
            }
        }

        #[inductive(tr)]
        pub fn lemma_tr1(pre: Self, post: Self, x: int) {
        }

        #[inductive(tr)]
        pub fn lemma_tr2(pre: Self, post: Self, x: int) {
        }
} }
#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn sm_duplicate_inductive_lemma_error(s: DupLemma::State) {}
trust_vc::state_machine! { MissingLemma {
        fields {
            pub t: int,
        }

        transition! {
            tr(x: int) {
                update t = x;
            }
        }

        #[invariant]
        pub fn the_inv(self) -> bool {
            self.t == 5
        }
} }
#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn sm_missing_inductive_lemma_error(s: MissingLemma::State) {}
trust_vc::state_machine! { MissingLemmaInit {
        fields {
            pub t: int,
        }

        init! {
            tr(x: int) {
                init t = x;
            }
        }

        #[invariant]
        pub fn the_inv(self) -> bool {
            self.t == 5
        }
} }
#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn sm_missing_inductive_lemma_init_error(s: MissingLemmaInit::State) {}
trust_vc::state_machine! { LemmaReadonly {
        fields {
            pub t: int,
        }

        readonly! {
            tr(x: int) {
            }
        }

        #[inductive(tr)]
        pub fn lemma_tr1(pre: Self, post: Self, x: int) {
        }
} }
#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn sm_inductive_lemma_readonly_error(s: LemmaReadonly::State) {}
trust_vc::state_machine! { LemmaProperty {
        fields {
            pub t: int,
        }

        property! {
            tr(x: int) {
            }
        }

        #[inductive(tr)]
        pub fn lemma_tr1(pre: Self, post: Self, x: int) {
        }
} }
#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn sm_inductive_lemma_property_error(s: LemmaProperty::State) {}
trust_vc::state_machine! { LemmaWrongArgs {
        fields {
            pub t: int,
        }

        transition! {
            tr(x: int) {
            }
        }

        #[inductive(tr)]
        pub fn lemma_tr1(pre: Self, post: Self, y: int) {
        }
} }
#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn sm_lemma_wrong_args_error(s: LemmaWrongArgs::State) {}
trust_vc::state_machine! { LemmaBadName {
        fields {
            pub t: int,
        }

        transition! {
            tr(x: int) {
            }
        }

        #[inductive(tro)]
        pub fn lemma_tr1(pre: Self, post: Self, x: int) {
        }
} }
#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn sm_lemma_bad_transition_name_error(s: LemmaBadName::State) {}
trust_vc::state_machine! { LemmaGenerics {
        fields {
            pub t: int,
        }

        transition! {
            tr(x: int) {
            }
        }

        #[inductive(tr)]
        pub fn lemma_tr1<T>(pre: Self, post: Self, x: int) {
        }
} }
#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn sm_lemma_bad_generic_params_error(s: LemmaGenerics::State) {}
trust_vc::state_machine! { LemmaReturn {
        fields {
            pub t: int,
        }

        transition! {
            tr(x: int) {
            }
        }

        #[inductive(tr)]
        pub fn lemma_tr1(pre: Self, post: Self, x: int) -> bool {
        }
} }
#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn sm_lemma_bad_return_type_error(s: LemmaReturn::State) {}
trust_vc::state_machine! { LemmaHeader {
        fields {
            pub t: int,
        }

        transition! {
            tr(x: int) {
            }
        }

        #[inductive(tr)]
        pub fn lemma_tr1(pre: Self, post: Self, x: int) {
            requires(true);
        }
} }
#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn sm_lemma_bad_header_error(s: LemmaHeader::State) {}
trust_vc::state_machine! { ConflictAttrs {
        fields {
            pub t: int,
        }

        init! {
            tr(x: int) {
                init t = x;
            }
        }

        #[invariant]
        #[inductive(tr)]
        pub fn the_inv(self) -> bool {
            self.t == 5
        }
} }
#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn sm_conflicting_attrs_error(s: ConflictAttrs::State) {}
trust_vc::state_machine! { ExplicitModeInv {
        fields {
            pub t: int,
        }

        init! {
            tr(x: int) {
                init t = x;
            }
        }

        #[invariant]
        #[verifier::spec]
        pub fn the_inv(self) -> bool {
            true
        }
} }
#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn sm_explicit_mode_inv_error(s: ExplicitModeInv::State) {}
trust_vc::state_machine! { ExplicitModeField {
        fields {
            #[verifier::spec]
            pub t: int,
        }
} }
#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn sm_explicit_mode_field_error(s: ExplicitModeField::State) {}
trust_vc::state_machine! { ExplicitModeProof {
        fields {
            pub t: int,
        }

        init! {
            tr(x: int) {
                init t = x;
            }
        }

        #[invariant]
        pub fn the_inv(self) -> bool {
            true
        }

        #[inductive(tr)]
        #[verifier::proof]
        pub fn lemma_tr1(post: Self, x: int) {
        }
} }
#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn sm_explicit_mode_proof_error(s: ExplicitModeProof::State) {}
trust_vc::state_machine! { InvWrongParams {
        fields {
            pub t: int,
        }

        init! {
            tr(x: int) {
                init t = x;
            }
        }

        #[invariant]
        pub fn the_inv(x: int) -> bool {
            true
        }

        #[inductive(tr)]
        #[verifier::proof]
        pub fn lemma_tr1(post: Self, x: int) {
        } // FAILS
} }
#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn sm_inv_wrong_params_error(s: InvWrongParams::State) {}
trust_vc::state_machine! { InvWrongRet {
        fields {
            pub t: int,
        }

        init! {
            tr(x: int) {
                init t = x;
            }
        }

        #[invariant]
        pub fn the_inv(self) -> int {
            5
        }

        #[inductive(tr)]
        #[verifier::proof]
        pub fn lemma_tr1(post: Self, x: int) {
        } // FAILS
} }
#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn sm_inv_wrong_ret_error(s: InvWrongRet::State) {}
trust_vc::state_machine! { InvWrongGenerics {
        fields {
            pub t: int,
        }

        init! {
            tr(x: int) {
                init t = x;
            }
        }

        #[invariant]
        pub fn the_inv<V>(self) -> bool {
            true
        }

        #[inductive(tr)]
        #[verifier::proof]
        pub fn lemma_tr1(post: Self, x: int) {
        } // FAILS
} }
#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn sm_inv_wrong_generics_error(s: InvWrongGenerics::State) {}
trust_vc::state_machine! { MultiFields {
        fields {
            pub t: int,
        }

        fields {
            pub x: int,
        }
} }
#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn sm_multiple_fields_error(s: MultiFields::State) {}
trust_vc::state_machine! { NoFields {
} }
#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn sm_no_fields_error(s: NoFields::State) {}
trust_vc::state_machine! { FieldReserved1 {
        fields {
            pub instance: int,
        }
} }
#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn sm_field_name_reserved_ident1_error(s: FieldReserved1::State) {}
trust_vc::state_machine! { FieldReserved2 {
        fields {
            pub param_token_a: int,
        }
} }
#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn sm_field_name_reserved_ident2_error(s: FieldReserved2::State) {}
trust_vc::state_machine! { LetReserved1 {
        fields {
            pub t: int,
        }

        transition! {
            tr() {
                let instance = 5;
            }
        }
} }
#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn sm_let_name_reserved_ident1_error(s: LetReserved1::State) {}
trust_vc::state_machine! { LetReserved2 {
        fields {
            pub t: int,
        }

        transition! {
            tr() {
                let param_token_a = 5;
            }
        }
} }
#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn sm_let_name_reserved_ident2_error(s: LetReserved2::State) {}
trust_vc::state_machine! { ArgReserved1 {
        fields {
            pub t: int,
        }

        transition! {
            tr(instance: int) {
            }
        }
} }
#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn sm_arg_reserved_ident1_error(s: ArgReserved1::State) {}
trust_vc::state_machine! { ArgReserved2 {
        fields {
            pub t: int,
        }

        transition! {
            tr(param_token_a: int) {
            }
        }
} }
#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn sm_arg_reserved_ident2_error(s: ArgReserved2::State) {}
trust_vc::state_machine! { instance {
        fields {
            pub t: int,
        }
} }
#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn sm_sm_name_reserved_ident1_error(s: instance::State) {}
trust_vc::state_machine! { param_token_a {
        fields {
            pub t: int,
        }
} }
#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn sm_sm_name_reserved_ident2_error(s: param_token_a::State) {}


#[trust_vc::ensures(true)]
fn state_machine_relation_codegen_tr1_verified(y: u64, z: u64) {
    trust_vc::assume!(y <= z);
    trust_vc::assume!(z < 1000u64);

    let pre = ScalarState { x: 7u64, y, z };
    let post = ScalarState {
        x: pre.x,
        y: pre.y,
        z: pre.z + 1u64,
    };

    trust_vc::assert!(post.x == pre.x);
    trust_vc::assert!(post.y == pre.y);
    trust_vc::assert!(post.z == pre.z + 1u64);
    trust_vc::assert!(post.y <= post.z);
}

#[trust_vc::ensures(true)]
fn state_machine_init_branch_relation_verified(x: u64, y: u64, z: u64) {
    trust_vc::assume!(y <= z);
    trust_vc::assume!(z < 1000u64);

    let post = ScalarState {
        x,
        y,
        z: if x == y { z } else { z + 1u64 },
    };

    trust_vc::assert!(post.x == x);
    trust_vc::assert!(post.y == y);
    trust_vc::assert!(post.y <= post.z);
}

#[trust_vc::ensures(true)]
fn tokenized_bool_add_remove_surrogate_verified() {
    let init_false = false;
    let added = init_false || true;
    let removed = added && false;
    let have_token = added;

    trust_vc::assert!(added);
    trust_vc::assert!(have_token);
    trust_vc::assert!(!removed);
    trust_vc::assert!(removed == init_false);
}

#[trust_vc::ensures(true)]
fn state_machine_relation_wrong_post_counterexample() {
    let pre_z = 4u64;
    let post_z = 5u64;

    trust_vc::assert!(post_z == pre_z);
}

#[trust_vc::ensures(true)]
fn tokenized_bool_have_missing_counterexample() {
    let optional_true_token = false;

    trust_vc::assert!(optional_true_token);
}

#[trust_vc::ensures(true)]
fn state_machine_macro_surface_currently_blocked() {
    state_machine! {
        X {
            fields {
                pub t: u64,
            }

            transition! {
                tr() {
                    update t = 5u64;
                }
            }
        }
    };

    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn tokenized_state_machine_macro_surface_currently_blocked() {
    tokenized_state_machine! {
        X {
            fields {
                #[sharding(variable)]
                pub t: u64,
            }

            init! {
                initialize() {
                    init t = 5u64;
                }
            }
        }
    };

    trust_vc::assert!(true);
}
