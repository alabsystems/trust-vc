// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

// First partial executable TrustVc scout for upstream Verus
// `source/rust_verify_test/tests/state_machines.rs`.
//
// The upstream file is primarily a macro and diagnostic suite for Verus
// `state_machine!` and `tokenized_state_machine!`: relation code generation,
// tokenized sharding strategies, inductive lemmas, deterministic guard rules,
// pattern-binding checks, persistent token behavior, and many exact macro error
// messages. TrustVc does not yet provide a one-to-one replacement for those
// state-machine macros or generated token APIs.
//
// This unsupported-gap scout records only stable Rust-valid evidence TrustVc can
// execute today:
// - scalar transition/init relation witnesses adjacent to upstream
//   `relation_codegen`;
// - boolean token-operation surrogates adjacent to upstream `bool_codegen`;
// - stable counterexamples for false relation/token claims; and
// - direct state-machine macro surfaces that fail closed instead of being
//   accepted as replacement evidence.

#![allow(dead_code, unused_macros)]

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
];

pub fn state_machines_rs_expected_cases(
) -> &'static [(&'static str, &'static str, &'static str, usize)] {
    STATE_MACHINES_RS_EXPECTED_CASES
}

pub fn state_machines_rs_expected_error_patterns(
) -> &'static [(&'static str, &'static [&'static str])] {
    STATE_MACHINES_RS_EXPECTED_ERROR_PATTERNS
}

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
