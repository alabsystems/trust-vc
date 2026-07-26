// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Expanded partial executable TrustVc scout for upstream Verus
// `rust_verify_test/tests/proof_in_spec.rs`.
//
// The upstream file exercises Verus proof blocks embedded inside recursive
// spec/pure functions, including proof-call effects, recursion cycles, tracked
// values, and spinoff prover behavior. TrustVc does not yet support that inline
// proof-in-spec surface. This file records only Rust-valid nearest-neighbor
// coverage: recursive spec functions checked by executable compute assertions,
// deterministic wrong-value counterexamples, verified proof/spec helper calls,
// bit-vector proof surrogates, fail-closed boundaries for proof code written
// inside spec functions, and a currently-verifying choose-body semantic blocker.
//
// Full parity remains unsupported: inline proof blocks inside spec/pure code,
// spec-to-proof calls, proof calls affecting recursive spec termination,
// by-block proof effects, tracked value mode diagnostics, recursion-cycle
// diagnostics, choose-body proof blocks, and spinoff-prover behavior are not
// claimed here. The manifest row must remain unsupported-gap until those
// surfaces have direct replacement evidence.

#![allow(dead_code)]

use trust_vc_types::{nat, Tracked};

pub type ProofInSpecExpectedCase = (&'static str, &'static str, &'static str, usize);
pub type ProofInSpecExpectedErrorPatterns = (&'static str, &'static [&'static str]);

pub const PROOF_IN_SPEC_RS_EXPECTED_CASES: &[ProofInSpecExpectedCase] = &[
    (
        "rec_assert_result_small_compute_verified",
        "rec_assert_result",
        "verified",
        1,
    ),
    (
        "rec_spec_calling_spec_helper_compute_verified",
        "",
        "verified",
        1,
    ),
    (
        "proof_calling_spec_helper_verified",
        "",
        "verified",
        1,
    ),
    (
        "proof_calling_proof_helper_verified",
        "",
        "verified",
        1,
    ),
    (
        "proof_by_compute_spec_helper_verified",
        "",
        "verified",
        1,
    ),
    (
        "rec_assert_bitvector_requires_verified",
        "",
        "verified",
        1,
    ),
    (
        "rec_spinoff_prover_compute_verified",
        "",
        "verified",
        1,
    ),
    (
        "rec_assert_result_wrong_value_counterexample",
        "rec_assert_result",
        "counterexample",
        1,
    ),
    (
        "rec_spec_calling_spec_helper_wrong_value_counterexample",
        "",
        "counterexample",
        1,
    ),
    (
        "proof_calling_spec_helper_wrong_result_counterexample",
        "",
        "counterexample",
        1,
    ),
    (
        "proof_calling_proof_helper_bad_requires_counterexample",
        "",
        "counterexample",
        1,
    ),
    (
        "proof_by_compute_spec_helper_wrong_value_counterexample",
        "",
        "counterexample",
        1,
    ),
    (
        "rec_assert_bitvector_missing_requires_counterexample",
        "",
        "counterexample",
        1,
    ),
    (
        "nonrecursive_spec_proof_block_fails_closed",
        "nonrecursive_not_yet_supported1",
        "error",
        0,
    ),
    (
        "recursive_spec_proof_block_fails_closed",
        "nonrecursive_not_yet_supported2",
        "error",
        0,
    ),
    (
        "proof_fn_local_proof_block_expression_fails_closed",
        "non_spec_fn_not_yet_supported",
        "error",
        0,
    ),
    (
        "spec_proof_block_return_fails_closed",
        "return_not_allowed",
        "error",
        0,
    ),
    (
        "proof_block_assignment_fails_closed",
        "assign_not_allowed",
        "error",
        0,
    ),
    (
        "spec_calling_proof_helper_compute_fails_closed",
        "",
        "error",
        0,
    ),
    (
        "spec_tracked_get_boundary_fails_closed",
        "",
        "error",
        0,
    ),
    (
        "choose_body_proof_block_currently_verifies_blocker",
        "",
        "verified-blocker",
        0,
    ),
];

pub const PROOF_IN_SPEC_RS_EXPECTED_ERROR_PATTERNS: &[ProofInSpecExpectedErrorPatterns] = &[
    (
        "nonrecursive_spec_proof_block_fails_closed",
        &["Unsupported proof_block!()"],
    ),
    (
        "recursive_spec_proof_block_fails_closed",
        &["Unsupported proof_block!()"],
    ),
    (
        "proof_fn_local_proof_block_expression_fails_closed",
        &["Unsupported proof_block!()"],
    ),
    (
        "spec_proof_block_return_fails_closed",
        &["Unsupported proof_block!()"],
    ),
    (
        "proof_block_assignment_fails_closed",
        &["Unsupported proof_block!()"],
    ),
    (
        "spec_calling_proof_helper_compute_fails_closed",
        &["proof_in_spec_ghost_helper"],
    ),
    (
        "spec_tracked_get_boundary_fails_closed",
        &["Tracked::get", "unsupported", "method", "get"],
    ),
];

pub fn proof_in_spec_rs_expected_cases() -> &'static [ProofInSpecExpectedCase] {
    PROOF_IN_SPEC_RS_EXPECTED_CASES
}

pub fn proof_in_spec_rs_expected_error_patterns() -> &'static [ProofInSpecExpectedErrorPatterns] {
    PROOF_IN_SPEC_RS_EXPECTED_ERROR_PATTERNS
}

#[trust_vc::decreases(i)]
#[trust_vc::spec]
fn proof_in_spec_countdown(i: nat) -> nat {
    if i == 0 {
        0
    } else {
        proof_in_spec_countdown((i - 1) as nat) + 1
    }
}

#[trust_vc::ensures(true)]
fn rec_assert_result_small_compute_verified() {
    trust_vc::assert_by_compute!(proof_in_spec_countdown(4 as nat) == (4 as nat); compute_only);
}

#[trust_vc::ensures(true)]
fn rec_assert_result_wrong_value_counterexample() {
    trust_vc::assert_by_compute!(proof_in_spec_countdown(4 as nat) == (5 as nat); compute_only);
}

#[trust_vc::spec]
fn proof_in_spec_successor(i: nat) -> nat {
    i + 1
}

#[trust_vc::decreases(i)]
#[trust_vc::spec]
fn proof_in_spec_countdown_via_spec_helper(i: nat) -> nat {
    if i == 0 {
        0
    } else {
        proof_in_spec_successor(proof_in_spec_countdown_via_spec_helper((i - 1) as nat))
    }
}

#[trust_vc::ensures(true)]
fn rec_spec_calling_spec_helper_compute_verified() {
    trust_vc::assert_by_compute!(
        proof_in_spec_countdown_via_spec_helper(4 as nat) == (4 as nat);
        compute_only
    );
}

#[trust_vc::ensures(true)]
fn rec_spec_calling_spec_helper_wrong_value_counterexample() {
    trust_vc::assert_by_compute!(
        proof_in_spec_countdown_via_spec_helper(4 as nat) == (3 as nat);
        compute_only
    );
}

#[trust_vc::contract(
    requires(i == 3 as nat),
    ensures(out == 4 as nat),
    returns(out),
)]
#[trust_vc::proof]
fn proof_calling_spec_helper_verified(i: nat) -> nat {
    proof_in_spec_successor(i)
}

#[trust_vc::contract(
    requires(i == 3 as nat),
    ensures(out == 5 as nat),
    returns(out),
)]
#[trust_vc::proof]
fn proof_calling_spec_helper_wrong_result_counterexample(i: nat) -> nat {
    proof_in_spec_successor(i)
}

#[trust_vc::proof]
fn proof_in_spec_ghost_helper(i: nat) {
    trust_vc::assert!(i == i);
}

#[trust_vc::contract(
    requires(i == 3 as nat),
    ensures(true),
)]
#[trust_vc::proof]
fn proof_in_spec_requires_three_helper(i: nat) {
    trust_vc::assert!(i == 3 as nat);
}

#[trust_vc::proof]
fn proof_calling_proof_helper_verified() {
    proof_in_spec_requires_three_helper(3 as nat);
}

#[trust_vc::proof]
fn proof_calling_proof_helper_bad_requires_counterexample() {
    proof_in_spec_requires_three_helper(2 as nat);
}

#[trust_vc::ensures(true)]
fn proof_by_compute_spec_helper_verified() {
    trust_vc::assert_by_compute!(proof_in_spec_successor(3 as nat) == (4 as nat); compute_only);
}

#[trust_vc::ensures(true)]
fn proof_by_compute_spec_helper_wrong_value_counterexample() {
    trust_vc::assert_by_compute!(proof_in_spec_successor(3 as nat) == (5 as nat); compute_only);
}

#[trust_vc::requires(i != 0u64)]
#[trust_vc::ensures(true)]
fn rec_assert_bitvector_requires_verified(i: u64) {
    trust_vc::assert_by_bit_vector!(i >> 1u32 < i; requires i != 0u64);
}

#[trust_vc::ensures(true)]
fn rec_assert_bitvector_missing_requires_counterexample(i: u64) {
    trust_vc::assert_by_bit_vector!(i >> 1u32 < i);
}

#[trust_vc::spec]
fn spec_calling_proof_helper_fails_closed(i: nat) -> nat {
    proof_in_spec_ghost_helper(i);
    i
}

#[trust_vc::ensures(true)]
fn spec_calling_proof_helper_compute_fails_closed() {
    trust_vc::assert_by_compute!(
        spec_calling_proof_helper_fails_closed(2 as nat) == (2 as nat);
        compute_only
    );
}

#[trust_vc::spec]
fn nonrecursive_spec_proof_block_fails_closed(i: nat) -> nat {
    trust_vc::proof_block!({
        trust_vc::assert!(true);
    });
    i
}

#[trust_vc::decreases(i)]
#[trust_vc::spec]
fn recursive_spec_proof_block_fails_closed(i: nat) -> nat {
    trust_vc::proof_block!({
        trust_vc::assert!(true);
    });
    if i == 0 {
        0
    } else {
        recursive_spec_proof_block_fails_closed((i - 1) as nat) + 1
    }
}

#[trust_vc::proof]
fn proof_fn_local_proof_block_expression_fails_closed() {
    let value: nat = {
        trust_vc::proof_block!({
            trust_vc::assert!(true);
        });
        3 as nat
    };
    let _ = value;
}

#[trust_vc::spec]
fn spec_proof_block_return_fails_closed(i: nat) -> nat {
    trust_vc::proof_block!({
        if i > 0 {
            return 3 as nat;
        }
    });
    4 as nat
}

#[trust_vc::proof]
fn proof_block_assignment_fails_closed() {
    let mut seen = false;
    let value: nat = {
        trust_vc::proof_block!({
            seen = true;
        });
        3 as nat
    };
    let _ = (seen, value);
}

#[trust_vc::spec]
fn spec_tracked_get_boundary_fails_closed(t: Tracked<nat>) -> nat {
    let value = t.get();
    value
}

#[trust_vc::ensures(true)]
fn choose_body_proof_block_currently_verifies_blocker() {
    let _witness: nat = trust_vc::choose!(|i: nat| {
        trust_vc::proof_block!({
            trust_vc::assert!(true);
        });
        i == i
    });
}

#[trust_vc::decreases(i)]
#[trust_vc::spec]
fn proof_in_spec_spinoff_count(i: nat) -> nat {
    if i == 0 {
        0
    } else {
        proof_in_spec_spinoff_count((i - 1) as nat)
    }
}

#[trust_vc::ensures(true)]
fn rec_spinoff_prover_compute_verified() {
    trust_vc::assert_by_compute!(proof_in_spec_spinoff_count(0 as nat) == (0 as nat); compute_only);
}
