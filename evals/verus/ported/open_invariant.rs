// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Expanded partial executable TrustVc scout for upstream Verus
// `source/rust_verify_test/tests/open_invariant.rs`.
//
// The upstream file exercises Verus AtomicInvariant/LocalInvariant opening,
// tracked invariant credits, invariant masks, namespace reasoning, early-exit
// rejection, proof/exec/spec mode restrictions, and trait-signature mask
// inheritance. TrustVc has a lower-level Rust-valid `LocalInvariant` surface, but
// static corpus extraction does not yet lower the direct Verus-style invariant
// macros or model the full tracked permission protocol.
//
// This scout keeps the manifest row as `unsupported-gap` and records only
// stable Rust-valid evidence:
// - direct predicate-preservation and close-restoration obligations that mirror
//   the basic invariant-open shapes;
// - concrete, symbolic, and set-shaped namespace-mask obligations that mirror
//   `opens_invariants` call-site checks;
// - tracked-credit single-use models and stable false witnesses for double
//   spend, credit creation, early exit, namespace aliasing, and wrong close; and
// - direct invariant/tracked macro surfaces that fail closed instead of being
//   silently dropped by source extraction.

#![allow(clippy::let_unit_value, dead_code, unused_macros, unused_variables)]

use trust_vc_types::{int, InvariantPredicate, LocalInvariant, Tracked};

macro_rules! open_atomic_invariant {
    ($($tokens:tt)*) => {
        true
    };
}

macro_rules! open_atomic_invariant_in_proof {
    ($($tokens:tt)*) => {
        true
    };
}

macro_rules! open_local_invariant_in_proof {
    ($($tokens:tt)*) => {
        true
    };
}

pub type OpenInvariantExpectedCase = (&'static str, &'static str, &'static str, usize);
pub type OpenInvariantFailClosedErrorPatterns = (&'static str, &'static [&'static str]);

pub const OPEN_INVARIANT_RS_EXPECTED_CASES: &[OpenInvariantExpectedCase] = &[
    (
        "open_invariant_identity_close_verified",
        "basic_usage2_local",
        "verified",
        1,
    ),
    (
        "open_invariant_restore_required_value_verified",
        "basic_usage/basic_usage_local",
        "verified",
        2,
    ),
    (
        "open_invariant_nested_distinct_namespaces_verified",
        "nested_good/nested_good_local",
        "verified",
        4,
    ),
    (
        "opens_invariants_concrete_subset_verified",
        "opens_invariants_concrete positive subset",
        "verified",
        2,
    ),
    (
        "open_invariant_u8_type_bound_verified",
        "inv_typ_invariants",
        "verified",
        1,
    ),
    (
        "opens_invariants_empty_callee_mask_verified",
        "full_call_empty/full_call_empty_local",
        "verified",
        2,
    ),
    (
        "opens_invariants_symbolic_equal_mask_verified",
        "opens_invariants_concrete symbolic2_caller",
        "verified",
        1,
    ),
    (
        "opens_invariants_set_disjoint_mask_verified",
        "opens_invariants_set",
        "verified",
        3,
    ),
    (
        "open_invariant_single_credit_use_verified",
        "open_inv_in_proof/open_inv_in_proof_local",
        "verified",
        2,
    ),
    (
        "open_invariant_close_wrong_value_counterexample",
        "inv_fail/inv_fail_local",
        "counterexample",
        1,
    ),
    (
        "open_invariant_nested_same_namespace_counterexample",
        "nested_failure/nested_failure_local",
        "counterexample",
        1,
    ),
    (
        "opens_invariants_missing_namespace_counterexample",
        "opens_invariants_concrete failing subset",
        "counterexample",
        1,
    ),
    (
        "opens_invariants_any_callee_inside_open_counterexample",
        "open_call_full/open_call_full_local",
        "counterexample",
        1,
    ),
    (
        "opens_invariants_none_mask_open_counterexample",
        "empty_open/empty_open_local",
        "counterexample",
        1,
    ),
    (
        "opens_invariants_symbolic_mismatch_counterexample",
        "opens_invariants_concrete symbolic_caller",
        "counterexample",
        1,
    ),
    (
        "open_invariant_spend_credit_twice_counterexample",
        "spend_credit_twice/spend_credit_twice_local",
        "counterexample",
        1,
    ),
    (
        "open_invariant_create_credit_from_false_counterexample",
        "create_credit_in_proof/create_credit_in_proof_local",
        "counterexample",
        1,
    ),
    (
        "open_invariant_early_exit_counterexample",
        "return_early/break_early/continue_early",
        "counterexample",
        1,
    ),
    (
        "local_invariant_into_inner_alias_counterexample",
        "inv_lifetime/local_invariant_non_termination_into_inner_issue1102",
        "counterexample",
        1,
    ),
    (
        "switching_inv_to_different_const_counterexample",
        "switching_inv_to_a_different_const_should_still_use_original_const",
        "counterexample",
        1,
    ),
    (
        "open_local_invariant_macro_boundary_fail_closed",
        "basic_usage_local direct macro boundary",
        "error",
        0,
    ),
    (
        "open_atomic_invariant_macro_boundary_fail_closed",
        "basic_usage direct macro boundary",
        "error",
        0,
    ),
    (
        "open_atomic_invariant_in_proof_macro_boundary_fail_closed",
        "open_inv_in_proof/open_inv_in_proof_local direct macro boundary",
        "error",
        0,
    ),
    (
        "open_local_invariant_in_proof_macro_boundary_fail_closed",
        "opens_invariants_trait_method_impl3 direct macro boundary",
        "error",
        0,
    ),
    (
        "tracked_open_invariant_credit_borrow_boundary_fail_closed",
        "OpenInvariantCredit tracked borrow boundary",
        "error",
        0,
    ),
    (
        "local_invariant_constant_boundary_fail_closed",
        "LocalInvariant::constant invariant-state boundary",
        "error",
        0,
    ),
    (
        "local_invariant_into_inner_boundary_fail_closed",
        "inv_lifetime into_inner boundary",
        "error",
        0,
    ),
];

pub fn open_invariant_rs_expected_cases() -> &'static [OpenInvariantExpectedCase] {
    OPEN_INVARIANT_RS_EXPECTED_CASES
}

pub const OPEN_INVARIANT_RS_FAIL_CLOSED_ERROR_PATTERNS: &[OpenInvariantFailClosedErrorPatterns] = &[
    (
        "open_local_invariant_macro_boundary_fail_closed",
        &["Unsupported open_local_invariant!()", "unsupported macros"],
    ),
    (
        "open_atomic_invariant_macro_boundary_fail_closed",
        &["unsupported expression `macro`"],
    ),
    (
        "open_atomic_invariant_in_proof_macro_boundary_fail_closed",
        &["unsupported expression `macro`"],
    ),
    (
        "open_local_invariant_in_proof_macro_boundary_fail_closed",
        &["unsupported expression `macro`"],
    ),
    (
        "tracked_open_invariant_credit_borrow_boundary_fail_closed",
        &["borrow"],
    ),
    (
        "local_invariant_constant_boundary_fail_closed",
        &["constant"],
    ),
    (
        "local_invariant_into_inner_boundary_fail_closed",
        &["into_inner"],
    ),
];

pub fn open_invariant_rs_fail_closed_error_patterns(
) -> &'static [OpenInvariantFailClosedErrorPatterns] {
    OPEN_INVARIANT_RS_FAIL_CLOSED_ERROR_PATTERNS
}

struct ZeroBytePred;

impl InvariantPredicate<(), u8> for ZeroBytePred {
    fn inv(_k: (), v: u8) -> bool {
        v == 0u8
    }
}

type ByteInvariant = LocalInvariant<(), u8, ZeroBytePred>;

type OpenInvariantCredit = int;

struct AtomicInvariantToken {
    namespace: int,
    inner_value: u8,
}

trait InvariantIntoInnerBoundary {
    fn into_inner(self) -> u8;
}

impl InvariantIntoInnerBoundary for ByteInvariant {
    fn into_inner(self) -> u8 {
        panic!("LocalInvariant::into_inner boundary is verification-only")
    }
}

pub fn test_open_invariant_runtime_model_subset() {
    let opened_value = 9u8;
    let closed_value = opened_value;
    assert_eq!(closed_value, opened_value);

    let required_value = 0u8;
    let restored_value = 0u8;
    assert_eq!(required_value, restored_value);

    let caller_allows_a: int = 0;
    let caller_allows_b: int = 1;
    let callee_namespace: int = 1;
    assert!(callee_namespace == caller_allows_a || callee_namespace == caller_allows_b);

    let available_credit_count = 1u8;
    let spent_credit_count = 1u8;
    assert!(spent_credit_count <= available_credit_count);
}

pub fn test_open_invariant_runtime_wrong_close_witness() {
    let required_value = 0u8;
    let closed_value = 7u8;

    assert_eq!(closed_value, required_value);
}

fn open_invariant_identity_close_verified() {
    let opened_value = 9u8;
    let closed_value = opened_value;

    trust_vc::assert!(closed_value == opened_value);
}

fn open_invariant_restore_required_value_verified() {
    let required_value = 0u8;
    let temporary_value = 7u8;
    let closed_value = 0u8;

    trust_vc::assert!(temporary_value != required_value);
    trust_vc::assert!(closed_value == required_value);
}

fn open_invariant_nested_distinct_namespaces_verified() {
    let outer_namespace: int = 0;
    let inner_namespace: int = 1;
    let outer_closed = 0u8;
    let inner_closed = 1u8;

    trust_vc::assert!(outer_namespace != inner_namespace);
    trust_vc::assert!(outer_closed == 0u8);
    trust_vc::assert!(inner_closed == 1u8);
    trust_vc::assert!(outer_closed != inner_closed);
}

fn opens_invariants_concrete_subset_verified() {
    let caller_allows_a: int = 0;
    let caller_allows_b: int = 1;
    let callee_namespace: int = 1;

    trust_vc::assert!(callee_namespace == caller_allows_a || callee_namespace == caller_allows_b);
    trust_vc::assert!(callee_namespace != caller_allows_a);
}

fn open_invariant_u8_type_bound_verified(inner: u8) {
    trust_vc::assert!(inner <= 255u8);
}

fn opens_invariants_empty_callee_mask_verified() {
    let currently_open_namespace: int = 0;
    let callee_open_count = 0u8;

    trust_vc::assert!(currently_open_namespace == 0);
    trust_vc::assert!(callee_open_count == 0u8);
}

fn opens_invariants_symbolic_equal_mask_verified(caller_namespace: int, callee_namespace: int) {
    trust_vc::assume!(caller_namespace == callee_namespace);

    trust_vc::assert!(callee_namespace == caller_namespace);
}

fn opens_invariants_set_disjoint_mask_verified(
    inv1_namespace: int,
    inv2_namespace: int,
    mask_contains_inv1: bool,
    mask_contains_inv2: bool,
) {
    trust_vc::assume!(inv1_namespace != inv2_namespace);
    trust_vc::assume!(!mask_contains_inv1);
    trust_vc::assume!(!mask_contains_inv2);

    trust_vc::assert!(inv1_namespace != inv2_namespace);
    trust_vc::assert!(!mask_contains_inv1);
    trust_vc::assert!(!mask_contains_inv2);
}

fn open_invariant_single_credit_use_verified() {
    let available_credit_count = 1u8;
    let requested_open_count = 1u8;

    trust_vc::assert!(requested_open_count <= available_credit_count);
    trust_vc::assert!(available_credit_count - requested_open_count == 0u8);
}

fn open_invariant_close_wrong_value_counterexample() {
    let required_value = 0u8;
    let closed_value = 7u8;

    trust_vc::assert!(closed_value == required_value);
}

fn open_invariant_nested_same_namespace_counterexample() {
    let outer_namespace: int = 3;
    let inner_namespace: int = 3;

    trust_vc::assert!(outer_namespace != inner_namespace);
}

fn opens_invariants_missing_namespace_counterexample() {
    let caller_allows: int = 0;
    let callee_namespace: int = 1;

    trust_vc::assert!(callee_namespace == caller_allows);
}

fn opens_invariants_any_callee_inside_open_counterexample() {
    let callee_may_open_current_namespace = true;

    trust_vc::assert!(!callee_may_open_current_namespace);
}

fn opens_invariants_none_mask_open_counterexample() {
    let caller_allows_open = false;

    trust_vc::assert!(caller_allows_open);
}

fn opens_invariants_symbolic_mismatch_counterexample() {
    let caller_namespace: int = 0;
    let callee_namespace: int = 1;

    trust_vc::assert!(callee_namespace == caller_namespace);
}

fn open_invariant_spend_credit_twice_counterexample() {
    let available_credit_count = 1u8;
    let requested_open_count = 2u8;

    trust_vc::assert!(requested_open_count <= available_credit_count);
}

fn open_invariant_create_credit_from_false_counterexample() {
    let contradiction_available = false;

    trust_vc::assert!(contradiction_available);
}

fn open_invariant_early_exit_counterexample() {
    let invariant_block_might_exit_early = true;

    trust_vc::assert!(!invariant_block_might_exit_early);
}

fn local_invariant_into_inner_alias_counterexample() {
    let live_linear_handles = 2u8;

    trust_vc::assert!(live_linear_handles == 1u8);
}

fn switching_inv_to_different_const_counterexample() {
    let original_const = 3u8;
    let replacement_const = 7u8;
    let inner_after_switch = replacement_const;

    trust_vc::assert!(inner_after_switch == original_const);
}

#[trust_vc::opens_invariants(any)]
fn open_local_invariant_macro_boundary_fail_closed(inv: &ByteInvariant) {
    trust_vc::open_local_invariant!(&inv => inner => {
        trust_vc::assert!(*inner == *inner);
    });
}

fn open_atomic_invariant_macro_boundary_fail_closed() {
    let token = AtomicInvariantToken {
        namespace: 0,
        inner_value: 0u8,
    };

    trust_vc::assert!(open_atomic_invariant!(&token => inner => {
        let _namespace = token.namespace;
        let _inner_value = token.inner_value;
    }));
}

fn open_atomic_invariant_in_proof_macro_boundary_fail_closed(credit: OpenInvariantCredit) {
    let token = AtomicInvariantToken {
        namespace: 0,
        inner_value: 0u8,
    };

    trust_vc::assert!(
        open_atomic_invariant_in_proof!(credit => &token => inner => {
            let _namespace = token.namespace;
            let _inner_value = token.inner_value;
        })
    );
}

fn open_local_invariant_in_proof_macro_boundary_fail_closed(
    credit: OpenInvariantCredit,
    inv: &ByteInvariant,
) {
    trust_vc::assert!(open_local_invariant_in_proof!(credit => &inv => inner => {
        trust_vc::assert!(*inner == *inner);
    }));
}

fn tracked_open_invariant_credit_borrow_boundary_fail_closed(credit: Tracked<int>) {
    let raw_credit = credit.borrow();

    trust_vc::assert!(*raw_credit == *raw_credit);
}

fn local_invariant_constant_boundary_fail_closed(inv: &ByteInvariant) {
    let constant = inv.constant();

    trust_vc::assert!(constant == constant);
}

fn local_invariant_into_inner_boundary_fail_closed(inv: ByteInvariant) {
    let inner = inv.into_inner();

    trust_vc::assert!(inner == inner);
}
