// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Focused partial TrustVc port for upstream Verus `rust_verify_test/tests/refs.rs`.
//
// This covers immutable-reference erasure for local borrows, shared-reference
// parameters, direct shared-reference returns including a named lifetime,
// and typed or inferred local aliases initialized from a returned shared
// reference, slice/Vec view witnesses through ordinary shared references,
// read-only local mutable-reference aliases, read-only mutable-reference
// parameter aliases, read-only mutable-reference forwarding through a helper,
// manual old-state snapshots, a simple mutable-reference typing invariant, and
// a mutable reference to a shared reference argument that does not mutate the
// referent, local mutable-reference aliases that write back to the borrowed
// local, field-borrow mutable-reference aliases that write back to the borrowed
// field, mutable-to-shared reference coercion after an update, and direct scalar
// mutable-reference parameter aliases that write back to the erased parameter
// referent, concrete scalar mutable-reference helper-body updates, concrete
// mutable-reference div2 body updates, and shadowed mutable-reference aliases.
// The upstream file remains fail-closed because
// executable `&mut` old-state contracts, tracked mutable references,
// non-scalar/projection parameter-derived mutable-reference alias writes,
// caller-side post-call writeback through mutable-reference arguments,
// mutable self receivers,
// generic mutable references, overloaded-deref specifications, and
// Verus-specific reference diagnostics are not fully mirrored.

#![allow(dead_code)]

use trust_vc_types::{Tracked, View};

pub const REFS_RS_EXPECTED_CASES: &[(&str, &str, &str, usize)] = &[
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

pub fn refs_rs_expected_cases() -> &'static [(&'static str, &'static str, &'static str, usize)] {
    REFS_RS_EXPECTED_CASES
}

struct RefsFieldPair {
    x: u64,
    y: u64,
}

struct RefsSelfValue {
    v: u64,
}

impl RefsSelfValue {
    fn add1(&mut self) {
        self.v = self.v + 1u64;
    }
}

struct RefsDerefValue {
    inner: usize,
}

impl core::ops::Deref for RefsDerefValue {
    type Target = usize;

    fn deref(&self) -> &Self::Target {
        &self.inner
    }
}

#[trust_vc::requires(p == 12u64)]
#[trust_vc::ensures(true)]
fn refs_local_borrow_deref(p: u64) {
    let b: &u64 = &p;
    trust_vc::assert!(*b == 12u64);
}

#[trust_vc::requires(p == 12u64)]
#[trust_vc::ensures(true)]
fn refs_local_borrow_wrong_value_counterexample(p: u64) {
    let b: &u64 = &p;
    trust_vc::assert!(*b == 12u64);
    trust_vc::assert!(p == 13u64);
}

#[trust_vc::requires(*p == 12u64)]
#[trust_vc::ensures(true)]
fn refs_shared_param_alias_deref(p: &u64) {
    let b: &u64 = p;
    trust_vc::assert!(*b == 12u64);
}

#[trust_vc::requires(*p == 12u64)]
#[trust_vc::ensures(result == *p)]
fn refs_shared_param_read(p: &u64) -> u64 {
    *p
}

#[trust_vc::ensures(result == p)]
fn refs_return_ref_identity(p: &u64) -> &u64 {
    p
}

#[trust_vc::ensures(result == p)]
fn refs_return_ref_named_lifetime<'a>(p: &'a u64) -> &'a u64 {
    p
}

#[trust_vc::requires(p == 12u64)]
#[trust_vc::ensures(true)]
fn refs_return_ref_caller_alias(p: u64) {
    let a = p;
    let b: &u64 = refs_return_ref_identity(&a);
    trust_vc::assert!(*b == 12u64);
}

#[trust_vc::requires(p == 12u64)]
#[trust_vc::ensures(true)]
fn refs_return_ref_caller_alias_wrong_value_counterexample(p: u64) {
    let a = p;
    let b: &u64 = refs_return_ref_identity(&a);
    trust_vc::assert!(*b == 12u64);
    trust_vc::assert!(a == 13u64);
}

#[trust_vc::requires(p == 12u64)]
#[trust_vc::ensures(true)]
fn refs_return_ref_caller_alias_inferred(p: u64) {
    let a = p;
    let b = refs_return_ref_identity(&a);
    trust_vc::assert!(*b == 12u64);
}

#[trust_vc::requires(p == 12u64)]
#[trust_vc::ensures(true)]
fn refs_return_ref_caller_alias_inferred_wrong_value_counterexample(p: u64) {
    let a = p;
    let b = refs_return_ref_identity(&a);
    trust_vc::assert!(*b == 12u64);
    trust_vc::assert!(a == 13u64);
}

#[trust_vc::requires(p == 12u64)]
#[trust_vc::ensures(true)]
fn refs_return_ref_named_lifetime_caller(p: u64) {
    let a = p;
    let b = refs_return_ref_named_lifetime(&a);
    trust_vc::assert!(*b == 12u64);
}

#[trust_vc::requires(p == 12u64)]
#[trust_vc::ensures(true)]
fn refs_return_ref_named_lifetime_wrong_value_counterexample(p: u64) {
    let a = p;
    let b = refs_return_ref_named_lifetime(&a);
    trust_vc::assert!(*b == 12u64);
    trust_vc::assert!(a == 13u64);
}

#[trust_vc::ensures(true)]
fn refs_slice_view_from_shared_reference() {
    let slice: &[u8] = &[7u8, 8u8, 9u8];

    trust_vc::assert!(slice.view().len() == 3usize);
    trust_vc::assert!(slice.view().index(1usize) == 8u8);
}

#[trust_vc::ensures(true)]
fn refs_slice_view_wrong_index_counterexample() {
    let slice: &[u8] = &[7u8, 8u8, 9u8];

    trust_vc::assert!(slice.view().index(1usize) == 8u8);
    trust_vc::assert!(false);
}

#[trust_vc::ensures(true)]
fn refs_vec_view_through_shared_reference() {
    let mut v: Vec<u8> = Vec::new();
    v.push(7u8);
    v.push(8u8);
    v.push(9u8);
    let v_ref: &Vec<u8> = &v;

    trust_vc::assert!((*v_ref).view().len() == 3usize);
    trust_vc::assert!((*v_ref).view().index(2usize) == 9u8);
}

#[trust_vc::ensures(true)]
fn refs_vec_view_through_shared_reference_wrong_len_counterexample() {
    let mut v: Vec<u8> = Vec::new();
    v.push(7u8);
    v.push(8u8);
    v.push(9u8);
    let v_ref: &Vec<u8> = &v;

    trust_vc::assert!((*v_ref).view().len() == 3usize);
    trust_vc::assert!(false);
}

#[trust_vc::requires(p == 12u64)]
#[trust_vc::ensures(true)]
fn refs_local_mut_borrow_deref(p: u64) {
    let mut a = p;
    let b: &mut u64 = &mut a;
    trust_vc::assert!(*b == 12u64);
}

#[trust_vc::requires(p == 12u64)]
#[trust_vc::ensures(true)]
fn refs_local_mut_borrow_wrong_value_counterexample(p: u64) {
    let mut a = p;
    let b: &mut u64 = &mut a;
    trust_vc::assert!(*b == 12u64);
    trust_vc::assert!(a == 13u64);
}

#[trust_vc::requires(p == 12u64)]
#[trust_vc::ensures(true)]
fn refs_mut_param_alias_deref(p: &mut u64) {
    let b: &mut u64 = p;
    trust_vc::assert!(*b == 12u64);
}

#[trust_vc::requires(p == 12u64)]
#[trust_vc::ensures(true)]
fn refs_mut_param_alias_wrong_value_counterexample(p: &mut u64) {
    let b: &mut u64 = p;
    trust_vc::assert!(*b == 12u64);
    trust_vc::assert!(p == 13u64);
}

// Upstream `test_mut_ref_forward` gives the callee (`div2`) a REAL `ensures`
// relating the &mut param's post-state, and the caller's post-call reasoning
// flows ONLY through that ensures. `ensures(true)` dropped that clause, so the
// caller's post-call assert had no support once free-call &mut havoc (d568e2e)
// landed. Port-faithfulness fix: state the post-call value like upstream does.
// The callee body matches upstream's shape (no reborrow — div2 works on `a`
// directly); the CALLER keeps the reborrow read, which is this case's surface.
#[trust_vc::requires(p == 12u64)]
#[trust_vc::ensures(p == 12u64)]
fn refs_mut_param_forward_read_callee(p: &mut u64) {
    trust_vc::assert!(p == 12u64);
}

#[trust_vc::requires(p == 12u64)]
#[trust_vc::ensures(true)]
fn refs_mut_param_forward_read(p: &mut u64) {
    refs_mut_param_forward_read_callee(p);
    let b: &mut u64 = p;
    trust_vc::assert!(*b == 12u64);
}

#[trust_vc::requires(p == 12u64)]
#[trust_vc::ensures(true)]
fn refs_mut_param_forward_read_wrong_value_counterexample(p: &mut u64) {
    refs_mut_param_forward_read_callee(p);
    let b: &mut u64 = p;
    trust_vc::assert!(*b == 12u64);
    trust_vc::assert!(p == 13u64);
}

#[trust_vc::ensures(true)]
fn refs_mut_ref_typing_invariant(a: &mut u64) {
    let b: &mut u64 = a;
    trust_vc::assert!(*b >= 0u64);
}

#[trust_vc::ensures(true)]
fn refs_mut_ref_typing_invariant_counterexample(a: &mut u64) {
    let b: &mut u64 = a;
    trust_vc::assert!(*b >= 0u64);
    trust_vc::assert!(false);
}

#[trust_vc::requires(p == 2u64)]
#[trust_vc::ensures(true)]
fn refs_mut_ref_manual_old_snapshot_add1(p: u64) {
    let mut a = p;
    let before = a;
    let a_ref: &mut u64 = &mut a;
    *a_ref = before + 1u64;

    trust_vc::assert!(*a_ref == before + 1u64);
    trust_vc::assert!(a == before + 1u64);
}

#[trust_vc::requires(p == 2u64)]
#[trust_vc::ensures(true)]
fn refs_mut_ref_manual_old_snapshot_wrong_value_counterexample(p: u64) {
    let mut a = p;
    let before = a;
    let a_ref: &mut u64 = &mut a;
    *a_ref = before + 1u64;

    trust_vc::assert!(a == before + 1u64);
    trust_vc::assert!(false);
}

#[trust_vc::requires(a == 5u32)]
#[trust_vc::ensures(true)]
fn refs_mut_ref_coerce_to_shared_ref_after_update(a: &mut u32) {
    let a_ref: &mut u32 = a;
    *a_ref = 6u32;
    {
        let _updated: &u32 = a_ref;
    }

    trust_vc::assert!(a == 6u32);
}

fn refs_mut_ref_to_shared_ref_sink(_x: &mut &u8) {}

#[trust_vc::ensures(true)]
fn refs_mut_ref_to_shared_ref_argument_preserves_local() {
    let mut y: u8 = 0u8;
    refs_mut_ref_to_shared_ref_sink(&mut &y);
    trust_vc::assert!(y == 0u8);
}

#[trust_vc::ensures(true)]
fn refs_mut_ref_to_shared_ref_argument_wrong_value_counterexample() {
    let mut y: u8 = 0u8;
    refs_mut_ref_to_shared_ref_sink(&mut &y);
    trust_vc::assert!(y == 0u8);
    trust_vc::assert!(false);
}

#[trust_vc::requires(p == 12u64)]
#[trust_vc::ensures(true)]
fn refs_local_mut_borrow_assignment(p: u64) {
    let mut a = p;
    let b: &mut u64 = &mut a;
    *b = 13u64;
    trust_vc::assert!(a == 13u64);
}

#[trust_vc::requires(p == 12u64)]
#[trust_vc::ensures(true)]
fn refs_local_mut_borrow_assignment_currently_blocked(p: u64) {
    let mut a = p;
    let b: &mut u64 = &mut a;
    *b = 13u64;
    trust_vc::assert!(a == 13u64);
}

#[trust_vc::requires(p == 12u64)]
#[trust_vc::ensures(true)]
fn refs_local_mut_borrow_assignment_wrong_value_counterexample(p: u64) {
    let mut a = p;
    let b: &mut u64 = &mut a;
    *b = 13u64;
    trust_vc::assert!(a == 13u64);
    trust_vc::assert!(false);
}

#[trust_vc::requires(p == 12u64)]
#[trust_vc::ensures(true)]
fn refs_mut_param_alias_assignment(p: &mut u64) {
    let b: &mut u64 = p;
    *b = 13u64;
    trust_vc::assert!(p == 13u64);
    trust_vc::assert!(*b == 13u64);
}

#[trust_vc::requires(p == 12u64)]
#[trust_vc::ensures(true)]
fn refs_mut_param_alias_assignment_wrong_value_counterexample(p: &mut u64) {
    let b: &mut u64 = p;
    *b = 13u64;
    trust_vc::assert!(p == 13u64);
    trust_vc::assert!(false);
}

#[trust_vc::ensures(true)]
fn refs_mut_ref_field_borrow_assignment() {
    let mut pair = RefsFieldPair { x: 5u64, y: 7u64 };
    let x_ref: &mut u64 = &mut pair.x;
    *x_ref = 6u64;

    trust_vc::assert!(pair.x == 6u64);
    trust_vc::assert!(pair.y == 7u64);
}

#[trust_vc::ensures(true)]
fn refs_mut_ref_field_borrow_assignment_wrong_value_counterexample() {
    let mut pair = RefsFieldPair { x: 5u64, y: 7u64 };
    let x_ref: &mut u64 = &mut pair.x;
    *x_ref = 6u64;

    trust_vc::assert!(pair.x == 6u64);
    trust_vc::assert!(false);
}

#[trust_vc::requires(p == 12u64)]
#[trust_vc::ensures(true)]
fn refs_mut_param_alias_reborrow_assignment_currently_blocked(p: &mut u64) {
    let b: &mut u64 = p;
    let c: &mut u64 = b;
    *c = 13u64;
    trust_vc::assert!(p == 13u64);
}

#[trust_vc::requires(a == 2u64)]
#[trust_vc::ensures(true)]
fn refs_mut_ref_arg_exec_add1_concrete(a: &mut u64) {
    let a_ref: &mut u64 = a;
    *a_ref = 3u64;
    trust_vc::assert!(a == 3u64);
    trust_vc::assert!(*a_ref == 3u64);
}

#[trust_vc::ensures(true)]
fn refs_mut_ref_arg_exec_add1_wrong_value_counterexample(a: &mut u64) {
    let a_ref: &mut u64 = a;
    *a_ref = 3u64;
    trust_vc::assert!(a == 4u64);
}

#[trust_vc::requires(a == 8u64)]
#[trust_vc::ensures(true)]
fn refs_mut_ref_forward_div2_callee(a: &mut u64) {
    let a_ref: &mut u64 = a;
    *a_ref = 4u64;
    trust_vc::assert!(a == 4u64);
}

#[trust_vc::requires(a == 8u64)]
#[trust_vc::ensures(true)]
fn refs_mut_ref_forward_div2_wrong_value_counterexample(a: &mut u64) {
    let a_ref: &mut u64 = a;
    *a_ref = 4u64;
    trust_vc::assert!(a == 4u64);
    trust_vc::assert!(false);
}

// Upstream `test_mut_ref_shadow`'s callee (`foo`) has an EMPTY body — its
// `ensures equal(*x, *old(x))` is a pure no-op preservation contract. The port
// had added a reborrow (`let _shadowed_ref = x;`) that upstream does not have,
// which the two-state `&mut`-postcondition resolver rejects fail-closed
// (escaped reference). Port-faithfulness fix: empty body, like upstream. The
// SHADOWING part of the upstream test lives in the caller-side cases
// (`refs_mut_ref_shadow_preserves_value` / `_wrong_value_counterexample`).
#[trust_vc::requires(x == 6u32)]
#[trust_vc::ensures(x == 6u32)]
fn refs_mut_ref_shadow_noop(x: &mut u32) {}

#[trust_vc::ensures(true)]
fn refs_mut_ref_shadow_preserves_value() {
    let h = 5u32;
    let mut h = h + 1u32;
    let h_ref: &mut u32 = &mut h;
    trust_vc::assert!(*h_ref == 6u32);
}

#[trust_vc::ensures(true)]
fn refs_mut_ref_shadow_wrong_value_counterexample() {
    let h = 5u32;
    let mut h = h + 1u32;
    let h_ref: &mut u32 = &mut h;
    trust_vc::assert!(*h_ref == 6u32);
    trust_vc::assert!(false);
}

#[trust_vc::ensures(true)]
fn refs_mut_ref_arg_exec_caller_currently_blocked() {
    let mut a = 2u64;
    let a_ref: &mut u64 = &mut a;
    refs_mut_ref_arg_exec_add1_concrete(a_ref);
    trust_vc::assert!(a == 3u64);
}

#[trust_vc::requires(a == 2u64)]
#[trust_vc::ensures(true)]
fn refs_mut_ref_arg_exec_direct_param_write_currently_blocked(a: &mut u64) {
    *a = *a + 1u64;
    trust_vc::assert!(a == 3u64);
}

#[trust_vc::ensures(true)]
fn refs_mut_ref_arg_exec_old_state_currently_blocked(a: &mut u64) {
    trust_vc::assert!(*old(a) < 10u64);
}

#[trust_vc::requires(*old(a) < 10u64)]
#[trust_vc::ensures(true)]
fn refs_mut_ref_arg_exec_old_requires_currently_blocked(a: &mut u64) {
    trust_vc::assert!(*a == *a);
}

#[trust_vc::requires(a == 5u64)]
#[trust_vc::ensures(result == 5u64)]
fn refs_mut_ref_return_old_field_value(a: &mut u64) -> u64 {
    let before = *a;
    let a_ref: &mut u64 = a;
    *a_ref = before + 1u64;
    before
}

#[trust_vc::ensures(true)]
fn refs_mut_ref_field_and_update_currently_blocked() {
    let mut pair = RefsFieldPair { x: 5u64, y: 7u64 };
    pair.x = refs_mut_ref_return_old_field_value(&mut pair.x);

    trust_vc::assert!(pair.x == 5u64);
    trust_vc::assert!(pair.y == 7u64);
}

#[trust_vc::ensures(true)]
fn refs_mut_ref_self_receiver_currently_blocked() {
    let mut value = RefsSelfValue { v: 2u64 };
    value.add1();

    trust_vc::assert!(value.v == 3u64);
}

#[trust_vc::ensures(true)]
fn refs_mut_ref_generic_currently_blocked<T: Copy + PartialEq>(a: &mut T) {
    trust_vc::assert!(*a == *a);
}

#[trust_vc::proof]
fn refs_tracked_mut_ref_borrow_currently_blocked(t: Tracked<&mut u64>) {
    let borrowed = t.borrow();

    trust_vc::assert!(**borrowed == **borrowed);
}

#[trust_vc::requires(x.inner == 101usize)]
#[trust_vc::ensures(true)]
fn refs_overloaded_deref_currently_blocked(x: &RefsDerefValue) {
    let value: &usize = x.deref();

    trust_vc::assert!(*value == 101usize);
}
