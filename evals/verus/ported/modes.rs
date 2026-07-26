// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Focused partial executable TrustVc port for upstream Verus
// `rust_verify_test/tests/modes.rs`.
//
// The upstream file remains broad Verus mode-system coverage: spec/proof
// fields, wrapper destructuring, proof/tracked locals, ghost/tracked wrapper
// constructors, unwrap_parameter internals, mode-specific mutable references,
// and exact diagnostics.
//
// This Rust-valid scout intentionally covers only what TrustVc can execute and
// verify through source extraction today:
// - ordinary exec struct/tuple/if/return mode behavior;
// - proof/spec mode call separation and spec expression evaluation;
// - Ghost<T> parameter view erasure and copyability witnesses;
// - Tracked<T> wrapper parameter acceptance and Copy-payload reuse;
// - stable false witnesses for wrong tuple projection and Ghost/Tracked
//   false-tail claims; and
// - fail-closed boundaries for unsupported wrapper destructuring,
//   spec-to-proof calls, old-state expressions, Ghost::new, Tracked::get/borrow,
//   and Ghost<T> tuple projection.
//
// The manifest entry remains `unsupported-gap`.

#![allow(dead_code)]

use trust_vc_types::{int, Ghost, Tracked};

pub type ModesExpectedCase = (&'static str, &'static str, &'static str, usize);
pub type ModesExpectedErrorPatterns = (&'static str, &'static [&'static str]);
pub type ModesFailClosedErrorPatterns = ModesExpectedErrorPatterns;

pub const MODES_RS_EXPECTED_CASES: &[ModesExpectedCase] = &[
    (
        "mode_exec_struct_field_projection_verified",
        "",
        "verified",
        2,
    ),
    (
        "mode_exec_tuple_projection_verified",
        "",
        "verified",
        2,
    ),
    (
        "mode_exec_if_expression_verified",
        "",
        "verified",
        2,
    ),
    (
        "mode_exec_return_value_verified",
        "",
        "verified",
        1,
    ),
    (
        "mode_spec_if_expression_verified",
        "",
        "verified",
        1,
    ),
    (
        "mode_spec_can_call_spec_helper_verified",
        "",
        "verified",
        1,
    ),
    (
        "proof_mode_can_call_spec_helper_verified",
        "",
        "verified",
        1,
    ),
    (
        "proof_mode_can_call_proof_helper_verified",
        "",
        "verified",
        1,
    ),
    (
        "ghost_param_view_reflexive",
        "fn_param_wrappers",
        "verified",
        1,
    ),
    (
        "ghost_param_copyable_verified",
        "",
        "verified",
        1,
    ),
    (
        "tracked_param_wrapper_is_accepted",
        "tracked_tracked_get",
        "verified",
        1,
    ),
    (
        "tracked_copy_wrapper_reuse_verified",
        "",
        "verified",
        1,
    ),
    (
        "empty_tuple_wrappers_verified",
        "",
        "verified",
        1,
    ),
    (
        "mode_ghost_tuple_projection_verified",
        "",
        "verified",
        2,
    ),
    (
        "mode_exec_tuple_projection_wrong_value_counterexample",
        "",
        "counterexample",
        1,
    ),
    (
        "ghost_param_view_wrong_value_counterexample",
        "fn_param_wrappers",
        "counterexample",
        1,
    ),
    (
        "ghost_param_copy_wrong_value_counterexample",
        "",
        "counterexample",
        1,
    ),
    (
        "tracked_wrapper_false_assert_counterexample",
        "",
        "counterexample",
        1,
    ),
    (
        "spec_mode_proof_call_compute_fails_closed",
        "",
        "error",
        0,
    ),
    (
        "mode_old_in_exec_currently_blocked",
        "",
        "error",
        0,
    ),
    (
        "mode_ghost_constructor_in_exec_currently_blocked",
        "",
        "error",
        0,
    ),
    (
        "mode_tracked_get_currently_blocked",
        "",
        "error",
        0,
    ),
    (
        "mode_tracked_borrow_currently_blocked",
        "",
        "error",
        0,
    ),
    (
        "fn_param_wrapper_pattern_currently_blocked",
        "fn_param_wrappers",
        "error",
        0,
    ),
];

pub fn modes_rs_expected_cases() -> &'static [ModesExpectedCase] {
    MODES_RS_EXPECTED_CASES
}

pub const MODES_RS_EXPECTED_ERROR_PATTERNS: &[ModesExpectedErrorPatterns] = &[
    (
        "spec_mode_proof_call_compute_fails_closed",
        &["mode_separation_proof_helper"],
    ),
    (
        "mode_old_in_exec_currently_blocked",
        &["Unsupported old-state expression `old(...)`", "old"],
    ),
    (
        "mode_ghost_constructor_in_exec_currently_blocked",
        &["Ghost::new"],
    ),
    ("mode_tracked_get_currently_blocked", &["get"]),
    ("mode_tracked_borrow_currently_blocked", &["borrow"]),
    (
        "fn_param_wrapper_pattern_currently_blocked",
        &["Unsupported parameter pattern"],
    ),
];

pub const MODES_RS_FAIL_CLOSED_ERROR_PATTERNS: &[ModesFailClosedErrorPatterns] =
    MODES_RS_EXPECTED_ERROR_PATTERNS;

pub fn modes_rs_expected_error_patterns() -> &'static [ModesExpectedErrorPatterns] {
    MODES_RS_EXPECTED_ERROR_PATTERNS
}

pub fn modes_rs_fail_closed_error_patterns() -> &'static [ModesFailClosedErrorPatterns] {
    MODES_RS_FAIL_CLOSED_ERROR_PATTERNS
}

struct ModesExecStruct {
    spec_like: u64,
    exec_like: u64,
}

#[trust_vc::spec]
fn mode_separation_spec_successor(x: int) -> int {
    x + 1
}

#[trust_vc::ensures(result == 2)]
#[trust_vc::spec]
fn mode_separation_spec_double_successor(x: int) -> int {
    mode_separation_spec_successor(mode_separation_spec_successor(x))
}

#[trust_vc::requires(flag)]
#[trust_vc::ensures(result == 1)]
#[trust_vc::spec]
fn mode_spec_if_expression_verified(flag: bool) -> int {
    if flag {
        1
    } else {
        0
    }
}

#[trust_vc::requires(x == 0)]
#[trust_vc::ensures(result == 2)]
#[trust_vc::spec]
fn mode_spec_can_call_spec_helper_verified(x: int) -> int {
    mode_separation_spec_double_successor(x)
}

#[trust_vc::contract(
    requires(x == 7),
    ensures(result == 8),
    returns(result),
)]
#[trust_vc::proof]
fn proof_mode_can_call_spec_helper_verified(x: int) -> int {
    mode_separation_spec_successor(x)
}

#[trust_vc::contract(
    requires(x == 7),
    ensures(true),
)]
#[trust_vc::proof]
fn mode_separation_proof_helper(x: int) {
    trust_vc::assert!(x == x);
}

#[trust_vc::contract(
    requires(x == 7),
    ensures(true),
)]
#[trust_vc::proof]
fn proof_mode_can_call_proof_helper_verified(x: int) {
    mode_separation_proof_helper(x);
    trust_vc::assert!(x == 7);
}

#[trust_vc::spec]
fn spec_mode_calling_proof_helper_fails_closed(x: int) -> int {
    mode_separation_proof_helper(x);
    x
}

#[trust_vc::ensures(true)]
fn spec_mode_proof_call_compute_fails_closed() {
    trust_vc::assert_by_compute!(
        spec_mode_calling_proof_helper_fails_closed(2) == 2;
        compute_only
    );
}

#[trust_vc::ensures(true)]
fn mode_exec_struct_field_projection_verified() {
    let pair = ModesExecStruct {
        spec_like: 4u64,
        exec_like: 9u64,
    };

    trust_vc::assert!(pair.spec_like == 4u64);
    trust_vc::assert!(pair.exec_like == 9u64);
}

#[trust_vc::ensures(true)]
fn mode_exec_tuple_projection_verified() {
    let pair = (4u64, 9u64);

    trust_vc::assert!(pair.0 == 4u64);
    trust_vc::assert!(pair.1 == 9u64);
}

#[trust_vc::requires(flag)]
#[trust_vc::ensures(true)]
fn mode_exec_if_expression_verified(flag: bool) {
    let value = if flag { 3u64 } else { 2u64 };

    trust_vc::assert!(value == 3u64);
}

#[trust_vc::ensures(result == 3u64)]
fn mode_exec_return_value_verified() -> u64 {
    3u64
}

#[trust_vc::ensures(true)]
fn mode_exec_tuple_projection_wrong_value_counterexample() {
    let pair = (4u64, 9u64);

    trust_vc::assert!(pair.0 == 9u64);
}

#[trust_vc::ensures(true)]
fn ghost_param_view_reflexive(g: Ghost<int>) {
    trust_vc::assert!(g.view() == g.view());
}

#[trust_vc::ensures(true)]
fn ghost_param_copyable_verified(g: Ghost<int>) {
    let first = g;
    let second = g;

    trust_vc::assert!(first.view() == second.view());
}

#[trust_vc::ensures(true)]
fn ghost_param_view_wrong_value_counterexample(g: Ghost<int>) {
    trust_vc::assert!(g.view() == g.view());
    trust_vc::assert!(false);
}

#[trust_vc::ensures(true)]
fn ghost_param_copy_wrong_value_counterexample(g: Ghost<int>) {
    let first = g;
    let second = g;

    trust_vc::assert!(first.view() == second.view());
    trust_vc::assert!(false);
}

#[trust_vc::proof]
fn tracked_param_wrapper_is_accepted(t: Tracked<int>) {
    let _ = t;
    trust_vc::assert!(true);
}

#[trust_vc::proof]
fn tracked_copy_wrapper_reuse_verified(t: Tracked<int>) {
    let first = t;
    let second = t;
    let _ = (first, second);
    trust_vc::assert!(true);
}

#[trust_vc::proof]
fn tracked_wrapper_false_assert_counterexample(t: Tracked<int>) {
    let _ = t;
    trust_vc::assert!(false);
}

#[trust_vc::proof]
fn empty_tuple_wrappers_verified(g: Ghost<()>, t: Tracked<()>) {
    let _ = (g, t);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn mode_old_in_exec_currently_blocked(x: u64) {
    trust_vc::assert!(old(x) == x);
}

#[trust_vc::ensures(true)]
fn mode_ghost_constructor_in_exec_currently_blocked() {
    let g = Ghost::new(true);
    trust_vc::assert!(g.view());
}

#[trust_vc::proof]
fn mode_tracked_get_currently_blocked(t: Tracked<int>) {
    let value = t.get();
    trust_vc::assert!(value == value);
}

#[trust_vc::proof]
fn mode_tracked_borrow_currently_blocked(t: Tracked<int>) {
    let value = t.borrow();
    trust_vc::assert!(*value == *value);
}

// De-surrogated 2026-07-18 (ROOT-D pattern-binding / tuple-projection rework):
// `g.view().0` on a Ghost<(u64, u64)> now projects and verifies;
// discriminator-certified genuine (`.0 == .1` distinctness Counterexamples).
#[trust_vc::ensures(true)]
fn mode_ghost_tuple_projection_verified(g: Ghost<(u64, u64)>) {
    trust_vc::assert!(g.view().0 == g.view().0);
}

#[trust_vc::ensures(true)]
fn fn_param_wrapper_pattern_currently_blocked(Ghost(g): Ghost<int>) {
    trust_vc::assert!(g == g);
}
