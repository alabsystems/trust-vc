// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

// First partial executable TrustVc scout for upstream Verus
// `source/rust_verify_test/tests/broadcast_forall.rs`.
//
// The upstream file exercises Verus broadcast proof functions, `broadcast use`
// statements, broadcast groups, module-level broadcast imports, recursive-use
// diagnostics, reveal rejection on proof functions, state-machine ordering, and
// mutable-parameter rejection. TrustVc has a different broadcast surface today:
// broadcast lemmas are Rust attributes and group activation is a proc macro.
//
// This scout keeps the upstream manifest entry as `unsupported-gap` and records
// only stable Rust-valid evidence for the closest current TrustVc behavior:
// - an activated grouped broadcast can discharge an opaque predicate assertion;
// - a grouped broadcast can be activated in the same proof as a quantified
//   trigger assertion;
// - a named bundle can activate multiple grouped broadcast lemmas together;
// - an adjacent false universal is rejected with a concrete counterexample;
// - source extraction now ACTIVATES `broadcast_use!` (direct and local-macro
//   expanded), so an activated grouped broadcast discharges an opaque-predicate
//   assertion on the file path just as it does at runtime.
//
// The entry stays `unsupported-gap` because TrustVc still does not mirror Verus
// broadcast proof fn syntax, module-level broadcast use, group declarations, or
// the recursive-use / reveal / state-machine / mutable-parameter diagnostics.

#![allow(clippy::eq_op, dead_code)]

use trust_vc_types::int;

pub const BROADCAST_FORALL_RS_EXPECTED_CASES: &[(&str, &str, &str, usize)] = &[
    (
        "broadcast_forall_grouped_axiom_verified",
        "test_ring_algebra_broadcast_use_stmt_1",
        "verified",
        1,
    ),
    (
        "broadcast_forall_quantified_grouped_axiom_verified",
        "test_ring_algebra_broadcast_use_stmt_1",
        "verified",
        1,
    ),
    (
        "broadcast_forall_named_bundle_verified",
        "test_ring_algebra_basic",
        "verified",
        2,
    ),
    (
        "broadcast_forall_false_universal_counterexample",
        "test_fails_by_broadcast_forall_2",
        "counterexample",
        1,
    ),
    (
        "broadcast_forall_source_broadcast_use_verified",
        "test_ring_algebra_broadcast_use_stmt_1",
        "verified",
        1,
    ),
    (
        "broadcast_forall_source_broadcast_use_local_macro_verified",
        "test_ring_algebra_broadcast_use_stmt_1",
        "verified",
        1,
    ),
];

pub const BROADCAST_FORALL_RS_EXPECTED_ERROR_PATTERNS: &[(&str, &[&str])] = &[];

pub fn broadcast_forall_rs_expected_cases(
) -> &'static [(&'static str, &'static str, &'static str, usize)] {
    BROADCAST_FORALL_RS_EXPECTED_CASES
}

pub fn broadcast_forall_rs_expected_error_patterns(
) -> &'static [(&'static str, &'static [&'static str])] {
    BROADCAST_FORALL_RS_EXPECTED_ERROR_PATTERNS
}

#[trust_vc::spec]
#[trust_vc::opaque]
pub fn broadcast_forall_predicate(i: int) -> bool {
    i == i
}

#[trust_vc::broadcast_group(broadcast_forall_predicate_group)]
#[trust_vc::broadcast]
#[trust_vc::trigger(broadcast_forall_predicate(i))]
pub fn broadcast_forall_predicate_is_true(i: int) {
    trust_vc::ensures!(broadcast_forall_predicate(i));
}

#[trust_vc::spec]
#[trust_vc::opaque]
pub fn broadcast_forall_bundle_alpha(i: int) -> bool {
    i == i
}

#[trust_vc::spec]
#[trust_vc::opaque]
pub fn broadcast_forall_bundle_beta(i: int) -> bool {
    i + 1 > i
}

#[trust_vc::broadcast_group(broadcast_forall_bundle_alpha_group)]
#[trust_vc::broadcast]
#[trust_vc::trigger(broadcast_forall_bundle_alpha(i))]
pub fn broadcast_forall_bundle_alpha_is_true(i: int) {
    trust_vc::ensures!(broadcast_forall_bundle_alpha(i));
}

#[trust_vc::broadcast_group(broadcast_forall_bundle_beta_group)]
#[trust_vc::broadcast]
#[trust_vc::trigger(broadcast_forall_bundle_beta(i))]
pub fn broadcast_forall_bundle_beta_is_true(i: int) {
    trust_vc::ensures!(broadcast_forall_bundle_beta(i));
}

trust_vc::reveal_group!(broadcast_forall_bundle {
    broadcast_forall_bundle_alpha_is_true,
    broadcast_forall_bundle_beta_is_true
});

#[trust_vc::broadcast_group(broadcast_forall_quantified_arith_group)]
#[trust_vc::broadcast]
#[trust_vc::trigger(i + 0)]
pub fn broadcast_forall_quantified_arith_identity(i: int) {
    trust_vc::ensures!(i + 0 == i);
}

#[trust_vc::proof]
pub fn broadcast_forall_grouped_axiom_verified() {
    let witness: int = 10;
    let _ = broadcast_forall_predicate(witness);
    broadcast_forall_predicate_is_true(witness);
    trust_vc::broadcast_use!(broadcast_forall_predicate_group);

    trust_vc::assert!(broadcast_forall_predicate(witness));
}

#[trust_vc::proof]
pub fn broadcast_forall_named_bundle_verified() {
    let witness: int = 10;
    let _ = broadcast_forall_bundle_alpha(witness);
    let _ = broadcast_forall_bundle_beta(witness);
    broadcast_forall_bundle_alpha_is_true(witness);
    broadcast_forall_bundle_beta_is_true(witness);
    trust_vc::broadcast_use!(broadcast_forall_bundle);

    trust_vc::assert!(broadcast_forall_bundle_alpha(witness));
    trust_vc::assert!(broadcast_forall_bundle_beta(witness));
}

#[trust_vc::proof]
#[rustfmt::skip]
pub fn broadcast_forall_quantified_grouped_axiom_verified() {
    broadcast_forall_quantified_arith_identity(0);
    trust_vc::broadcast_use!(broadcast_forall_quantified_arith_group);

    trust_vc::assert!(forall |i: int| #[trigger] (i + 0) == i);
}

#[rustfmt::skip]
fn broadcast_forall_false_universal_counterexample() {
    trust_vc::assert!(forall |i: int| i > 0);
}

pub fn broadcast_forall_source_broadcast_use_verified() {
    trust_vc::broadcast_use!(broadcast_forall_predicate_group);
    trust_vc::assert!(broadcast_forall_predicate(5));
}

pub fn broadcast_forall_source_broadcast_use_local_macro_verified() {
    macro_rules! activate_broadcast_group {
        () => {
            trust_vc::broadcast_use!(broadcast_forall_predicate_group);
        };
    }

    activate_broadcast_group!();
    trust_vc::assert!(broadcast_forall_predicate(5));
}
