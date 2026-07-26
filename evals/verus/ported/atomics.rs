// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

// First partial executable TrustVc scout for upstream Verus
// `source/rust_verify_test/tests/atomics.rs`.
//
// Upstream atomics.rs exercises Verus' atomic-invariant checker: an
// `open_atomic_invariant!` body may contain at most one atomic operation, may
// not contain ordinary exec operations, and the same one-atomic-operation rule
// is enforced for functions marked `#[verifier(atomic)]`. This Rust-valid scout
// keeps the corpus entry as `unsupported-gap` and covers only the direct boolean
// acceptance predicates that TrustVc can verify today:
// - one atomic operation and no non-atomic operation verifies;
// - a proof-only prefix plus one atomic operation verifies;
// - two atomic operations are rejected as a counterexample;
// - a non-atomic operation is rejected as a counterexample; and
// - the Verus `open_atomic_invariant!` macro boundary remains fail-closed.
//
// Full parity remains unsupported: AtomicInvariant/LocalInvariant semantics,
// invariant masks, tracked credits, opens_invariants/no_unwind clauses,
// #[verifier(atomic)] lowering, closure checks, recursion diagnostics, trait
// atomic diagnostics, loop-specific diagnostics, and Verus diagnostic text are
// not modeled here.

#![allow(dead_code, unused_macros)]

pub const ATOMICS_RS_EXPECTED_CASES: &[(&str, &str, &str, usize)] = &[
    (
        "open_atomic_invariant_one_atomic_verified",
        "one_atomic_ok",
        "verified",
        1,
    ),
    (
        "open_atomic_invariant_proof_prefix_verified",
        "proof_call_ok",
        "verified",
        1,
    ),
    (
        "atomic_function_one_atomic_verified",
        "untrusted_atomic_success",
        "verified",
        1,
    ),
    (
        "open_atomic_invariant_two_atomic_counterexample",
        "two_atomic_fail",
        "counterexample",
        1,
    ),
    (
        "open_atomic_invariant_non_atomic_counterexample",
        "non_atomic_fail",
        "counterexample",
        1,
    ),
    (
        "atomic_function_non_atomic_counterexample",
        "untrusted_atomic_fail",
        "counterexample",
        1,
    ),
    (
        "open_atomic_invariant_macro_boundary_fail_closed",
        "open_atomic_invariant_macro_boundary",
        "error",
        0,
    ),
];

pub const ATOMICS_RS_EXPECTED_ERROR_PATTERNS: &[(&str, &[&str])] = &[(
    "open_atomic_invariant_macro_boundary_fail_closed",
    &["unsupported", "macro", "open_atomic_invariant"],
)];

pub fn atomics_rs_expected_cases() -> &'static [(&'static str, &'static str, &'static str, usize)]
{
    ATOMICS_RS_EXPECTED_CASES
}

pub fn atomics_rs_expected_error_patterns() -> &'static [(&'static str, &'static [&'static str])]
{
    ATOMICS_RS_EXPECTED_ERROR_PATTERNS
}

macro_rules! open_atomic_invariant {
    ($($tokens:tt)*) => {
        true
    };
}

struct AtomicInvariantToken {
    atomic_ops: u8,
    non_atomic_ops: u8,
}

#[trust_vc::ensures(true)]
fn open_atomic_invariant_one_atomic_verified() {
    let atomic_operations = 1u8;
    let non_atomic_operations = 0u8;

    let accepted = atomic_operations <= 1u8 && non_atomic_operations == 0u8;
    trust_vc::assert!(accepted);
}

#[trust_vc::ensures(true)]
fn open_atomic_invariant_proof_prefix_verified() {
    let proof_operations = 1u8;
    let atomic_operations = 1u8;
    let non_atomic_operations = 0u8;

    let accepted =
        proof_operations == 1u8 && atomic_operations <= 1u8 && non_atomic_operations == 0u8;
    trust_vc::assert!(accepted);
}

#[trust_vc::ensures(true)]
fn open_atomic_invariant_two_atomic_counterexample() {
    let atomic_operations = 2u8;
    let non_atomic_operations = 0u8;

    let accepted = atomic_operations <= 1u8 && non_atomic_operations == 0u8;
    trust_vc::assert!(accepted);
}

#[trust_vc::ensures(true)]
fn open_atomic_invariant_non_atomic_counterexample() {
    let atomic_operations = 1u8;
    let non_atomic_operations = 1u8;

    let accepted = atomic_operations <= 1u8 && non_atomic_operations == 0u8;
    trust_vc::assert!(accepted);
}

#[trust_vc::ensures(true)]
fn atomic_function_one_atomic_verified() {
    let atomic_operations = 1u8;
    let non_atomic_operations = 0u8;

    let accepted = atomic_operations <= 1u8 && non_atomic_operations == 0u8;
    trust_vc::assert!(accepted);
}

#[trust_vc::ensures(true)]
fn atomic_function_non_atomic_counterexample() {
    let atomic_operations = 1u8;
    let non_atomic_operations = 1u8;

    let accepted = atomic_operations <= 1u8 && non_atomic_operations == 0u8;
    trust_vc::assert!(accepted);
}

#[trust_vc::ensures(true)]
fn open_atomic_invariant_macro_boundary_fail_closed() {
    let token = AtomicInvariantToken {
        atomic_ops: 1u8,
        non_atomic_ops: 0u8,
    };

    trust_vc::assert!(open_atomic_invariant!(&token => inner => {
        let _atomic_ops = token.atomic_ops;
        let _non_atomic_ops = token.non_atomic_ops;
    }));
}
