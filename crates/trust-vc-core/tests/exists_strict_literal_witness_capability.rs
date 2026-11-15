// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! CAPABILITY + SOUNDNESS PIN (quantifiers.rs `test1` port shape, 2026-09-13):
//! an existential goal whose body is a single STRICT comparison of the binder
//! against an integer literal — `exists|i: u32| i > 300u32` — used to reach ay
//! as a bare negated `exists` over a triggerless arithmetic body, where CEGQI
//! gives up (`Solver returned unknown ((incomplete quantifier-cegqi))`). The
//! witness is structurally determined: the neighbour of the literal in the
//! strict direction (`301u32` here) is a witness exactly when any witness
//! exists, because the binder domain is an integer interval. The refutation
//! encoder now proves the stronger quantifier-free goal
//! `range(301) && 301 > 300`, exactly as it already did for `i == w` and the
//! non-strict `i <= w` / `i >= w` shapes.
//!
//! Every false claim of the same shape is refuted (Counterexample), never
//! Verified: a literal on the boundary of the domain leaves no neighbour
//! inside the domain, and a conjunction is NOT taken apart — a false
//! conjunction with a true first conjunct must not borrow its witness.

use trust_vc_core::{verify_function_from_file, VerifyResult};

fn verify(tmp_id: &str, func: &str, src: &str) -> Result<VerifyResult, String> {
    let mut p = std::env::temp_dir();
    p.push(format!("tvc_eslw_{}_{}.rs", std::process::id(), tmp_id));
    std::fs::write(&p, src).expect("write fixture");
    let result =
        verify_function_from_file(p.to_str().expect("utf8 path"), func).map_err(|e| e.to_string());
    let _ = std::fs::remove_file(&p);
    result
}

// The port's Rust-validity surrogate for the `exists(|i: T| …)` call surface
// (evals/verus/ported/quantifiers.rs); the lowering recognizes the call by name.
const SRC: &str = r#"
#![allow(dead_code)]

use trust_vc_types::nat;

fn exists<T, F>(_f: F) -> bool
where
    F: Fn(T) -> bool,
{
    true
}

// CONTROL — the quantifiers.rs `test1` port shape verbatim.
#[trust_vc::requires(ground == 300u32)]
#[trust_vc::ensures(true)]
fn test1_shape(ground: u32) {
    trust_vc::assert!(ground == 300u32);
    trust_vc::assert!(exists(|i: u32| i > 300u32));
}

// LIAR — the `test1_fails` port shape: no u32 exceeds u32::MAX.
#[trust_vc::ensures(true)]
fn test1_fails_shape() {
    trust_vc::assert!(exists(|i: u32| i > 0xffff_ffffu32));
}

// Literal on the left, binder on the right.
#[trust_vc::ensures(true)]
fn flipped_sides_verified() {
    trust_vc::assert!(exists(|i: u32| 300u32 < i));
}

// Strict upper bound: the witness is the literal's lower neighbour (0).
#[trust_vc::ensures(true)]
fn strict_lt_unsigned_verified() {
    trust_vc::assert!(exists(|i: u32| i < 1u32));
}

// LIAR — no u32 is below 0.
#[trust_vc::ensures(true)]
fn strict_lt_unsigned_fails() {
    trust_vc::assert!(exists(|i: u32| i < 0u32));
}

// Signed, both directions, at the domain edge: 127 and -128 are witnesses …
#[trust_vc::ensures(true)]
fn signed_gt_edge_verified() {
    trust_vc::assert!(exists(|i: i8| i > 126i8));
}

#[trust_vc::ensures(true)]
fn signed_lt_edge_verified() {
    trust_vc::assert!(exists(|i: i8| i < -127i8));
}

// … LIARS — and past the edge there is none.
#[trust_vc::ensures(true)]
fn signed_gt_past_edge_fails() {
    trust_vc::assert!(exists(|i: i8| i > 127i8));
}

#[trust_vc::ensures(true)]
fn signed_lt_past_edge_fails() {
    trust_vc::assert!(exists(|i: i8| i < -128i8));
}

// Unbounded `nat`: the upper neighbour always exists.
#[trust_vc::ensures(true)]
fn nat_gt_verified() {
    trust_vc::assert!(exists|i: nat| i > 5);
}

// LIAR — `nat` has no element below 0.
#[trust_vc::ensures(true)]
fn nat_lt_zero_fails() {
    trust_vc::assert!(exists|i: nat| i < 0);
}

// SOUNDNESS GUARD — a false conjunction whose FIRST conjunct alone has a
// witness (301) must not be Verified: the lever must not take a conjunction
// apart.
#[trust_vc::ensures(true)]
fn false_conjunction_never_verified() {
    trust_vc::assert!(exists(|i: u32| i > 300u32 && i < 300u32));
}
"#;

fn expect_verified(func: &str) {
    let r = verify(func, func, SRC);
    assert!(
        matches!(r, Ok(VerifyResult::Verified)),
        "{func} should verify, got {r:?}"
    );
}

fn expect_counterexample(func: &str) {
    let r = verify(func, func, SRC);
    assert!(
        matches!(r, Ok(VerifyResult::Counterexample { .. })),
        "{func} should be refuted with a Counterexample, got {r:?}"
    );
}

#[test]
fn test1_port_shape_verifies() {
    expect_verified("test1_shape");
}

#[test]
fn test1_fails_port_shape_is_refuted() {
    expect_counterexample("test1_fails_shape");
}

#[test]
fn flipped_sides_verify() {
    expect_verified("flipped_sides_verified");
}

#[test]
fn strict_upper_bound_pair() {
    expect_verified("strict_lt_unsigned_verified");
    expect_counterexample("strict_lt_unsigned_fails");
}

#[test]
fn signed_domain_edge_pairs() {
    expect_verified("signed_gt_edge_verified");
    expect_verified("signed_lt_edge_verified");
    expect_counterexample("signed_gt_past_edge_fails");
    expect_counterexample("signed_lt_past_edge_fails");
}

#[test]
fn nat_pair() {
    expect_verified("nat_gt_verified");
    expect_counterexample("nat_lt_zero_fails");
}

#[test]
fn false_conjunction_is_never_verified() {
    let r = verify(
        "false_conjunction_never_verified",
        "false_conjunction_never_verified",
        SRC,
    );
    assert!(
        !matches!(r, Ok(VerifyResult::Verified)),
        "a false conjunction must never verify, got {r:?}"
    );
}
