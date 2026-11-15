// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! CAPABILITY + SOUNDNESS PIN (external_type_specification same-crate enum
//! payload projection, 2026-09-12): the synthesized datatype accessors
//! (`v.is_Variant()`, `v.get_Variant_field()`) are PURE `&self` reads. Before,
//! they had no in-scope impl signature, so the receiver-mutation detector
//! treated the first accessor call on a let-bound enum as a possible mutation
//! and havoced the binding — the NEXT assertion then saw a bare `value` with no
//! model ("unresolved variable `value`"). The liars pin that a user-declared
//! `&mut self` method on the same enum still havocs the receiver, and that a
//! reassignment between two accessor reads is seen.

use trust_vc_core::{verify_function_from_file, VerifyResult};

fn verify(tmp_id: &str, func: &str, src: &str) -> VerifyResult {
    let mut p = std::env::temp_dir();
    p.push(format!("tvc_earp_{}_{}.rs", std::process::id(), tmp_id));
    std::fs::write(&p, src).expect("write fixture");
    let result =
        verify_function_from_file(p.to_str().expect("utf8 path"), func).unwrap_or_else(|e| {
            VerifyResult::Error {
                message: e.to_string(),
            }
        });
    let _ = std::fs::remove_file(&p);
    result
}

const SRC: &str = r#"
enum Shape {
    One(u8),
    Two,
}

impl Shape {
    fn make_two(&mut self) {
        *self = Shape::Two;
    }
}

// CONTROL: two accessor reads on the same let-bound enum; the second still
// sees the constructor.
#[trust_vc::ensures(true)]
fn two_accessor_reads_verify() {
    let value = Shape::One(9u8);
    trust_vc::assert!(value.get_One_0() == 9u8);
    trust_vc::assert!(!value.is_Two());
    trust_vc::assert!(value.is_One());
}

// LIAR: the payload is 9, not 8 — still refuted after a tester read.
#[trust_vc::ensures(true)]
fn accessor_read_after_tester_liar() {
    let value = Shape::One(9u8);
    trust_vc::assert!(value.is_One());
    trust_vc::assert!(value.get_One_0() == 8u8);
}

// CONTROL: a reassignment between reads is tracked.
#[trust_vc::ensures(true)]
fn reassignment_between_reads_verifies() {
    let mut value = Shape::One(9u8);
    trust_vc::assert!(value.is_One());
    value = Shape::Two;
    trust_vc::assert!(value.is_Two());
}

// LIAR: … and the stale variant is not assumed after the reassignment.
#[trust_vc::ensures(true)]
fn reassignment_between_reads_liar() {
    let mut value = Shape::One(9u8);
    trust_vc::assert!(value.is_One());
    value = Shape::Two;
    trust_vc::assert!(value.is_One());
}

// LIAR (SOUNDNESS): a user-declared `&mut self` method still havocs the
// receiver — the old variant must NOT be assumed afterwards. (Today the
// havoced let-bound enum has no declared solver symbol, so the stale read
// fails CLOSED as an extraction error rather than being refuted — an
// over-rejection that predates this change and is pinned as such.)
#[trust_vc::ensures(true)]
fn mutating_method_still_havocs_liar() {
    let mut value = Shape::One(9u8);
    trust_vc::assert!(value.is_One());
    value.make_two();
    trust_vc::assert!(value.is_One());
}
"#;

fn expect_verified(id: &str, func: &str) {
    match verify(id, func, SRC) {
        VerifyResult::Verified => {}
        other => panic!("{func}: expected Verified, got {other:?}"),
    }
}

fn expect_counterexample(id: &str, func: &str) {
    match verify(id, func, SRC) {
        VerifyResult::Counterexample { .. } => {}
        other => panic!("{func}: expected Counterexample, got {other:?}"),
    }
}

#[test]
fn control_two_accessor_reads_verify() {
    expect_verified("c1", "two_accessor_reads_verify");
}

#[test]
fn liar_accessor_read_after_tester_is_refuted() {
    expect_counterexample("l1", "accessor_read_after_tester_liar");
}

#[test]
fn control_reassignment_between_reads_verifies() {
    expect_verified("c2", "reassignment_between_reads_verifies");
}

#[test]
fn liar_reassignment_between_reads_is_refuted() {
    expect_counterexample("l2", "reassignment_between_reads_liar");
}

#[test]
fn liar_mutating_method_still_havocs() {
    match verify("l3", "mutating_method_still_havocs_liar", SRC) {
        VerifyResult::Verified => panic!("a `&mut self` method must still havoc the receiver"),
        VerifyResult::Error { message } => assert!(
            message.contains("unresolved variable `value`"),
            "the fail-closed shape changed — re-pin deliberately: {message}"
        ),
        _ => {}
    }
}
