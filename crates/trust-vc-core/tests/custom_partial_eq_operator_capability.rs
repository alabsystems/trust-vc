// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! CAPABILITY PIN (audit rows 385/489 — `==` / `!=` on a datatype with a
//! hand-written `PartialEq`, 2026-09-11): the operator now lowers to the
//! impl's own `eq` (the inherent-method body axiom the `.eq()` method call
//! already used), and `!=` to the impl's `ne` when one is written, else to
//! `!eq` — exactly Rust's dispatch. The structural gate of 2026-07-24 stays
//! for the shapes that have no such axiom (a manual `PartialEq` reached only
//! through a FIELD of a derived-PartialEq datatype still fails closed).

use trust_vc_core::{verify_function_from_file, VerifyResult};

fn verify(tmp_id: &str, func: &str, src: &str) -> VerifyResult {
    let mut p = std::env::temp_dir();
    p.push(format!("tvc_cpeo_{}_{}.rs", std::process::id(), tmp_id));
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
#[derive(Clone, Copy)]
struct Inverted { value: u8 }
impl PartialEq for Inverted {
    fn eq(&self, other: &Self) -> bool { self.value != other.value }
}

#[derive(Clone, Copy, Eq)]
struct Plain(u8, bool);
impl PartialEq for Plain {
    fn eq(&self, other: &Self) -> bool { self.0 == other.0 && self.1 == other.1 }
}

#[derive(Clone, Copy)]
struct OddNe { value: u8 }
impl PartialEq for OddNe {
    fn eq(&self, other: &Self) -> bool { self.value == other.value }
    fn ne(&self, _other: &Self) -> bool { true }
}

#[derive(Clone, Copy, PartialEq)]
struct Outer(Inverted);

// CONTROL: `==` means the inverted body — `{1} == {2}` holds.
#[trust_vc::ensures(true)]
fn inverted_eq_operator_control() {
    let a = Inverted { value: 1 };
    let b = Inverted { value: 2 };
    trust_vc::assert!(a == b);
}
// LIAR: the structural reading `{1} == {1}` is FALSE under the inverted body.
#[trust_vc::ensures(true)]
fn inverted_eq_operator_structural_liar() {
    let a = Inverted { value: 1 };
    let same = Inverted { value: 1 };
    trust_vc::assert!(a == same);
}
// CONTROL: `!=` is `!eq` — `{1} != {1}` holds under the inverted body.
#[trust_vc::ensures(true)]
fn inverted_ne_operator_control() {
    let a = Inverted { value: 1 };
    let same = Inverted { value: 1 };
    trust_vc::assert!(a != same);
}
// LIAR: `{1} != {2}` is FALSE under the inverted body.
#[trust_vc::ensures(true)]
fn inverted_ne_operator_liar() {
    let a = Inverted { value: 1 };
    let b = Inverted { value: 2 };
    trust_vc::assert!(a != b);
}
// CONTROL (upstream eq_cmp test_p_ee shape): a field-wise custom body.
#[trust_vc::ensures(true)]
fn plain_custom_ne_operator_control() {
    let left = Plain(3u8, true);
    let different = Plain(3u8, false);
    trust_vc::assert!(left != different);
}
// LIAR: … and `==` of those two is refuted.
#[trust_vc::ensures(true)]
fn plain_custom_eq_operator_liar() {
    let left = Plain(3u8, true);
    let different = Plain(3u8, false);
    trust_vc::assert!(left == different);
}
// CONTROL: a hand-written `ne` is what `!=` calls, even when it disagrees with `eq`.
#[trust_vc::ensures(true)]
fn written_ne_operator_control() {
    let a = OddNe { value: 4 };
    let same = OddNe { value: 4 };
    trust_vc::assert!(a != same);
    trust_vc::assert!(a == same);
}
// LIAR: `!(a != same)` contradicts the written `ne`.
#[trust_vc::ensures(true)]
fn written_ne_operator_liar() {
    let a = OddNe { value: 4 };
    let same = OddNe { value: 4 };
    trust_vc::assert!(!(a != same));
}
// FAIL-CLOSED: a manual PartialEq reached through a FIELD of a derived-PartialEq
// datatype has no axiom for the outer comparison — still refused.
#[trust_vc::ensures(true)]
fn transitive_manual_eq_still_fails_closed() {
    let a = Outer(Inverted { value: 1 });
    let b = Outer(Inverted { value: 2 });
    trust_vc::assert!(a == b);
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
fn control_inverted_eq_operator_verifies() {
    expect_verified("c1", "inverted_eq_operator_control");
}

#[test]
fn liar_inverted_eq_operator_structural_is_rejected() {
    expect_counterexample("l1", "inverted_eq_operator_structural_liar");
}

#[test]
fn control_inverted_ne_operator_verifies() {
    expect_verified("c2", "inverted_ne_operator_control");
}

#[test]
fn liar_inverted_ne_operator_is_rejected() {
    expect_counterexample("l2", "inverted_ne_operator_liar");
}

#[test]
fn control_plain_custom_ne_operator_verifies() {
    expect_verified("c3", "plain_custom_ne_operator_control");
}

#[test]
fn liar_plain_custom_eq_operator_is_rejected() {
    expect_counterexample("l3", "plain_custom_eq_operator_liar");
}

#[test]
fn control_written_ne_operator_verifies() {
    expect_verified("c4", "written_ne_operator_control");
}

#[test]
fn liar_written_ne_operator_is_rejected() {
    expect_counterexample("l4", "written_ne_operator_liar");
}

#[test]
fn transitive_manual_eq_still_fails_closed() {
    match verify("f1", "transitive_manual_eq_still_fails_closed", SRC) {
        VerifyResult::Error { message } if message.contains("hand-written `PartialEq` impl") => {}
        other => panic!("transitive case: expected the structural-gate Error, got {other:?}"),
    }
}
