// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! A loop-body arithmetic obligation is not dropped because a FIELD MEMBER or a
//! struct-literal field LABEL shares the name of a loop-modified variable.
//!
//! Loop-body obligations are rendered over fresh head symbols for every
//! loop-modified variable, and an obligation that still mentions such a
//! variable by its bare name is DEFERRED (not emitted) as inconsistent. The
//! bare-name scan was a plain whole-word match, so the member `i` in `p.i`
//! under a loop counter `i` counted as a bare read: `x = p.i + 100u8` inside
//! `while i < 3 { .. }` under `requires(p.i == 200u8)` VERIFIED a guaranteed
//! overflow, while the same body under a counter named `k` is a
//! counterexample. The same scan dropped the field-write right-hand-side
//! obligation of `o.i.f = o.i.f + 1u8`. The head-symbol substitution had the
//! matching defect: it rewrote the label of `O8 { i: .., ..o }` into
//! `(i__loopbody_0):`, an unparsable obligation. Members and labels are now
//! skipped by both the scan and the substitution; a `..` range operator is not
//! a member access.
//!
//! The label detection bailed on any `|` between the label's `,` and its
//! struct-literal `{` (so a closure / quantifier binder list keeps the
//! conservative reading), which also caught a logical `||` and a bitwise `|`
//! in an EARLIER field value: `x = B8 { b: c || c, i: 5u8 }.i + 251u8` inside
//! `while i < 3u8 { .. }` VERIFIED,
//! and so did `K8 { k: a | a, .. }` and `K8 { k: if c || c { .. } .., .. }`.
//! The deferral scan now ignores every declaration-or-label position (a `word`
//! followed by a single `:`, or right after `::`), none of which reads the
//! variable, and the label detection reads `||` and an operand-led `|` as
//! operators.
//!
//! Every positive has a liar refuted in the same file context.

use trust_vc_core::{verify_function_from_file, VerifyResult};

fn verify(id: &str, func: &str, src: &str) -> VerifyResult {
    let mut p = std::env::temp_dir();
    p.push(format!("tvc_lbmshn_{}_{}.rs", std::process::id(), id));
    std::fs::write(&p, src).expect("write fixture");
    let r = verify_function_from_file(p.to_str().unwrap(), func).unwrap_or_else(|e| {
        VerifyResult::Error {
            message: e.to_string(),
        }
    });
    let _ = std::fs::remove_file(&p);
    r
}

fn verified(r: &VerifyResult) -> bool {
    matches!(r, VerifyResult::Verified)
}

fn refuted(r: &VerifyResult) -> bool {
    matches!(r, VerifyResult::Counterexample { .. })
}

fn refuted_at_overflow_check(r: &VerifyResult) -> bool {
    matches!(r, VerifyResult::Counterexample { obligation_name, .. } if obligation_name.starts_with("overflow_check_"))
}

const SRC: &str = r#"
struct S8 { f: u8 }
struct O8 { i: S8, k: u8 }
struct P8 { i: u8 }

#[trust_vc::requires(p.i == 200u8)]
fn member_named_like_counter_read_overflow(p: P8) { let mut i = 0u64; let mut x = 0u8; while i < 3u64 { trust_vc::invariant!(i <= 3u64); x = p.i + 100u8; i = i + 1u64; } }
#[trust_vc::requires(p.i == 200u8)]
fn member_unrelated_counter_read_overflow_control(p: P8) { let mut k = 0u64; let mut x = 0u8; while k < 3u64 { trust_vc::invariant!(k <= 3u64); x = p.i + 100u8; k = k + 1u64; } }
#[trust_vc::requires(p.i == 100u8)]
fn member_named_like_counter_read_in_range(p: P8) { let mut i = 0u64; let mut x = 0u8; while i < 3u64 { trust_vc::invariant!(i <= 3u64); x = p.i + 100u8; trust_vc::assert!(x == 200u8); i = i + 1u64; } }
#[trust_vc::requires(p.i == 100u8)]
fn member_named_like_counter_read_in_range_liar(p: P8) { let mut i = 0u64; let mut x = 0u8; while i < 3u64 { trust_vc::invariant!(i <= 3u64); x = p.i + 100u8; trust_vc::assert!(x == 201u8); i = i + 1u64; } }
#[trust_vc::requires(o.i.f == 0u8)]
fn nested_member_write_named_like_counter_overflow(mut o: O8) { let mut i = 0u64; while i < 300u64 { trust_vc::invariant!(i <= 300u64); o.i.f = o.i.f + 1u8; i = i + 1u64; } }
#[trust_vc::requires(o.i.f == 0u8)]
fn nested_member_compound_named_like_counter_overflow(mut o: O8) { let mut i = 0u64; while i < 300u64 { trust_vc::invariant!(i <= 300u64); o.i.f += 1u8; i = i + 1u64; } }
#[trust_vc::requires(o.i.f == 0u8)]
fn label_named_like_counter_overflow(mut o: O8) { let mut i = 0u64; let mut x = 0u8; while i < 3u64 { trust_vc::invariant!(i <= 3u64); o.i = S8 { f: 200u8 }; x = o.i.f + 100u8; i = i + 1u64; } }
#[trust_vc::requires(o.i.f == 0u8)]
fn label_named_like_counter_in_range(mut o: O8) { let mut i = 0u64; let mut x = 0u8; while i < 3u64 { trust_vc::invariant!(i <= 3u64); o.i = S8 { f: 100u8 }; x = o.i.f + 100u8; trust_vc::assert!(x == 200u8); i = i + 1u64; } }
#[trust_vc::requires(o.i.f == 0u8)]
fn label_named_like_counter_in_range_liar(mut o: O8) { let mut i = 0u64; let mut x = 0u8; while i < 3u64 { trust_vc::invariant!(i <= 3u64); o.i = S8 { f: 100u8 }; x = o.i.f + 100u8; trust_vc::assert!(x == 201u8); i = i + 1u64; } }
#[trust_vc::ensures(true)]
fn counter_itself_still_havoced(p: P8) { let mut i = 250u8; while i > 0u8 { trust_vc::invariant!(true); i = i + p.i; } }
struct B8 { b: bool, i: u8 }
struct K8 { k: u8, i: u8 }
#[trust_vc::ensures(true)]
fn label_after_logical_or_overflow(c: bool) { let mut i = 0u8; let mut x = 0u8; while i < 3u8 { trust_vc::invariant!(i <= 3u8); x = B8 { b: c || c, i: 5u8 }.i + 251u8; i = i + 1u8; } }
#[trust_vc::ensures(true)]
fn label_after_bitwise_or_overflow(a: u8) { let mut i = 0u8; let mut x = 0u8; while i < 3u8 { trust_vc::invariant!(i <= 3u8); x = K8 { k: a | a, i: 5u8 }.i + 251u8; i = i + 1u8; } }
#[trust_vc::ensures(true)]
fn label_after_if_with_logical_or_overflow(c: bool) { let mut i = 0u8; let mut x = 0u8; while i < 3u8 { trust_vc::invariant!(i <= 3u8); x = K8 { k: if c || c { 1u8 } else { 2u8 }, i: 5u8 }.i + 251u8; i = i + 1u8; } }
#[trust_vc::ensures(true)]
fn label_and_value_after_logical_or_overflow(c: bool) { let mut i = 0u8; let mut x = 0u8; while i < 100u8 { trust_vc::invariant!(i <= 100u8); x = B8 { b: c || c, i: i }.i + 200u8; i = i + 1u8; } }
#[trust_vc::ensures(true)]
fn label_after_logical_or_in_range(c: bool) { let mut i = 0u8; let mut x = 0u8; while i < 3u8 { trust_vc::invariant!(i <= 3u8); x = B8 { b: c || c, i: 5u8 }.i + 250u8; trust_vc::assert!(x == 255u8); i = i + 1u8; } }
#[trust_vc::ensures(true)]
fn label_after_logical_or_in_range_liar(c: bool) { let mut i = 0u8; let mut x = 0u8; while i < 3u8 { trust_vc::invariant!(i <= 3u8); x = B8 { b: c || c, i: 5u8 }.i + 250u8; trust_vc::assert!(x == 254u8); i = i + 1u8; } }
#[trust_vc::ensures(true)]
fn quantifier_binder_named_like_counter(c: bool) { let mut i = 0u8; while i < 3u8 { trust_vc::invariant!(i <= 3u8); trust_vc::assert!(forall|i: int| 0 <= i && i < 1 ==> i == 0); i = i + 1u8; } }
#[trust_vc::ensures(true)]
fn quantifier_binder_named_like_counter_liar(c: bool) { let mut i = 0u8; while i < 3u8 { trust_vc::invariant!(i <= 3u8); trust_vc::assert!(forall|i: int| 0 <= i && i < 2 ==> i == 0); i = i + 1u8; } }
"#;

#[test]
fn member_sharing_a_counter_name_keeps_its_obligation() {
    for (id, func) in [
        ("a1", "member_named_like_counter_read_overflow"),
        ("a2", "member_unrelated_counter_read_overflow_control"),
        ("a3", "nested_member_write_named_like_counter_overflow"),
        ("a4", "nested_member_compound_named_like_counter_overflow"),
        ("a5", "counter_itself_still_havoced"),
    ] {
        let r = verify(id, func, SRC);
        assert!(
            refuted_at_overflow_check(&r),
            "CARDINAL: {func} overflows inside the loop body and must be refuted at its safety obligation, got {r:?}"
        );
    }
    assert!(
        verified(&verify(
            "a6",
            "member_named_like_counter_read_in_range",
            SRC
        )),
        "the in-range read keeps verifying"
    );
    assert!(
        refuted(&verify(
            "a7",
            "member_named_like_counter_read_in_range_liar",
            SRC
        )),
        "the wrong in-range value must be refuted"
    );
}

#[test]
fn struct_literal_label_sharing_a_counter_name_renders_and_keeps_its_obligation() {
    let r = verify("b1", "label_named_like_counter_overflow", SRC);
    assert!(
        refuted_at_overflow_check(&r),
        "CARDINAL: label_named_like_counter_overflow overflows and must be refuted at its safety obligation, got {r:?}"
    );
    let r = verify("b2", "label_named_like_counter_in_range", SRC);
    assert!(
        verified(&r),
        "the in-range read through a rebuilt struct literal verifies, got {r:?}"
    );
    assert!(
        refuted(&verify("b3", "label_named_like_counter_in_range_liar", SRC)),
        "the wrong value read through the rebuilt struct literal must be refuted"
    );
}

#[test]
fn struct_literal_label_after_an_or_operator_keeps_its_obligation() {
    for (id, func) in [
        ("c1", "label_after_logical_or_overflow"),
        ("c2", "label_after_bitwise_or_overflow"),
        ("c3", "label_after_if_with_logical_or_overflow"),
        ("c4", "label_and_value_after_logical_or_overflow"),
    ] {
        let r = verify(id, func, SRC);
        assert!(
            refuted_at_overflow_check(&r),
            "CARDINAL: {func} overflows inside the loop body and must be refuted at its safety obligation, got {r:?}"
        );
    }
    for (id, func) in [
        ("c5", "label_after_logical_or_in_range"),
        ("c7", "quantifier_binder_named_like_counter"),
    ] {
        let r = verify(id, func, SRC);
        assert!(verified(&r), "{func} should verify, got {r:?}");
        let liar = format!("{func}_liar");
        let r = verify(&format!("{id}l"), &liar, SRC);
        assert!(refuted(&r), "{liar} must be refuted, got {r:?}");
    }
}
