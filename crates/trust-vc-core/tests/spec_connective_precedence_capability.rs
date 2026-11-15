// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Verus spec-connective precedence on the file path (the upstream adts.rs
//! `get_syntax_2_pass` / `matches_syntax_1_pass` /
//! `matches_syntax_precedence_3` / `test_is_variant_get_2` shapes):
//!
//! * `&&&` bullets bind LOOSEST: `{ &&& a ==> b &&& c ==> d }` is
//!   `(a ==> b) && (c ==> d)`. Before the `&&&` lowering the bullets reached
//!   `syn` as bitwise `&` over erased references and bound TIGHTER than `==>`,
//!   so the FALSE claim `{ &&& false ==> true &&& true ==> false }` VERIFIED.
//! * `EXPR matches PAT ==> RHS` stops at a top-level `<==>`: the FALSE claim
//!   `E::B matches A(x) ==> true <==> false` VERIFIED because the RHS
//!   swallowed the equivalence.
//! * A `matches` carrying an `==>` / `&&` tail as the RIGHT operand of a binary
//!   operator (`false && E::A matches E::A ==> true`) is rejected, as Verus
//!   rejects it ("matches with ==> is currently not allowed on the
//!   right-hand-side of most binary operators"); before, the flat rewrite read
//!   it as `false && (.. ==> true)` and `!(false && E::A matches E::A ==>
//!   true)` VERIFIED.
//! * A callee `ensures` that contains `==>` / `<==>` is NOT substituted at
//!   the call site: the connective markers are macros the call-site
//!   substituter does not descend into, so every caller fails closed as
//!   `unresolved variable`. Substituting through the markers is a completeness
//!   change the frozen syn lane does not take; the pins below only require
//!   that no caller, true or false, verifies through such an `ensures`
//!   without the substitution.
//!
//! Every other positive has a liar refuted in the same file context.

use trust_vc_core::{verify_function_from_file, VerifyResult};

fn verify(id: &str, func: &str, src: &str) -> VerifyResult {
    let mut p = std::env::temp_dir();
    p.push(format!("tvc_scp_{}_{}.rs", std::process::id(), id));
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

const SRC: &str = r#"
enum E { A(u64), B }

enum U { A, B }
#[trust_vc::ensures(true)]
fn matches_implies_as_and_right_operand() {
    trust_vc::assert!(!(false && U::A matches U::A ==> true));
}
#[trust_vc::ensures(true)]
fn matches_and_as_eq_right_operand() {
    trust_vc::assert!(false == U::A matches U::A && true);
}
#[trust_vc::ensures(true)]
fn matches_implies_as_bitand_right_operand() {
    trust_vc::assert!(!(false & U::A matches U::A ==> true));
}
#[trust_vc::ensures(true)]
fn matches_implies_as_bitor_right_operand() {
    trust_vc::assert!(!(false | U::A matches U::A ==> true));
}
#[trust_vc::ensures(true)]
fn matches_implies_as_sub_right_operand(e: U) {
    trust_vc::assert!(!(1u8 - e matches U::A ==> true));
}
#[trust_vc::ensures(true)]
fn matches_implies_as_mul_right_operand(a: u8) {
    trust_vc::assert!(a * U::A matches U::A ==> true);
}
#[trust_vc::ensures(true)]
fn matches_implies_in_quantifier_body() {
    trust_vc::assert!(forall|e: U| e matches U::A ==> true);
}
#[trust_vc::ensures(true)]
fn matches_implies_in_quantifier_body_liar() {
    trust_vc::assert!(forall|e: U| e matches U::A ==> false);
}
#[trust_vc::ensures(true)]
fn matches_implies_parenthesized_under_and() {
    trust_vc::assert!(!(false && (U::A matches U::A ==> true)));
}
#[trust_vc::ensures(true)]
fn matches_implies_parenthesized_under_and_liar() {
    trust_vc::assert!(false && (U::A matches U::A ==> true));
}
#[trust_vc::ensures(true)]
fn big_and_false_claim() {
    trust_vc::assert!({ &&& false ==> true &&& true ==> false });
}
#[trust_vc::ensures(true)]
fn big_and_true_claim() {
    trust_vc::assert!({ &&& false ==> false &&& true ==> true });
}
#[trust_vc::ensures(true)]
fn big_and_iff_false_claim() {
    trust_vc::assert!({ &&& true <==> false &&& true });
}
#[trust_vc::requires({ &&& x > 1u64 ==> y == 2u64 &&& x < 1u64 ==> y == 3u64 })]
#[trust_vc::ensures(true)]
fn big_and_requires_in_force(x: u64, y: u64) {
    trust_vc::assert!(x == 0u64 ==> y == 3u64);
    trust_vc::assert!(x == 2u64 ==> y == 2u64);
}
#[trust_vc::requires({ &&& x > 1u64 ==> y == 2u64 &&& x < 1u64 ==> y == 3u64 })]
#[trust_vc::ensures(true)]
fn big_and_requires_liar(x: u64, y: u64) {
    trust_vc::assert!(x == 0u64 ==> y == 2u64);
}
#[trust_vc::requires({ &&& t matches A(x) &&& x == 4u64 })]
#[trust_vc::ensures(true)]
fn big_and_matches_owns_tail(t: E) {
    trust_vc::assert!(t is A && t->0 == 4u64);
}
#[trust_vc::requires({ &&& t matches A(x) &&& x == 4u64 })]
#[trust_vc::ensures(true)]
fn big_and_matches_owns_tail_liar(t: E) {
    trust_vc::assert!(t->0 == 5u64);
}
#[trust_vc::ensures(true)]
fn matches_implies_then_iff_false_claim() {
    trust_vc::assert!(E::B matches A(x) ==> true <==> false);
}
#[trust_vc::ensures(true)]
fn matches_implies_then_iff_true_claim() {
    trust_vc::assert!(E::B matches A(x) ==> false <==> true);
}
#[trust_vc::ensures(true)]
fn matches_binding_implies_then_iff_true_claim() {
    trust_vc::assert!(E::A(5u64) matches A(x) ==> x == 5u64 <==> true);
}
#[trust_vc::ensures(true)]
fn matches_binding_implies_then_iff_liar() {
    trust_vc::assert!(E::A(5u64) matches A(x) ==> x == 6u64 <==> true);
}
#[trust_vc::ensures(e is A ==> result == e->0)]
fn payload_or_zero(e: E) -> u64 {
    match e {
        E::A(v) => v,
        E::B => 0u64,
    }
}
#[trust_vc::ensures(true)]
fn caller_uses_implication_ensures() {
    let r = payload_or_zero(E::A(5u64));
    trust_vc::assert!(r == 5u64);
}
#[trust_vc::ensures(true)]
fn caller_uses_implication_ensures_liar() {
    let r = payload_or_zero(E::A(5u64));
    trust_vc::assert!(r == 6u64);
}
#[trust_vc::ensures(result <==> e is A)]
fn is_a(e: E) -> bool {
    match e {
        E::A(_) => true,
        E::B => false,
    }
}
#[trust_vc::ensures(true)]
fn caller_uses_iff_ensures() {
    let r = is_a(E::A(1u64));
    trust_vc::assert!(r);
}
#[trust_vc::ensures(true)]
fn caller_uses_iff_ensures_liar() {
    let r = is_a(E::B);
    trust_vc::assert!(r);
}
"#;

#[test]
fn big_and_bullets_bind_loosest_over_implication() {
    assert!(
        refuted(&verify("b1", "big_and_false_claim", SRC)),
        "CARDINAL: {{ &&& false ==> true &&& true ==> false }} is FALSE and must be refuted"
    );
    assert!(
        verified(&verify("b2", "big_and_true_claim", SRC)),
        "{{ &&& false ==> false &&& true ==> true }} must verify"
    );
    assert!(
        refuted(&verify("b3", "big_and_iff_false_claim", SRC)),
        "CARDINAL: {{ &&& true <==> false &&& true }} is FALSE and must be refuted"
    );
}

#[test]
fn matches_with_tail_as_binary_right_operand_is_rejected() {
    for (id, func) in [
        ("p1", "matches_implies_as_and_right_operand"),
        ("p2", "matches_and_as_eq_right_operand"),
        // `&`, `|`, `-`, `*` after an operand are binary too (Verus's
        // `handle_binary_ops` rejects every `Expr::Binary`); the `&` / `|`
        // forms used to reach the solver as a Bool
        // `bvand` / `bvor` sort mismatch instead.
        ("p5", "matches_implies_as_bitand_right_operand"),
        ("p6", "matches_implies_as_bitor_right_operand"),
        ("p7", "matches_implies_as_sub_right_operand"),
        ("p8", "matches_implies_as_mul_right_operand"),
    ] {
        let r = verify(id, func, SRC);
        assert!(
            matches!(&r, VerifyResult::Error { message } if message.contains("is currently not allowed on the right-hand-side")),
            "{func}: Verus rejects this shape; it must fail closed with the upstream message, got {r:?}"
        );
    }
    assert!(
        verified(&verify(
            "p3",
            "matches_implies_parenthesized_under_and",
            SRC
        )),
        "the parenthesized reading still lowers and verifies"
    );
    assert!(
        refuted(&verify(
            "p4",
            "matches_implies_parenthesized_under_and_liar",
            SRC
        )),
        "the parenthesized false claim must be refuted"
    );
    // A closure / quantifier binder list's closing `|` is not a bitwise or:
    // its body keeps the established `matches ==>` lowering.
    let r = verify("p9", "matches_implies_in_quantifier_body", SRC);
    assert!(
        verified(&r),
        "the quantifier-body implication verifies, got {r:?}"
    );
    let r = verify("p10", "matches_implies_in_quantifier_body_liar", SRC);
    assert!(
        refuted(&r),
        "the quantifier-body false implication must be refuted, got {r:?}"
    );
}

#[test]
fn big_and_requires_bullets_are_each_in_force() {
    assert!(
        verified(&verify("r1", "big_and_requires_in_force", SRC)),
        "both bulleted implications of the requires are in force"
    );
    assert!(
        refuted(&verify("r2", "big_and_requires_liar", SRC)),
        "a claim the bullets do not entail must be refuted"
    );
}

#[test]
fn big_and_matches_bullet_owns_following_bullets() {
    assert!(
        verified(&verify("m1", "big_and_matches_owns_tail", SRC)),
        "`&&& t matches A(x) &&& x == 4` scopes x over the tail"
    );
    assert!(
        refuted(&verify("m2", "big_and_matches_owns_tail_liar", SRC)),
        "the wrong payload claim must be refuted"
    );
}

#[test]
fn matches_implication_rhs_stops_at_iff() {
    assert!(
        refuted(&verify("i1", "matches_implies_then_iff_false_claim", SRC)),
        "CARDINAL: (B matches A(x) ==> true) <==> false is FALSE and must be refuted"
    );
    assert!(
        verified(&verify("i2", "matches_implies_then_iff_true_claim", SRC)),
        "(B matches A(x) ==> false) <==> true must verify"
    );
    assert!(
        verified(&verify(
            "i3",
            "matches_binding_implies_then_iff_true_claim",
            SRC
        )),
        "the binding still scopes into the implication RHS"
    );
    assert!(
        refuted(&verify("i4", "matches_binding_implies_then_iff_liar", SRC)),
        "the wrong bound-payload claim must be refuted"
    );
}

#[test]
fn callee_ensures_with_connectives_never_verify_a_liar() {
    let r = verify("c2", "caller_uses_implication_ensures_liar", SRC);
    assert!(
        !verified(&r),
        "CARDINAL: the wrong result claim through `e is A ==> result == e->0` \
         must not verify: {r:?}"
    );
    let r = verify("c4", "caller_uses_iff_ensures_liar", SRC);
    assert!(
        !verified(&r),
        "CARDINAL: the wrong claim through `result <==> e is A` must not verify: {r:?}"
    );
}
