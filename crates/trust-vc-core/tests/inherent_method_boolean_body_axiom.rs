// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! An inherent (or no-`self` trait-impl) associated method whose BODY is a
//! boolean/comparison expression. The definitional body axiom is
//! `Sym(args) == <body>`; without parenthesizing the body a comparison body
//! `a == b` spliced into `Sym(args) == a == b` (a chained comparison that fails
//! to PARSE), and a `&&`/`||` body `a && b` mis-parsed as `(Sym(args) == a) && b`
//! (a globally-inconsistent axiom → fail-closed Unknown). Both were fail-closed
//! (never a false-verify); the fix parenthesizes the body (`Sym == (a && b)`),
//! recovering the correct verdicts. CARDINAL: a true fact VERIFIES, a false one
//! must NOT verify.

use trust_vc_core::{verify_function_from_file, VerifyResult};

fn verify(tmp_id: &str, func: &str, src: &str) -> VerifyResult {
    let mut p = std::env::temp_dir();
    p.push(format!("tvc_bba_{}_{}.rs", std::process::id(), tmp_id));
    std::fs::write(&p, src).expect("write fixture");
    let r = verify_function_from_file(p.to_str().unwrap(), func).unwrap_or_else(|e| {
        VerifyResult::Error {
            message: e.to_string(),
        }
    });
    let _ = std::fs::remove_file(&p);
    r
}

const CMP_BODY: &str = r#"
struct S;
impl S {
    #[trust_vc::ensures(result == (a == b))]
    fn eq(a: u64, b: u64) -> bool { a == b }
}
#[trust_vc::ensures(true)]
fn eq_true() { let r: bool = S::eq(3u64, 3u64); trust_vc::assert!(r); }
#[trust_vc::ensures(true)]
fn eq_false_neg() { let r: bool = S::eq(3u64, 4u64); trust_vc::assert!(r); }
#[trust_vc::ensures(true)]
fn eq_negation() { let r: bool = S::eq(3u64, 4u64); trust_vc::assert!(!r); }
"#;

const AND_BODY: &str = r#"
struct S;
impl S {
    #[trust_vc::ensures(result == (a && b))]
    fn both(a: bool, b: bool) -> bool { a && b }
}
#[trust_vc::ensures(true)]
fn both_true() { let r: bool = S::both(true, true); trust_vc::assert!(r); }
#[trust_vc::ensures(true)]
fn both_false_neg() { let r: bool = S::both(true, false); trust_vc::assert!(r); }
#[trust_vc::ensures(true)]
fn both_negation() { let r: bool = S::both(true, false); trust_vc::assert!(!r); }
"#;

// A WITH-`self` PREDICATE method (`fn is_pos(&self) -> bool { self.x > 0 }`) — the
// ubiquitous Verus spec-predicate shape. Its comparison body hit the SAME
// unparenthesized body-axiom defect; the parenthesization fix recovers it.
const SELF_PREDICATE: &str = r#"
struct S { x: u64 }
impl S {
    #[trust_vc::ensures(result == (self.x > 0u64))]
    fn is_pos(&self) -> bool { self.x > 0u64 }
}
#[trust_vc::requires(s.x == 5u64)]
#[trust_vc::ensures(true)]
fn pred_pos(s: S) { trust_vc::assert!(s.is_pos()); }
#[trust_vc::requires(s.x == 0u64)]
#[trust_vc::ensures(true)]
fn pred_false_neg(s: S) { trust_vc::assert!(s.is_pos()); }
#[trust_vc::requires(s.x == 0u64)]
#[trust_vc::ensures(true)]
fn pred_negation(s: S) { trust_vc::assert!(!s.is_pos()); }
"#;

#[test]
fn comparison_body_true_fact_verifies() {
    assert!(matches!(
        verify("eqt", "eq_true", CMP_BODY),
        VerifyResult::Verified
    ));
    assert!(matches!(
        verify("eqn", "eq_negation", CMP_BODY),
        VerifyResult::Verified
    ));
}

#[test]
fn comparison_body_false_fact_not_verified() {
    assert!(
        !matches!(
            verify("eqf", "eq_false_neg", CMP_BODY),
            VerifyResult::Verified
        ),
        "CARDINAL: S::eq(3,4) is false — asserting it must NOT verify"
    );
}

#[test]
fn boolean_and_body_true_fact_verifies() {
    assert!(matches!(
        verify("bt", "both_true", AND_BODY),
        VerifyResult::Verified
    ));
    assert!(matches!(
        verify("bn", "both_negation", AND_BODY),
        VerifyResult::Verified
    ));
}

#[test]
fn boolean_and_body_false_fact_not_verified() {
    assert!(
        !matches!(
            verify("bf", "both_false_neg", AND_BODY),
            VerifyResult::Verified
        ),
        "CARDINAL: S::both(true,false) is false — asserting it must NOT verify"
    );
}

#[test]
fn self_predicate_comparison_body_true_fact_verifies() {
    assert!(matches!(
        verify("pp", "pred_pos", SELF_PREDICATE),
        VerifyResult::Verified
    ));
    assert!(matches!(
        verify("pn", "pred_negation", SELF_PREDICATE),
        VerifyResult::Verified
    ));
}

#[test]
fn self_predicate_comparison_body_false_fact_not_verified() {
    assert!(
        !matches!(
            verify("pf", "pred_false_neg", SELF_PREDICATE),
            VerifyResult::Verified
        ),
        "CARDINAL: s.is_pos() is false when s.x == 0 — asserting it must NOT verify"
    );
}
