// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Verus variant spec DSL: `e is Variant` / `e !is Variant` variant tests over
//! GENERAL datatypes (enums, Option), extending the prior Result-only `is Ok`/
//! `is Err` surface. Desugars to a match-bool the match encoder resolves against
//! the receiver's datatype. Positives Verify; every liar is fail-closed.

use trust_vc_core::{verify_function_from_file, VerifyResult};

fn verify(id: &str, func: &str, src: &str) -> VerifyResult {
    let mut p = std::env::temp_dir();
    p.push(format!("tvc_vis_{}_{}.rs", std::process::id(), id));
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

const SRC: &str = r#"
enum E { A(u64), B }
#[trust_vc::ensures(result is A)]
fn mk_a() -> E { E::A(5u64) }
#[trust_vc::ensures(result is B)]
fn mk_a_liar() -> E { E::A(5u64) }
#[trust_vc::ensures(result !is B)]
fn mk_notis() -> E { E::A(5u64) }
#[trust_vc::ensures(result !is A)]
fn mk_notis_liar() -> E { E::A(5u64) }
#[trust_vc::ensures(result is Some)]
fn mk_some() -> Option<u64> { Some(5u64) }
#[trust_vc::ensures(result is None)]
fn mk_some_liar() -> Option<u64> { Some(5u64) }
#[trust_vc::requires(e is A)]
#[trust_vc::ensures(true)]
fn assume_is(e: E) { trust_vc::assert!(e is A); }
#[trust_vc::ensures((result is A) && !(result is B))]
fn is_in_conjunction() -> E { E::A(5u64) }
#[trust_vc::ensures(result is Ok)]
fn result_is_ok() -> Result<u64, u64> { Ok(5u64) }
"#;

#[test]
fn is_variant_test_verifies_and_liar_fails_closed() {
    assert!(
        verified(&verify("a", "mk_a", SRC)),
        "result is A must verify"
    );
    assert!(
        !verified(&verify("al", "mk_a_liar", SRC)),
        "CARDINAL: result is B (it is A) must NOT verify"
    );
}
#[test]
fn notis_variant_test_verifies_and_liar_fails_closed() {
    assert!(
        verified(&verify("n", "mk_notis", SRC)),
        "result !is B must verify"
    );
    assert!(
        !verified(&verify("nl", "mk_notis_liar", SRC)),
        "CARDINAL: result !is A (it is A) must NOT verify"
    );
}
#[test]
fn is_variant_test_on_option() {
    assert!(
        verified(&verify("s", "mk_some", SRC)),
        "result is Some must verify"
    );
    assert!(
        !verified(&verify("sl", "mk_some_liar", SRC)),
        "CARDINAL: result is None (it is Some) must NOT verify"
    );
}
#[test]
fn is_in_requires_and_conjunction_and_result_regression() {
    assert!(
        verified(&verify("u", "assume_is", SRC)),
        "requires e is A + assert e is A must verify"
    );
    assert!(
        verified(&verify("c", "is_in_conjunction", SRC)),
        "(result is A) && !(result is B) must verify"
    );
    assert!(
        verified(&verify("r", "result_is_ok", SRC)),
        "existing Result `is Ok` must still verify"
    );
}
