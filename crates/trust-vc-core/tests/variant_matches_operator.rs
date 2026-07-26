// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Verus variant spec DSL: `e matches Pat` — variant/pattern testing in spec
//! position, including BINDING-INTO-IMPLICATION (`e matches A(x) ==> p(x)`,
//! the audit's specifically-noted gap). Desugars to a match-bool the match
//! encoder resolves. Positives Verify; every liar is fail-closed.

use trust_vc_core::{verify_function_from_file, VerifyResult};

fn verify(id: &str, func: &str, src: &str) -> VerifyResult {
    let mut p = std::env::temp_dir();
    p.push(format!("tvc_vm_{}_{}.rs", std::process::id(), id));
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
#[trust_vc::ensures(result matches A)]
fn m_bare() -> E { E::A(5u64) }
#[trust_vc::ensures(result matches B)]
fn m_bare_liar() -> E { E::A(5u64) }
#[trust_vc::ensures(result matches A(x) ==> x == 5u64)]
fn m_bind_pos() -> E { E::A(5u64) }
#[trust_vc::ensures(result matches A(x) ==> x == 6u64)]
fn m_bind_liar() -> E { E::A(5u64) }
#[trust_vc::requires(e matches A(x) ==> x == 5u64)]
#[trust_vc::ensures(true)]
fn m_bind_requires(e: E) {}
#[trust_vc::ensures(result matches Some)]
fn m_option() -> Option<u64> { Some(5u64) }
#[trust_vc::ensures(result matches A(x) && x == 5u64)]
fn m_bind_and_pos() -> E { E::A(5u64) }
#[trust_vc::ensures(result matches A(x) && x == 6u64)]
fn m_bind_and_liar() -> E { E::A(5u64) }
#[trust_vc::ensures({ &&& result matches A(x) &&& x == 5u64 })]
fn m_bind_big_and_pos() -> E { E::A(5u64) }
#[trust_vc::ensures({ &&& result matches A(x) &&& x == 6u64 })]
fn m_bind_big_and_liar() -> E { E::A(5u64) }
"#;

#[test]
fn matches_bare_variant_and_liar() {
    assert!(
        verified(&verify("b", "m_bare", SRC)),
        "result matches A must verify"
    );
    assert!(
        !verified(&verify("bl", "m_bare_liar", SRC)),
        "CARDINAL: result matches B (it is A) must NOT verify"
    );
}
#[test]
fn matches_binding_into_implication_and_liar() {
    assert!(
        verified(&verify("p", "m_bind_pos", SRC)),
        "result matches A(x) ==> x==5 must verify"
    );
    assert!(
        !verified(&verify("l", "m_bind_liar", SRC)),
        "CARDINAL: matches A(x) ==> x==6 must NOT verify"
    );
    assert!(
        verified(&verify("r", "m_bind_requires", SRC)),
        "requires-position binding-into-implication must verify"
    );
}
#[test]
fn matches_on_option() {
    assert!(
        verified(&verify("o", "m_option", SRC)),
        "result matches Some must verify"
    );
}

#[test]
fn matches_binding_into_and_and_big_and() {
    assert!(
        verified(&verify("ap", "m_bind_and_pos", SRC)),
        "matches binding must scope through `&&`"
    );
    assert!(
        !verified(&verify("al", "m_bind_and_liar", SRC)),
        "CARDINAL: a false bound payload under `&&` must not verify"
    );
    assert!(
        verified(&verify("bp", "m_bind_big_and_pos", SRC)),
        "matches binding must scope through following `&&&` bullets"
    );
    assert!(
        !verified(&verify("bl2", "m_bind_big_and_liar", SRC)),
        "CARDINAL: a false bound payload under `&&&` must not verify"
    );
}
