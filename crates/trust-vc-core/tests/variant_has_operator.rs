// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Verus `has` membership operator: `s has x` desugars to `(s).contains(x)`.
//! Positives Verify; the liar is fail-closed.

use trust_vc_core::{verify_function_from_file, VerifyResult};

fn verify(id: &str, func: &str, src: &str) -> VerifyResult {
    let mut p = std::env::temp_dir();
    p.push(format!("tvc_vh_{}_{}.rs", std::process::id(), id));
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
use trust_vc_types::Set;
#[trust_vc::requires(s has x)]
#[trust_vc::ensures(true)]
fn has_pos(s: Set<u64>, x: u64) { trust_vc::assert!(s has x); }
#[trust_vc::requires(s has x)]
#[trust_vc::ensures(true)]
fn has_liar(s: Set<u64>, x: u64, y: u64) { trust_vc::assert!(s has y); }
#[trust_vc::requires((s has x) && (s has y))]
#[trust_vc::ensures(true)]
fn has_conj(s: Set<u64>, x: u64, y: u64) { trust_vc::assert!(s has x); }
"#;

#[test]
fn has_membership_verifies_and_liar_fails_closed() {
    assert!(
        verified(&verify("p", "has_pos", SRC)),
        "s has x under requires must verify"
    );
    assert!(
        !verified(&verify("l", "has_liar", SRC)),
        "CARDINAL: assert s has y (only x assumed) must NOT verify"
    );
    assert!(
        verified(&verify("c", "has_conj", SRC)),
        "(s has x) && (s has y) must verify"
    );
}
