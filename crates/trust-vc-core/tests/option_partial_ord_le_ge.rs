// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! `Option<integer>` PartialOrd reflexive orderings `.le()` / `.ge()` in spec
//! context. Previously fail-closed (only strict `.lt()`/`.gt()` were modeled);
//! now derived soundly from the existing strict-order + structural-eq encoders:
//! `a <= b` == `a < b || a == b`, `a >= b` == `!(a < b)` (Option<int> is totally
//! ordered: None < Some(_), Some(x) < Some(y) iff x < y).

use trust_vc_core::{verify_function_from_file, VerifyResult};

fn verify(id: &str, func: &str, src: &str) -> VerifyResult {
    let mut p = std::env::temp_dir();
    p.push(format!("tvc_olg_{}_{}.rs", std::process::id(), id));
    std::fs::write(&p, src).expect("write fixture");
    // The override is process-wide and these tests run in parallel. Serialize
    // and restore it so this lane cannot race unrelated verifier tests or leak
    // cache-off state into later cases.
    let r =
        trust_vc_core::env::with_serialized_env_vars(&[("TRUST_VC_DISABLE_VC_CACHE", "1")], || {
            verify_function_from_file(p.to_str().unwrap(), func).unwrap_or_else(|e| {
                VerifyResult::Error {
                    message: e.to_string(),
                }
            })
        });
    let _ = std::fs::remove_file(&p);
    r
}
fn verified(r: &VerifyResult) -> bool {
    matches!(r, VerifyResult::Verified)
}

const SRC: &str = r#"
// Reflexivity: a <= a and a >= a for every Option value.
#[trust_vc::ensures(a.le(&a))]
fn le_reflexive(a: Option<u64>) {}
#[trust_vc::ensures(a.ge(&a))]
fn ge_reflexive(a: Option<u64>) {}

// Definitional equivalences derived from lt / eq.
#[trust_vc::ensures(a.le(&b) == (a.lt(&b) || a == b))]
fn le_definition(a: Option<u64>, b: Option<u64>) -> bool { true }
#[trust_vc::ensures(a.ge(&b) == !a.lt(&b))]
fn ge_definition(a: Option<u64>, b: Option<u64>) -> bool { true }

// Antisymmetry-ish: a <= b && b <= a ==> a == b.
#[trust_vc::ensures((a.le(&b) && b.le(&a)) ==> a == b)]
fn le_antisym(a: Option<u64>, b: Option<u64>) -> bool { true }

// CARDINAL: an unconditional ordering over arbitrary options must NOT verify.
#[trust_vc::ensures(a.ge(&b))]
fn ge_liar(a: Option<u64>, b: Option<u64>) {}
#[trust_vc::ensures(a.le(&b))]
fn le_liar(a: Option<u64>, b: Option<u64>) {}
"#;

#[test]
fn option_le_ge_positives() {
    for f in [
        "le_reflexive",
        "ge_reflexive",
        "le_definition",
        "ge_definition",
        "le_antisym",
    ] {
        assert!(
            verified(&verify(f, f, SRC)),
            "`{f}` should verify (sound total-order fact for Option<int>); got {:?}",
            verify(f, f, SRC)
        );
    }
}

#[test]
fn option_le_ge_liars_fail_closed() {
    for f in ["ge_liar", "le_liar"] {
        assert!(
            !verified(&verify(f, f, SRC)),
            "CARDINAL: `{f}` (unconditional ordering over arbitrary options) must NOT verify"
        );
    }
}
