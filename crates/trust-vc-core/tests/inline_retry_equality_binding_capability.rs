// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! CAPABILITY + SOUNDNESS PIN (proof_in_spec.rs
//! `proof_calling_spec_helper_wrong_result_counterexample` port shape,
//! 2026-09-13): a wrong claim about a value BOUND to a spec-fn call —
//! `returns(out)` with `out == successor(i)`, `ensures(out == 5)` where
//! `successor(3) == 4` — came back `Unknown (quantifier-ematching-exists)`:
//! ay refuses to certify the SAT model against the definitional `forall`, and
//! the demand-inline retry that exists for exactly this class died at encoder
//! setup with "Undefined function: successor". The equality-binding map had
//! recorded `out ↦ successor(i)` from the RAW assumption, so after the retry
//! inlined every call it substituted the raw call straight back in — to a UF
//! the override never declares. The binding is now extracted from the
//! inline-substituted assumption; the ground retry decides and the wrong
//! claim is a model-validated Counterexample, the right one Verified.

use trust_vc_core::{verify_function_from_file, VerifyResult};

fn verify(tmp_id: &str, func: &str, src: &str) -> Result<VerifyResult, String> {
    let mut p = std::env::temp_dir();
    p.push(format!("tvc_ireb_{}_{}.rs", std::process::id(), tmp_id));
    std::fs::write(&p, src).expect("write fixture");
    let result =
        verify_function_from_file(p.to_str().expect("utf8 path"), func).map_err(|e| e.to_string());
    let _ = std::fs::remove_file(&p);
    result
}

const SRC: &str = r#"
#![allow(dead_code)]

use trust_vc_types::nat;

#[trust_vc::spec]
fn successor(i: nat) -> nat {
    i + 1
}

#[trust_vc::spec]
fn twice_successor(i: nat) -> nat {
    successor(successor(i))
}

// CONTROL — the port's true twin: successor(3) == 4.
#[trust_vc::contract(
    requires(i == 3 as nat),
    ensures(out == 4 as nat),
    returns(out),
)]
#[trust_vc::proof]
fn returns_binding_right_claim(i: nat) -> nat {
    successor(i)
}

// LIAR — the port shape verbatim: successor(3) != 5.
#[trust_vc::contract(
    requires(i == 3 as nat),
    ensures(out == 5 as nat),
    returns(out),
)]
#[trust_vc::proof]
fn returns_binding_wrong_claim(i: nat) -> nat {
    successor(i)
}

// Two-level chain through the inline depth bound: twice_successor(3) == 5.
#[trust_vc::contract(
    requires(i == 3 as nat),
    ensures(out == 5 as nat),
    returns(out),
)]
#[trust_vc::proof]
fn nested_binding_right_claim(i: nat) -> nat {
    twice_successor(i)
}

// LIAR — twice_successor(3) != 6.
#[trust_vc::contract(
    requires(i == 3 as nat),
    ensures(out == 6 as nat),
    returns(out),
)]
#[trust_vc::proof]
fn nested_binding_wrong_claim(i: nat) -> nat {
    twice_successor(i)
}

// The same binding through a body `let`: right and wrong claims.
#[trust_vc::ensures(true)]
fn let_binding_right_claim() {
    let out: nat = successor(3 as nat);
    trust_vc::assert!(out == 4 as nat);
}

#[trust_vc::ensures(true)]
fn let_binding_wrong_claim() {
    let out: nat = successor(3 as nat);
    trust_vc::assert!(out == 5 as nat);
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
fn returns_binding_pair() {
    expect_verified("returns_binding_right_claim");
    expect_counterexample("returns_binding_wrong_claim");
}

#[test]
fn nested_binding_pair() {
    expect_verified("nested_binding_right_claim");
    expect_counterexample("nested_binding_wrong_claim");
}

#[test]
fn let_binding_pair() {
    expect_verified("let_binding_right_claim");
    expect_counterexample("let_binding_wrong_claim");
}
