// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! CAPABILITY PIN (audit row 428): the most ordinary counter loop over a `mut`
//! PARAMETER with a `requires` on it verifies.
//!
//! `requires(i == 0) while i < 10 { invariant!(i <= 10); i = i + 1; }
//! assert!(i == 10)` came back `Unknown(VacuousTruth)` (measured 2026-09-10):
//! the whole-function vacuity precheck encoded the entry fact `i == 0` and the
//! loop's negated-guard exit fact `!(i < 10)` over the same bare symbol, so the
//! assumptions looked contradictory although every proof lane frames them as
//! two states. The same loop over `let mut i = 0u64` verified. The precheck now
//! runs in the post-loop framing the lanes use.
//!
//! Liars keep the precheck honest: conflicting `requires` are still caught, a
//! loop that can never exit still contradicts its exit fact, and a wrong
//! post-loop assertion still refutes.

use trust_vc_core::{verify_function_from_file, VerifyResult};

fn verify(tmp_id: &str, func: &str, src: &str) -> VerifyResult {
    let mut p = std::env::temp_dir();
    p.push(format!("tvc_lpc_{}_{}.rs", std::process::id(), tmp_id));
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
#[trust_vc::requires(i == 0u64)]
#[trust_vc::ensures(true)]
pub fn canonical(mut i: u64) {
    while i < 10u64 {
        trust_vc::invariant!(i <= 10u64);
        i = i + 1u64;
    }
    trust_vc::assert!(i == 10u64);
}

#[trust_vc::requires(i <= 3u64)]
#[trust_vc::ensures(true)]
pub fn weaker_requires(mut i: u64) {
    while i < 10u64 {
        trust_vc::invariant!(i <= 10u64);
        i = i + 1u64;
    }
    trust_vc::assert!(i == 10u64);
}

#[trust_vc::requires(i == 0u64)]
#[trust_vc::ensures(result == 10u64)]
pub fn canonical_postcondition(mut i: u64) -> u64 {
    while i < 10u64 {
        trust_vc::invariant!(i <= 10u64);
        i = i + 1u64;
    }
    i
}

#[trust_vc::requires(i == 0u64)]
#[trust_vc::ensures(true)]
pub fn post_loop_liar(mut i: u64) {
    while i < 10u64 {
        trust_vc::invariant!(i <= 10u64);
        i = i + 1u64;
    }
    trust_vc::assert!(i == 11u64);
}

#[trust_vc::requires(i == 0u64)]
#[trust_vc::requires(i == 1u64)]
#[trust_vc::ensures(true)]
pub fn contradictory_requires(mut i: u64) {
    while i < 10u64 {
        trust_vc::invariant!(i <= 10u64);
        i = i + 1u64;
    }
    trust_vc::assert!(i == 11u64);
}

#[trust_vc::requires(c)]
#[trust_vc::ensures(true)]
pub fn loop_that_never_exits(c: bool, mut i: u64) {
    while c {
        trust_vc::invariant!(i <= 10u64);
        i = 0u64;
    }
    trust_vc::assert!(i == 11u64);
}
"#;

fn expect_verified(label: &str, result: VerifyResult) {
    assert!(
        matches!(result, VerifyResult::Verified),
        "{label} must verify: {result:?}"
    );
}

#[test]
fn counter_loop_over_a_required_param_verifies() {
    expect_verified("canonical", verify("c1", "canonical", SRC));
}

#[test]
fn counter_loop_with_a_weaker_requires_verifies() {
    expect_verified("weaker_requires", verify("c2", "weaker_requires", SRC));
}

#[test]
fn counter_loop_result_postcondition_verifies() {
    expect_verified(
        "canonical_postcondition",
        verify("c3", "canonical_postcondition", SRC),
    );
}

#[test]
fn wrong_post_loop_assertion_still_refutes() {
    let result = verify("c4", "post_loop_liar", SRC);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "post_loop_liar must be refuted: {result:?}"
    );
}

#[test]
fn contradictory_requires_are_still_caught() {
    let result = verify("c5", "contradictory_requires", SRC);
    assert!(
        !matches!(result, VerifyResult::Verified),
        "conflicting requires must never let a false assertion verify: {result:?}"
    );
}

#[test]
fn a_loop_that_never_exits_does_not_verify_a_false_post_loop_assertion() {
    let result = verify("c6", "loop_that_never_exits", SRC);
    assert!(
        !matches!(result, VerifyResult::Verified),
        "a never-exiting loop must not let `i == 11` verify: {result:?}"
    );
}
