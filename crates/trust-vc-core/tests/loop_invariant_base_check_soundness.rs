// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! CARDINAL / SOUNDNESS REGRESSION: a FALSE loop invariant on a `let mut`-local
//! counter was silently ASSUMED — its base (establishment) obligation vacuously
//! "verified". Root cause: the loop-invariant base check runs at LOOP ENTRY but
//! its assumption set included the auto-generated post-loop negated-guard exit
//! fact (`post_loop_assumption_*`, e.g. `!(i < 3)`). Together with the loop's
//! entry binding (`i == 0`) that is contradictory (`i == 0 ∧ i >= 3`), so ANY
//! invariant — including `i == 100` — vacuously passed the base case, letting a
//! false invariant prove a false postcondition/assert. Found by the 2026-07-24
//! adversarial re-audit; fixed by excluding post-loop facts from the base check
//! (encoder/verification/typed.rs).
//!
//! The fix is fail-closed and cannot over-reject: the excluded fact is not yet
//! true at entry, so dropping it only makes the establishment obligation
//! stricter — a genuine invariant that holds at entry still verifies, and its
//! post-loop USE (invariant ∧ ¬guard) is unaffected.

use trust_vc_core::{verify_function_from_file, VerifyResult};

fn verify(id: &str, func: &str, src: &str) -> VerifyResult {
    let _env_lock = trust_vc_core::env::lock_env();
    let _vc_cache = trust_vc_core::env::ScopedEnvVar::set("TRUST_VC_DISABLE_VC_CACHE", "1");
    let mut p = std::env::temp_dir();
    p.push(format!("tvc_libc_{}_{}.rs", std::process::id(), id));
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
// FALSE invariant on a let-local counter used to prove a FALSE postcondition
// (real result is 3, not 100).
#[trust_vc::ensures(result == 100u64)]
fn while_false_inv_postcond() -> u64 {
    let mut i: u64 = 0;
    while i < 3u64 { trust_vc::invariant!(i == 100u64); i = i + 1u64; }
    i
}
// FALSE invariant used to prove a FALSE assert inside the loop body.
#[trust_vc::ensures(true)]
fn while_false_inv_assert() {
    let mut i: u64 = 0;
    while i < 3u64 { trust_vc::invariant!(i == 100u64); trust_vc::assert!(i == 100u64); i = i + 1u64; }
}
// FALSE invariant (>=5, false at entry) → false postcondition.
#[trust_vc::ensures(result >= 5u64)]
fn while_false_inv_ge() -> u64 {
    let mut i: u64 = 0;
    while i < 3u64 { trust_vc::invariant!(i >= 5u64); i = i + 1u64; }
    i
}
// TRUE invariant, real result 3 — must still verify.
#[trust_vc::ensures(result == 3u64)]
fn while_true_inv() -> u64 {
    let mut i: u64 = 0;
    while i < 3u64 { trust_vc::invariant!(i <= 3u64); i = i + 1u64; }
    i
}
// TRUE invariant USED post-loop (invariant ∧ ¬guard ⟹ i == 3 ⟹ result <= 3).
#[trust_vc::ensures(result <= 3u64)]
fn while_inv_used_postloop() -> u64 {
    let mut i: u64 = 0;
    while i < 3u64 { trust_vc::invariant!(i <= 3u64); i = i + 1u64; }
    i
}
"#;

#[test]
fn false_loop_invariant_is_refuted() {
    for f in [
        "while_false_inv_postcond",
        "while_false_inv_assert",
        "while_false_inv_ge",
    ] {
        assert!(
            !verified(&verify(f, f, SRC)),
            "CARDINAL: `{f}`: a FALSE loop invariant on a let-local counter must NOT be assumed \
             — its establishment must fail (a false postcondition/assert must be refuted); got {:?}",
            verify(f, f, SRC)
        );
    }
}

#[test]
fn true_loop_invariant_still_verifies() {
    for f in ["while_true_inv", "while_inv_used_postloop"] {
        assert!(
            verified(&verify(f, f, SRC)),
            "`{f}`: a genuine invariant that holds at entry (and its post-loop use) must still \
             verify — the base-check fix is fail-closed, not over-rejecting; got {:?}",
            verify(f, f, SRC)
        );
    }
}
