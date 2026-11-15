// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Adversarial soundness regression for the return-flow classifier relaxation
//! (`vc_extraction/return_extract.rs`): the "multiple top-level returns" branch
//! was merged from `> 1 → Ambiguous` into the `>= 1 → Single(first)` path.
//!
//! WHY THIS IS SOUND AND NON-TRIVIAL:
//! * A statement-level `return` unconditionally diverges, so the FIRST top-level
//!   `return` DOMINATES the block: it is the sole reachable return value and every
//!   later statement (further top-level `return`s included) is dead code. This is
//!   PRECISE, not an over-approximation.
//! * The relaxation lifts ONLY the multiple-top-level-returns CONSERVATISM guard.
//!   The soundness guard — a reachable *nested* return that could run before the
//!   first top-level return — is untouched (`!nested_returns.values.is_empty()` at
//!   return_extract.rs line 86, plus the NestedReturnScan `unsupported` guards).
//!
//! CRUX (first-DOMINATES, not merely "some" return): with `return A; return B;`
//! the result pins to A. A postcondition on A VERIFIES; the SAME postcondition on
//! B (dead code) must COUNTEREXAMPLE. Reversing the order flips which literal is
//! live, so the discriminator is ORDER-SENSITIVE. A `Verified` on either B-pinned
//! probe would witness that the merge inspected the wrong (or "some") return =
//! UNSOUND.
//!
//! GUARD-INTACT: a body with a reachable nested return before the top-level
//! returns must NOT verify a wrong result — it stays Ambiguous / fail-closed.
//!
//! CACHE DISCIPLINE (mandatory): every verdict is recomputed cache-off
//! (`TRUST_VC_DISABLE_VC_CACHE=1`) so a stale `Verified` can never mask a
//! false-verify. `assert_not_verified` treats an extraction `Err` and any solver
//! non-`Verified` (incl. `Unknown`) as a sound non-verify; acceptance probes
//! require exactly `Verified` and dead-value probes require exactly
//! `Counterexample`.

use trust_vc_core::{verify_function_from_file, VerifyResult};

fn repro_path() -> String {
    format!(
        "{}/tests/data/first_return_dominates_soundness_repro.rs",
        env!("CARGO_MANIFEST_DIR")
    )
}

fn verify(func: &str) -> Result<VerifyResult, trust_vc_core::TrustVcError> {
    // SOUNDNESS-CRITICAL: recompute every verdict cache-off. A single stale
    // `Verified` would otherwise be served forever and mask a real false-verify.
    trust_vc_core::env::with_serialized_env_vars(&[("TRUST_VC_DISABLE_VC_CACHE", "1")], || {
        verify_function_from_file(&repro_path(), func)
    })
}

fn verdict(func: &str) -> VerifyResult {
    verify(func).unwrap_or_else(|e| panic!("extract+verify `{func}` failed: {e:?}"))
}

fn assert_verified(func: &str) {
    let v = verdict(func);
    assert!(
        matches!(v, VerifyResult::Verified),
        "`{func}` should VERIFY (postcondition on the FIRST, dominating return); got {v:?}"
    );
}

/// Assert an exact `Counterexample`. Stronger than "not verified": it witnesses
/// that the return value is MODELED (pinned to the first return) yet the probe on
/// the dead second value is falsifiable — not that extraction fell over.
fn assert_counterexample(func: &str) {
    let v = verdict(func);
    assert!(
        matches!(v, VerifyResult::Counterexample { .. }),
        "`{func}` should COUNTEREXAMPLE (probe pins the DEAD return value); got {v:?}"
    );
}

fn assert_not_verified(func: &str) {
    // An extraction Err (fail-closed / Ambiguous lowering) or any solver
    // non-Verified verdict (incl. Unknown) is a sound non-verify.
    if let Ok(VerifyResult::Verified) = verify(func) {
        panic!("RETURN-FLOW FALSE-VERIFY: `{func}` must not verify")
    }
}

#[test]
fn t1_first_value_pinned_verified() {
    // `return 11; return 13;` with ensures(result == 11): the first return
    // dominates, so this VERIFIES.
    assert_verified("first_value_pinned_verified");
}

#[test]
fn t2_second_value_is_dead_counterexample() {
    // THE CRUX: `return 11; return 13;` with ensures(result == 13). 13 is dead;
    // result pins to the FIRST return (11), not "some" return. MUST COUNTEREXAMPLE
    // — a `Verified` here is the cardinal false-verify the merge could introduce.
    assert_counterexample("second_value_is_dead_counterexample");
}

#[test]
fn t3_reordered_first_value_pinned_verified() {
    // Order-sensitive: `return 13; return 11;` with ensures(result == 13). The
    // first return is now 13, so this VERIFIES.
    assert_verified("reordered_first_value_pinned_verified");
}

#[test]
fn t4_reordered_second_value_is_dead_counterexample() {
    // Order-sensitive companion: `return 13; return 11;` with ensures(result == 11).
    // 11 is now the dead second return. MUST COUNTEREXAMPLE.
    assert_counterexample("reordered_second_value_is_dead_counterexample");
}

#[test]
fn t5_guard_reachable_nested_return_before_top_level_fail_closed() {
    // GUARD-INTACT (the load-bearing line-86 `nested_returns.values` guard): a
    // reachable nested `return 1u8` precedes the top-level returns, so
    // classification stays Ambiguous. result could be 1u8, so `result == 11u8` is
    // FALSE and MUST NOT VERIFY.
    assert_not_verified("guard_reachable_nested_return_before_top_level_fail_closed");
}

#[test]
fn t6_guard_nested_return_in_local_init_fail_closed() {
    // GUARD-INTACT (local-initializer shape): a nested return in a local
    // initializer before the top-level returns trips the "local initializer
    // explicit return path" guard and stays fail-closed. MUST NOT VERIFY.
    assert_not_verified("guard_nested_return_in_local_init_fail_closed");
}
