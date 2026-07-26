// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Adversarial soundness regression for match-guard support: each of the three
//! false-verify traps (guarded irrefutable arm becoming the unconditional default;
//! a guarded arm wrongly treated as exhaustive; constant-folding a guarded arm whose
//! guard is false) must yield a counterexample or fail-closed Error — never Verified.
//! See `match_encode.rs`, `match_datatype.rs`, `compute.rs`, `const_eval.rs`.

use trust_vc_core::{verify_function_from_file, VerifyResult};

fn repro_path() -> String {
    format!(
        "{}/tests/data/match_guard_soundness_repro.rs",
        env!("CARGO_MANIFEST_DIR")
    )
}

fn verdict(func: &str) -> VerifyResult {
    verify_function_from_file(&repro_path(), func)
        .unwrap_or_else(|e| panic!("extract+verify `{func}` failed: {e:?}"))
}

fn assert_not_verified(func: &str) {
    let v = verdict(func);
    assert!(
        !matches!(v, VerifyResult::Verified),
        "MATCH-GUARD FALSE-VERIFY: `{func}` must not verify; got {v:?}"
    );
}

#[test]
fn trap1_guarded_irrefutable_arm_is_conditional() {
    // Guard false (x can be <= 100) ⇒ default 999 ⇒ result == 0 is refutable.
    assert_not_verified("trap1_guarded_irrefutable_arm");
}

#[test]
fn trap1b_guarded_wildcard_arm_is_conditional() {
    assert_not_verified("trap1b_guarded_wildcard_arm");
}

#[test]
fn trap2_guarded_arm_is_not_exhaustive() {
    // TrapE::B ∧ ¬(n > 1000) has no arm ⇒ non-exhaustive ⇒ must fail closed.
    let v = verdict("trap2_guarded_non_exhaustive");
    assert!(
        matches!(v, VerifyResult::Error { .. }) || !matches!(v, VerifyResult::Verified),
        "a guarded arm must not make the match exhaustive; got {v:?}"
    );
    assert!(
        !matches!(v, VerifyResult::Verified),
        "trap2 must never verify (non-exhaustive); got {v:?}"
    );
}

#[test]
fn trap3_const_fold_does_not_pick_guarded_false_arm() {
    assert_not_verified("trap3_const_fold_wrong_arm");
}

#[test]
fn positive_guard_selects_correct_arm_verifies() {
    // Constant arm bodies so the check isolates guard-based arm selection (100 < 10 is
    // false ⇒ the second Some arm ⇒ result 7). Arithmetic arm bodies over a pattern
    // binding hit a SEPARATE, pre-existing "unresolved binding in overflow check"
    // limitation in value-position matches, orthogonal to guards.
    let v = verdict("positive_guard_constant_bodies");
    assert!(
        matches!(v, VerifyResult::Verified),
        "a guard that selects the correct arm must verify (result == 7); got {v:?}"
    );
}
