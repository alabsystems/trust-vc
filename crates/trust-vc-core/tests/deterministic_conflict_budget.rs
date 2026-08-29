// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//
//! Acceptance pins for the DETERMINISTIC solver work budget
//! (`solver_budget::ConflictBudget`, threaded `#[verifier::rlimit(N)]` →
//! `vc_extraction` → `with_limits` → ay `:rlimit`).
//!
//! WHY THIS EXISTS. A wall-clock deadline lets machine load decide verdicts:
//! measured in ay, one query with byte-identical search counters returned
//! `unsat` at 1386ms and `unknown` at 1466ms against a 1450ms deadline. The
//! conflict budget is the machine-independent replacement. These tests pin
//! the four properties that make it trustworthy:
//!
//! 1. THE BUDGET BINDS — a tiny budget flips a normally-verifying obligation
//!    to `Unknown`, and the reason NAMES the budget (`resourceout — …
//!    #[verifier::rlimit]`), distinguishable from `timeout`.
//! 2. DETERMINISM — the tiny-budget run stops at the same point with the
//!    same verdict + reason on every repeat.
//! 3. FAIL-CLOSED — budget exhaustion is never `Verified`.
//! 4. LIAR PINS — a false obligation under a huge (or declined) budget still
//!    REFUTES: budget buys work, never verdicts.
//!
//! Cache is disabled for every solve here: the VC cache keys on the budget,
//! but a determinism test that hits the cache would measure the cache, not
//! the solver.

use trust_vc_core::{verify_function_from_file, VerifyResult};

fn fx() -> String {
    format!(
        "{}/tests/data/deterministic_conflict_budget.rs",
        env!("CARGO_MANIFEST_DIR")
    )
}

fn verify_cache_off(function: &str) -> trust_vc_core::TrustVcResult<VerifyResult> {
    trust_vc_core::env::with_serialized_env_vars(&[("TRUST_VC_DISABLE_VC_CACHE", "1")], || {
        verify_function_from_file(&fx(), function)
    })
}

/// The reason fragment `format_unknown_reason` renders for
/// `UnknownReason::ResourceLimit`. Pinned as a substring so the message can
/// grow context without breaking the pin, but can never silently collapse
/// back into the undifferentiated `resourceout`/`timeout` blur.
const BUDGET_REASON: &str = "deterministic conflict budget exhausted (#[verifier::rlimit])";

#[test]
fn control_verifies_under_the_default_budget() {
    let v = verify_cache_off("parity_default_budget");
    eprintln!("[BUDGET-CTRL] parity_default_budget => {v:?}");
    assert!(
        matches!(v, Ok(VerifyResult::Verified)),
        "the parity control must verify under the default budget, got {v:?}"
    );
}

#[test]
fn tiny_budget_binds_names_itself_and_fails_closed() {
    let v = verify_cache_off("parity_one_conflict").expect("verification should not error");
    eprintln!("[BUDGET-BIND] parity_one_conflict => {v:?}");
    // FAIL-CLOSED is the cardinal half: exhaustion must never verify.
    assert!(
        !matches!(v, VerifyResult::Verified),
        "budget exhaustion must NEVER yield Verified"
    );
    match &v {
        VerifyResult::Unknown { reason, .. } => {
            assert!(
                reason.contains(BUDGET_REASON),
                "the unknown reason must NAME the deterministic budget \
                 (distinguishable from `timeout`), got: {reason}"
            );
            assert!(
                !reason.contains("timeout"),
                "budget exhaustion must not read as a wall-clock timeout: {reason}"
            );
        }
        other => panic!("expected Unknown(resourceout), got {other:?}"),
    }
}

#[test]
fn tiny_budget_outcome_is_deterministic_across_five_repeats() {
    let render = |v: &VerifyResult| format!("{v:?}");
    let first = render(&verify_cache_off("parity_one_conflict").expect("run 1 should not error"));
    for run in 2..=5 {
        let this = render(
            &verify_cache_off("parity_one_conflict")
                .unwrap_or_else(|e| panic!("run {run} should not error: {e:?}")),
        );
        assert_eq!(
            this, first,
            "run {run} diverged from run 1 — the budget stop must be \
             machine-independent and repeat-identical"
        );
    }
}

#[test]
fn huge_budget_changes_nothing() {
    let v = verify_cache_off("parity_huge_budget");
    eprintln!("[BUDGET-HUGE] parity_huge_budget => {v:?}");
    assert!(
        matches!(v, Ok(VerifyResult::Verified)),
        "a 40M-conflict budget must verify exactly like the default, got {v:?}"
    );
}

#[test]
fn liar_under_huge_bounded_budget_still_refutes() {
    let v = verify_cache_off("liar_under_huge_budget");
    eprintln!("[BUDGET-LIAR] liar_under_huge_budget => {v:?}");
    assert!(
        matches!(v, Ok(VerifyResult::Counterexample { .. })),
        "a false ensures under rlimit(1000) must REFUTE, got {v:?}"
    );
}

#[test]
fn liar_under_infinity_still_refutes() {
    let v = verify_cache_off("liar_under_infinity");
    eprintln!("[BUDGET-LIAR-INF] liar_under_infinity => {v:?}");
    assert!(
        matches!(v, Ok(VerifyResult::Counterexample { .. })),
        "a false ensures under rlimit(infinity) must REFUTE, got {v:?}"
    );
}
