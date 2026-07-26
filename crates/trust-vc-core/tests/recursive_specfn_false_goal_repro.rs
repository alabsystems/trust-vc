// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Robustness regression (#54): verifying a FALSE goal against a CORRECT
//! recursive spec fn must return a clean, definitive `VerifyResult` — never
//! SIGBUS / stack overflow — while the matching TRUE goal still verifies.
//!
//! The original defect: the demand-inline retry (#2655) promoted a recursive
//! spec function to an inline body and `substitute_inline_calls`
//! (`encoder/eval/substitution_inline.rs`) recursed unbounded, inlining the
//! self/mutual call until the thread stack guard page faulted (SIGBUS). The fix:
//! (1) `build_body_catalog` excludes self-recursive bodies from demand-inline
//! candidates, and (2) `substitute_inline_calls` caps inline-expansion depth as
//! a hard backstop (covers mutual recursion too — see `ping`/`pong`). The
//! depth backstop itself is unit-tested in
//! `crates/trust-vc-core/src/encoder/eval/substitution_inline.rs`.

use trust_vc_core::{verify_function_from_file, VerifyResult};

fn repro_path() -> String {
    format!(
        "{}/tests/data/recursive_specfn_false_goal_repro.rs",
        env!("CARGO_MANIFEST_DIR")
    )
}

fn verdict(func: &str) -> VerifyResult {
    verify_function_from_file(&repro_path(), func)
        .unwrap_or_else(|err| panic!("extract/verify {func} must not error: {err:?}"))
}

/// (i) NO CRASH + (iii) NO false `Verified`: every concretely-false goal about a
/// correct recursive spec fn must return a clean result that is NOT `Verified`
/// (Counterexample preferred, Unknown tolerated). Reaching this assertion at all
/// proves there was no SIGBUS/stack overflow. Covers the exact reported shape
/// `good(0) == 1` plus the `good(1) == 5` / `good(2) == 1` variants, a `nat`
/// mirror of the canonical shape, and a mutually-recursive (`ping`/`pong`)
/// case that drives the inline-expansion depth backstop end to end.
#[test]
fn false_goals_never_crash_and_never_verify() {
    for func in [
        "false_good0_eq1",  // good(0) == 1   (good(0) == 0)
        "false_good1_eq5",  // good(1) == 5   (good(1) == 1)
        "false_good2_eq1",  // good(2) == 1   (good(2) == 2)
        "false_goodn0_eq1", // goodn(0) == 1  (nat mirror of canonical shape)
        "false_ping0_eq1",  // ping(0) == 1   (mutual recursion -> depth backstop)
    ] {
        let result = verdict(func);
        assert!(
            !matches!(result, VerifyResult::Verified),
            "{func}: a concretely-false goal must NOT verify; got {result:?}"
        );
    }
}

/// Preferred outcome: the false goals are *decided* (Counterexample), not merely
/// `Unknown`. Pins the fix to the strong, non-masking result for the
/// self-recursive (`good`) and mutually-recursive (`ping`/`pong`) shapes.
#[test]
fn false_goals_are_counterexamples() {
    for func in [
        "false_good0_eq1",
        "false_good1_eq5",
        "false_good2_eq1",
        "false_ping0_eq1",
    ] {
        let result = verdict(func);
        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "{func}: a false goal about a faithful recursive axiom should be a \
             Counterexample, got {result:?}"
        );
    }
}

/// (ii) Valid recursion still verifies — no over-rejection / no masking. The
/// matching TRUE goals must all `Verified`.
#[test]
fn true_goals_still_verify() {
    for func in [
        "true_good0_eq0",
        "true_good1_eq1",
        "true_good2_eq2",
        "true_goodn0_eq0",
        "true_ping0_eq0",
    ] {
        let result = verdict(func);
        assert!(
            matches!(result, VerifyResult::Verified),
            "{func}: a true goal about a correctly-decreasing recursive spec fn \
             must verify, got {result:?}"
        );
    }
}
