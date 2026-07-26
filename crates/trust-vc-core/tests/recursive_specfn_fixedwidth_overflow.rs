// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Soundness regression battery for the P1-E "shifts" cluster, recursive-u8
//! sub-case. Fixed-width arithmetic inside a recursive spec-fn body must wrap in
//! two's complement, consistent with the symbolic encoder. A by(compute)
//! refutation/upgrade must therefore agree with the wrapping value: a FALSE goal
//! over an overflowing recursive body must NEVER verify, while its TRUE
//! companion (and a non-overflowing instance) must still verify.
//!
//! See `crates/trust-vc-core/src/encoder/verification/compute.rs`
//! (`wrap_compute_int_to_type`, the `Arith` arm of `eval_expr`).

use trust_vc_core::{verify_function_from_file, VerifyResult};

fn path() -> String {
    format!(
        "{}/tests/data/recursive_specfn_fixedwidth_overflow.rs",
        env!("CARGO_MANIFEST_DIR")
    )
}

fn verdict(func: &str) -> VerifyResult {
    verify_function_from_file(&path(), func)
        .unwrap_or_else(|err| panic!("extract/verify {func} failed: {err:?}"))
}

/// FALSE goals over the overflowing fixed-width body. A `Verified` here is the
/// catastrophic false-Verified this fix closes (compute must wrap, not compute
/// `x + 1 > x` unbounded).
#[test]
fn false_recursive_overflow_goals_never_verify() {
    for func in [
        "h0_255_true_FALSE",
        "h0_255_both_FALSE",
        "h0_100_false_FALSE",
        "nr_255_true_FALSE",
    ] {
        let result = verdict(func);
        assert!(
            !matches!(result, VerifyResult::Verified),
            "UNSOUND: {func} verified a FALSE recursive-spec-fn goal whose body \
             overflows a fixed-width type (compute computed it unbounded). \
             Verdict: {result:?}"
        );
    }
}

/// TRUE companions must still verify — wrapping must keep the genuinely-true
/// facts provable (no over-rejection).
#[test]
fn true_recursive_overflow_goals_still_verify() {
    for func in ["h0_255_false_TRUE", "h0_100_true_TRUE", "nr_255_false_TRUE"] {
        let result = verdict(func);
        assert!(
            matches!(result, VerifyResult::Verified),
            "OVER-REJECTION: {func} is a genuinely-true fact (under the wrapping \
             semantics the symbolic encoder uses) but did not verify. \
             Verdict: {result:?}"
        );
    }
}
